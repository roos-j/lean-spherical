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
open Auto.Spherical.SphericalMaximal
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

/-! ## The sphere slice identity

The representation (4.1) rests on the distribution of the height `⟪ω, e⟫` of a
point of the unit sphere in a fixed unit direction `e`.  For the final
coordinate axis this is the repository's height-density computation
`integral_comp_last_unitSurfaceMeasure_succ`; an arbitrary unit direction is
reached by the reflection which exchanges the two unit vectors. -/

/-- The final-coordinate unit vector of `Euclidean (d + 1)`. -/
def lastAxis (d : ℕ) : Euclidean (d + 1) :=
  MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ) (fun i => if i = Fin.last d then 1 else 0)

/-- The one-dimensional slice measure carrying the height distribution of the
unit sphere of `Euclidean (d + 1)`: the density is `(1 - t²)^{(d-2)/2}` on
`(-1,1)`. -/
def sliceMeasure (d : ℕ) : Measure ℝ :=
  (volume.withDensity
    (fun t : ℝ => ENNReal.ofReal (Real.sqrt (1 - t ^ 2)) ^ (d - 2))).restrict
      (Ioo (-1 : ℝ) 1)

/-- **The sphere slice identity.**  For a unit direction `e`, integrating a
continuous function of the height `⟪ω, e⟫` over the unit sphere is the
one-dimensional integral against the slice measure, scaled by the surface mass
of the equatorial sphere. -/
theorem integral_comp_inner_unitSurfaceMeasure_succ {d : ℕ} (hd : 2 ≤ d)
    (e : Euclidean (d + 1)) (he : ‖e‖ = 1) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ ω : Metric.sphere (0 : Euclidean (d + 1)) 1,
        F (inner ℝ (ω : Euclidean (d + 1)) e) ∂unitSurfaceMeasure (d + 1)) =
      (surfaceMass d : ℂ) * ∫ t, F t ∂sliceMeasure d := by
  -- the reflection exchanging the final axis with `e`
  set a : Euclidean (d + 1) := lastAxis d with ha
  have hna : ‖a‖ = 1 := by
    rw [ha, lastAxis]
    exact norm_euclideanSucc_last d
  set u : Euclidean (d + 1) ≃ₗᵢ[ℝ] Euclidean (d + 1) :=
    Submodule.reflection (ℝ ∙ (a - e))ᗮ with hu
  have hua : u a = e := Submodule.reflection_sub (by rw [hna, he])
  set uSphere : Metric.sphere (0 : Euclidean (d + 1)) 1 ≃ₜ
      Metric.sphere (0 : Euclidean (d + 1)) 1 :=
    u.toHomeomorph.subtype (fun x => by
      simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
      rw [u.norm_map]) with huSphere
  have hmeasure : Measure.map uSphere (unitSurfaceMeasure (d + 1)) =
      unitSurfaceMeasure (d + 1) := by
    simpa only [huSphere] using map_unitSurfaceMeasure_linearIsometry (d + 1) u
  have hpres : MeasurePreserving uSphere (unitSurfaceMeasure (d + 1))
      (unitSurfaceMeasure (d + 1)) := ⟨uSphere.continuous.measurable, hmeasure⟩
  have hcomp := hpres.integral_comp uSphere.measurableEmbedding
    (fun ω : Metric.sphere (0 : Euclidean (d + 1)) 1 =>
      F (inner ℝ (ω : Euclidean (d + 1)) e))
  calc
    (∫ ω : Metric.sphere (0 : Euclidean (d + 1)) 1,
        F (inner ℝ (ω : Euclidean (d + 1)) e) ∂unitSurfaceMeasure (d + 1)) =
        ∫ ω : Metric.sphere (0 : Euclidean (d + 1)) 1,
          F (inner ℝ ((uSphere ω : Metric.sphere (0 : Euclidean (d + 1)) 1) :
            Euclidean (d + 1)) e) ∂unitSurfaceMeasure (d + 1) := hcomp.symm
    _ = ∫ ω : Metric.sphere (0 : Euclidean (d + 1)) 1,
          F ((ω : Euclidean (d + 1)) (Fin.last d))
            ∂unitSurfaceMeasure (d + 1) := by
        apply integral_congr_ae
        filter_upwards with ω
        have hval : ((uSphere ω : Metric.sphere (0 : Euclidean (d + 1)) 1) :
            Euclidean (d + 1)) = u (ω : Euclidean (d + 1)) := rfl
        rw [hval, ← hua, u.inner_map_map]
        rw [ha, lastAxis, inner_euclideanSucc_last]
    _ = (surfaceMass d : ℂ) * ∫ t, F t ∂sliceMeasure d :=
        integral_comp_last_unitSurfaceMeasure_succ hd F hF

/-- The spherical average of a radial function is a one-dimensional integral
of its profile against the slice measure.  This is the geometric half of the
representation (4.1). -/
theorem sphericalAverage_comp_norm_succ {d : ℕ} (hd : 2 ≤ d)
    (f₀ : ℝ → ℂ) (hf₀ : Continuous f₀)
    {x : Euclidean (d + 1)} (hx : x ≠ 0) (t : ℝ) :
    _root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x =
      (((surfaceMass (d + 1))⁻¹ * surfaceMass d : ℝ) : ℂ) *
        ∫ v, f₀ (Real.sqrt (‖x‖ ^ 2 + t ^ 2 + 2 * ‖x‖ * t * v)) ∂sliceMeasure d := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set e : Euclidean (d + 1) := ‖x‖⁻¹ • x with he
  have hne : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    field_simp
  set F : ℝ → ℂ := fun v => f₀ (Real.sqrt (‖x‖ ^ 2 + t ^ 2 + 2 * ‖x‖ * t * v)) with hF
  have hFcont : Continuous F := by
    rw [hF]
    exact hf₀.comp (Real.continuous_sqrt.comp (by fun_prop))
  have hpoint : ∀ ω : Metric.sphere (0 : Euclidean (d + 1)) 1,
      f₀ ‖x + t • (ω : Euclidean (d + 1))‖ =
        F (inner ℝ (ω : Euclidean (d + 1)) e) := by
    intro ω
    have hω : ‖(ω : Euclidean (d + 1))‖ = 1 := by
      simpa using ω.2
    have hinner : inner ℝ (ω : Euclidean (d + 1)) e =
        ‖x‖⁻¹ * inner ℝ x (ω : Euclidean (d + 1)) := by
      rw [he, real_inner_smul_right, real_inner_comm]
    have hsq : ‖x + t • (ω : Euclidean (d + 1))‖ ^ 2 =
        ‖x‖ ^ 2 + t ^ 2 + 2 * ‖x‖ * t * inner ℝ (ω : Euclidean (d + 1)) e := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hω,
        mul_one, hinner]
      have habs : |t| ^ 2 = t ^ 2 := sq_abs t
      rw [habs]
      field_simp
      ring
    rw [hF]
    congr 1
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  calc
    _root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x =
        (((surfaceMass (d + 1))⁻¹ : ℝ) : ℂ) *
          ∫ ω : Metric.sphere (0 : Euclidean (d + 1)) 1,
            f₀ ‖x + t • (ω : Euclidean (d + 1))‖ ∂unitSurfaceMeasure (d + 1) := by
      rw [_root_.Auto.Spherical.PowerWeights.sphericalAverage_eq_normalizedSphericalAverage,
        normalizedSphericalAverage, SurfaceMeasureDecay.sphericalAverage]
      push_cast
      ring
    _ = (((surfaceMass (d + 1))⁻¹ : ℝ) : ℂ) *
          ∫ ω : Metric.sphere (0 : Euclidean (d + 1)) 1,
            F (inner ℝ (ω : Euclidean (d + 1)) e) ∂unitSurfaceMeasure (d + 1) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      exact hpoint ω
    _ = (((surfaceMass (d + 1))⁻¹ : ℝ) : ℂ) *
          ((surfaceMass d : ℂ) * ∫ v, F v ∂sliceMeasure d) := by
      rw [integral_comp_inner_unitSurfaceMeasure_succ hd e hne F hFcont]
    _ = (((surfaceMass (d + 1))⁻¹ * surfaceMass d : ℝ) : ℂ) *
          ∫ v, F v ∂sliceMeasure d := by
      push_cast
      ring

/-- The slice measure written as an ordinary interval integral against its
density. -/
theorem integral_sliceMeasure_eq_intervalIntegral (d : ℕ) (F : ℝ → ℂ)
    (hF : Continuous F) :
    (∫ v, F v ∂sliceMeasure d) =
      ∫ v in (-1 : ℝ)..1, ((Real.sqrt (1 - v ^ 2) ^ (d - 2) : ℝ)) • F v := by
  have hmeas : Measurable fun v : ℝ =>
      ENNReal.ofReal (Real.sqrt (1 - v ^ 2)) ^ (d - 2) := by
    refine Measurable.pow_const ?_ _
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_sqrt.comp (by fun_prop)).measurable
  have htop : ∀ᵐ v : ℝ ∂(volume.restrict (Ioo (-1 : ℝ) 1)),
      ENNReal.ofReal (Real.sqrt (1 - v ^ 2)) ^ (d - 2) < ∞ := by
    refine Filter.Eventually.of_forall fun v => ?_
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  rw [sliceMeasure, restrict_withDensity measurableSet_Ioo,
    integral_withDensity_eq_integral_toReal_smul hmeas htop,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
  congr 1
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-! ## The kernel representation (4.1)–(4.2) -/

/-- The kernel `K_t(r,s)` of BRS (4.2), in ambient dimension `d`. -/
def brsKernel (d : ℕ) (t r s : ℝ) : ℝ :=
  (Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) /
      ((r + t) ^ 2 - (r - t) ^ 2)) ^ (d - 3) *
    (s / ((r + t) ^ 2 - (r - t) ^ 2))

/-- The denominator of (4.2) is `4rt`. -/
theorem brsKernel_eq_of_pos (d : ℕ) (t r s : ℝ) :
    brsKernel d t r s =
      (Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) /
          (4 * r * t)) ^ (d - 3) * (s / (4 * r * t)) := by
  unfold brsKernel
  rw [show (r + t) ^ 2 - (r - t) ^ 2 = 4 * r * t by ring]

set_option maxHeartbeats 1000000 in
/-- The change of variables `v = (s² − r² − t²)/(2rt)` turns the slice integral
into the kernel integral of BRS (4.1). -/
theorem intervalIntegral_slice_eq_kernel {d : ℕ} {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (f₀ : ℝ → ℂ) (hf₀ : Continuous f₀) :
    (∫ v in (-1 : ℝ)..1,
        ((Real.sqrt (1 - v ^ 2) ^ (d - 2) : ℝ)) •
          f₀ (Real.sqrt (r ^ 2 + t ^ 2 + 2 * r * t * v))) =
      ∫ s in |r - t|..(r + t),
        (((4 : ℝ) * 2 ^ (d - 2) * brsKernel (d + 1) t r s : ℝ)) • f₀ s := by
  have hrt : (0 : ℝ) < r * t := mul_pos hr ht
  have hab : |r - t| ≤ r + t := by
    rw [abs_le]
    constructor <;> linarith
  set φ : ℝ → ℝ := fun s => (s ^ 2 - r ^ 2 - t ^ 2) / (2 * (r * t)) with hφ
  set g : ℝ → ℂ := fun v =>
    ((Real.sqrt (1 - v ^ 2) ^ (d - 2) : ℝ)) •
      f₀ (Real.sqrt (r ^ 2 + t ^ 2 + 2 * r * t * v)) with hg
  have hgcont : Continuous g := by
    rw [hg]
    exact (Continuous.pow (Real.continuous_sqrt.comp (by fun_prop)) _).smul
      (hf₀.comp (Real.continuous_sqrt.comp (by fun_prop)))
  have hderiv : ∀ s ∈ uIcc (|r - t|) (r + t), HasDerivAt φ (s / (r * t)) s := by
    intro s _
    have h := ((hasDerivAt_pow 2 s).sub_const (r ^ 2)).sub_const (t ^ 2)
    have h2 := h.div_const (2 * (r * t))
    refine h2.congr_deriv ?_
    field_simp
    ring
  have hderivCont : ContinuousOn (fun s : ℝ => s / (r * t)) (uIcc (|r - t|) (r + t)) := by
    fun_prop
  have hsub := intervalIntegral.integral_deriv_smul_comp hderiv hderivCont hgcont
  have hleft : φ (|r - t|) = -1 := by
    show (|r - t| ^ 2 - r ^ 2 - t ^ 2) / (2 * (r * t)) = -1
    rw [sq_abs]
    field_simp
    ring
  have hright : φ (r + t) = 1 := by
    show ((r + t) ^ 2 - r ^ 2 - t ^ 2) / (2 * (r * t)) = 1
    field_simp
    ring
  rw [hleft, hright] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr ?_
  intro s hs
  rw [uIcc_of_le hab] at hs
  have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hs.1
  have hA : 0 ≤ (r + t) ^ 2 - s ^ 2 := by nlinarith [hs0, hs.2]
  have hB : 0 ≤ s ^ 2 - (r - t) ^ 2 := by
    have habs : |r - t| ^ 2 = (r - t) ^ 2 := sq_abs _
    nlinarith [hs.1, abs_nonneg (r - t), hs0]
  have hval : r ^ 2 + t ^ 2 + 2 * r * t * φ s = s ^ 2 := by
    show r ^ 2 + t ^ 2 + 2 * r * t * ((s ^ 2 - r ^ 2 - t ^ 2) / (2 * (r * t))) = s ^ 2
    field_simp
    ring
  have hsqrtval : Real.sqrt (r ^ 2 + t ^ 2 + 2 * r * t * φ s) = s := by
    rw [hval, Real.sqrt_sq hs0]
  have hone : 1 - φ s ^ 2 =
      ((r + t) ^ 2 - s ^ 2) * (s ^ 2 - (r - t) ^ 2) / (2 * (r * t)) ^ 2 := by
    show 1 - ((s ^ 2 - r ^ 2 - t ^ 2) / (2 * (r * t))) ^ 2 = _
    field_simp
    ring
  have hsqrtone : Real.sqrt (1 - φ s ^ 2) =
      Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) /
        (2 * (r * t)) := by
    rw [hone, show ((r + t) ^ 2 - s ^ 2) * (s ^ 2 - (r - t) ^ 2) / (2 * (r * t)) ^ 2
        = (Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) /
            (2 * (r * t))) ^ 2 by
      rw [div_pow]
      congr 1
      rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]]
    exact Real.sqrt_sq (by positivity)
  have hexp : d + 1 - 3 = d - 2 := by omega
  show (s / (r * t)) • g (φ s) = _
  have hgs : g (φ s) = ((Real.sqrt (1 - φ s ^ 2) ^ (d - 2) : ℝ)) • f₀ s := by
    simp only [hg, hsqrtval]
  rw [hgs, smul_smul]
  show (s / (r * t) * Real.sqrt (1 - φ s ^ 2) ^ (d - 2)) • f₀ s =
    ((4 : ℝ) * 2 ^ (d - 2) * brsKernel (d + 1) t r s) • f₀ s
  rw [brsKernel_eq_of_pos, hexp, hsqrtone]
  congr 1
  have h4 : (4 : ℝ) ^ (d - 2) = 2 ^ ((d - 2) * 2) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  rw [div_pow, div_pow, show (4 : ℝ) * r * t = 2 * (2 * (r * t)) by ring, mul_pow]
  field_simp
  ring_nf
  rw [h4]

set_option maxHeartbeats 800000 in
/-- **BRS (4.1)–(4.2).**  For a radial function with continuous profile `f₀`,
the spherical average of radius `t` at a nonzero point `x` is the kernel
integral of the profile over `[ |r - t|, r + t ]`, with `r = ‖x‖`. -/
theorem sphericalAverage_eq_kernel_integral {d : ℕ} (hd : 2 ≤ d)
    (f₀ : ℝ → ℂ) (hf₀ : Continuous f₀)
    {x : Euclidean (d + 1)} (hx : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    _root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x =
      (((surfaceMass (d + 1))⁻¹ * surfaceMass d * ((4 : ℝ) * 2 ^ (d - 2)) : ℝ) : ℂ) *
        ∫ s in |‖x‖ - t|..(‖x‖ + t),
          ((brsKernel (d + 1) t ‖x‖ s : ℝ)) • f₀ s := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hFcont : Continuous fun v : ℝ =>
      f₀ (Real.sqrt (‖x‖ ^ 2 + t ^ 2 + 2 * ‖x‖ * t * v)) :=
    hf₀.comp (Real.continuous_sqrt.comp (by fun_prop))
  have hpull :
      (∫ s in |‖x‖ - t|..(‖x‖ + t),
        (((4 : ℝ) * 2 ^ (d - 2) * brsKernel (d + 1) t ‖x‖ s : ℝ)) • f₀ s) =
      ((4 : ℝ) * 2 ^ (d - 2)) •
        ∫ s in |‖x‖ - t|..(‖x‖ + t), ((brsKernel (d + 1) t ‖x‖ s : ℝ)) • f₀ s := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr ?_
    intro s _
    show (((4 : ℝ) * 2 ^ (d - 2) * brsKernel (d + 1) t ‖x‖ s : ℝ)) • f₀ s =
      ((4 : ℝ) * 2 ^ (d - 2)) • (((brsKernel (d + 1) t ‖x‖ s : ℝ)) • f₀ s)
    rw [smul_smul]
  rw [sphericalAverage_comp_norm_succ hd f₀ hf₀ hx t,
    integral_sliceMeasure_eq_intervalIntegral d _ hFcont,
    intervalIntegral_slice_eq_kernel hr ht f₀ hf₀, hpull]
  rw [Complex.real_smul]
  push_cast
  ring

/-! ## The test function of Lemma 3.1

The necessity of `p ≤ q` is tested on a radial function supported in a union
of `2^{k-5}` annuli of thickness six at radius about `2^k`, separated by gaps
of length two.  A sphere of radius `t ∈ [1,2]` centred in the middle annulus
`I^k_n` stays inside the fattened annulus `I^{k,*}_n` and misses every other
one. -/

/-- The fattened annulus radii `I^{k,*}_n = [2^k + 8n + 1, 2^k + 8n + 7]`. -/
def annulusStar (k n : ℕ) : Set ℝ :=
  Icc ((2 : ℝ) ^ k + 8 * n + 1) ((2 : ℝ) ^ k + 8 * n + 7)

/-- The core annulus radii `I^k_n = [2^k + 8n + 3, 2^k + 8n + 5]`. -/
def annulusCore (k n : ℕ) : Set ℝ :=
  Icc ((2 : ℝ) ^ k + 8 * n + 3) ((2 : ℝ) ^ k + 8 * n + 5)

theorem annulusCore_subset_annulusStar (k n : ℕ) :
    annulusCore k n ⊆ annulusStar k n := by
  intro s hs
  rw [annulusCore, mem_Icc] at hs
  rw [annulusStar, mem_Icc]
  constructor <;> linarith [hs.1, hs.2]

/-- Distinct fattened annuli are disjoint: they have length six inside a
period of eight. -/
theorem annulusStar_disjoint {k m n : ℕ} (h : m ≠ n) :
    Disjoint (annulusStar k m) (annulusStar k n) := by
  rw [Set.disjoint_left]
  intro s hsm hsn
  rw [annulusStar, mem_Icc] at hsm hsn
  rcases Nat.lt_or_ge m n with hmn | hmn
  · have hcast : ((m : ℝ) + 1) ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hmn
    linarith [hsm.2, hsn.1]
  · have hnm : n < m := by omega
    have hcast : ((n : ℝ) + 1) ≤ (m : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hnm
    linarith [hsn.2, hsm.1]

/-- A radius within distance two of the core annulus lies in the fattened
annulus. -/
theorem mem_annulusStar_of_dist_le {k n : ℕ} {s u : ℝ}
    (hs : s ∈ annulusCore k n) (hu : |u - s| ≤ 2) : u ∈ annulusStar k n := by
  rw [annulusCore, mem_Icc] at hs
  rw [abs_le] at hu
  rw [annulusStar, mem_Icc]
  constructor <;> linarith [hs.1, hs.2, hu.1, hu.2]

/-- A radius within distance two of a different core annulus misses the
fattened annulus. -/
theorem notMem_annulusStar_of_dist_le {k m n : ℕ} (h : m ≠ n) {s u : ℝ}
    (hs : s ∈ annulusCore k m) (hu : |u - s| ≤ 2) : u ∉ annulusStar k n := by
  intro hun
  have hum : u ∈ annulusStar k m := mem_annulusStar_of_dist_le hs hu
  exact (Set.disjoint_left.mp (annulusStar_disjoint (k := k) h)) hum hun

/-- The radial profile of the test function of BRS Lemma 3.1, before the
normalizing constant. -/
def testProfile (k : ℕ) : ℝ → ℂ :=
  fun s => ∑ n ∈ Finset.Icc 1 (2 ^ (k - 5)),
    (annulusStar k n).indicator (fun _ => (1 : ℂ)) s

theorem measurable_testProfile (k : ℕ) : Measurable (testProfile k) := by
  unfold testProfile
  refine Finset.measurable_sum _ fun n _ => ?_
  exact measurable_const.indicator measurableSet_Icc

/-- On a fattened annulus of the family the profile equals one. -/
theorem testProfile_eq_one {k n : ℕ} (hn : n ∈ Finset.Icc 1 (2 ^ (k - 5)))
    {s : ℝ} (hs : s ∈ annulusStar k n) : testProfile k s = 1 := by
  rw [testProfile]
  rw [Finset.sum_eq_single n]
  · rw [Set.indicator_of_mem hs]
  · intro m hm hmn
    refine Set.indicator_of_notMem ?_ _
    exact Set.disjoint_right.mp (annulusStar_disjoint (k := k) hmn) hs
  · intro hcon
    exact absurd hn hcon

/-- The profile is nonnegative and bounded by one. -/
theorem testProfile_norm_le_one (k : ℕ) (s : ℝ) : ‖testProfile k s‖ ≤ 1 := by
  by_cases hs : ∃ n ∈ Finset.Icc 1 (2 ^ (k - 5)), s ∈ annulusStar k n
  · obtain ⟨n, hn, hsn⟩ := hs
    rw [testProfile_eq_one hn hsn]
    norm_num
  · have hzero : testProfile k s = 0 := by
      unfold testProfile
      refine Finset.sum_eq_zero fun n hn => ?_
      refine Set.indicator_of_notMem ?_ _
      intro hsn
      exact hs ⟨n, hn, hsn⟩
    rw [hzero]
    norm_num

/-- The normalized sphere measure of `Definitions.lean` is a probability
measure. -/
theorem unitSphereMeasure_real_univ {d : ℕ} (hd : 0 < d) :
    (_root_.Spherical.unitSphereMeasure d).real univ = 1 := by
  have hpos : 0 < unitSurfaceMeasure d univ := unitSurfaceMeasure_univ_pos hd
  have htop : unitSurfaceMeasure d univ ≠ ⊤ := measure_ne_top _ _
  rw [_root_.Spherical.unitSphereMeasure, measureReal_def, Measure.smul_apply,
    smul_eq_mul]
  have hval : ((volume : Measure (Euclidean d)).toSphere univ) =
      unitSurfaceMeasure d univ := rfl
  rw [hval, ENNReal.toReal_mul, ENNReal.toReal_inv]
  exact inv_mul_cancel₀ (ENNReal.toReal_pos (ne_of_gt hpos) htop).ne'

/-- **The key averaging property of the test function.**  A sphere of radius
`t ∈ [1,2]` centred at radius in the core annulus `I^k_n` stays inside the
fattened annulus, where the profile is one, so the average is one. -/
theorem sphericalAverage_testProfile_eq_one {d k n : ℕ} (hd : 0 < d)
    (hn : n ∈ Finset.Icc 1 (2 ^ (k - 5))) {x : Euclidean d}
    (hx : ‖x‖ ∈ annulusCore k n) {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    _root_.Spherical.sphericalAverage t (fun y => testProfile k ‖y‖) x = 1 := by
  have hpoint : ∀ ω : Metric.sphere (0 : Euclidean d) 1,
      testProfile k ‖x + t • (ω : Euclidean d)‖ = 1 := by
    intro ω
    refine testProfile_eq_one hn (mem_annulusStar_of_dist_le hx ?_)
    have hω : ‖(ω : Euclidean d)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have h1 : |‖x + t • (ω : Euclidean d)‖ - ‖x‖| ≤ ‖t • (ω : Euclidean d)‖ := by
      simpa using abs_norm_sub_norm_le (x + t • (ω : Euclidean d)) x
    rw [norm_smul, Real.norm_eq_abs, hω, mul_one] at h1
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    calc |‖x + t • (ω : Euclidean d)‖ - ‖x‖| ≤ |t| := h1
      _ = t := abs_of_pos ht0
      _ ≤ 2 := ht.2
  rw [_root_.Spherical.sphericalAverage,
    integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const,
    unitSphereMeasure_real_univ hd, one_smul]

/-! ## Volumes of radial annuli -/

/-- The closed radial annulus `{x : ‖x‖ ∈ [a,b]}`. -/
def radialAnnulusIcc (d : ℕ) (a b : ℝ) : Set (Euclidean d) := {x | ‖x‖ ∈ Icc a b}

theorem radialAnnulusIcc_eq_diff (d : ℕ) (a b : ℝ) :
    radialAnnulusIcc d a b =
      Metric.closedBall (0 : Euclidean d) b \ Metric.ball (0 : Euclidean d) a := by
  ext x
  simp only [radialAnnulusIcc, mem_setOf_eq, mem_Icc, Set.mem_diff,
    Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, not_lt]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem measurableSet_radialAnnulusIcc (d : ℕ) (a b : ℝ) :
    MeasurableSet (radialAnnulusIcc d a b) := by
  rw [radialAnnulusIcc_eq_diff]
  exact measurableSet_closedBall.diff measurableSet_ball

/-- The volume of a radial annulus is the difference of the `d`-th powers of
its radii, times the volume of the unit ball. -/
theorem volume_radialAnnulusIcc {d : ℕ} (hd : 0 < d) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    volume (radialAnnulusIcc d a b) =
      ENNReal.ofReal (b ^ d - a ^ d) * volume (Metric.ball (0 : Euclidean d) 1) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hfr : Module.finrank ℝ (Euclidean d) = d := finrank_euclideanSpace_fin
  have hsub : Metric.ball (0 : Euclidean d) a ⊆
      Metric.closedBall (0 : Euclidean d) b := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hfin : volume (Metric.ball (0 : Euclidean d) a) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hclosed := Measure.addHaar_closedBall (volume : Measure (Euclidean d))
    (0 : Euclidean d) (le_trans ha hab)
  have hopen := Measure.addHaar_ball (volume : Measure (Euclidean d))
    (0 : Euclidean d) ha
  rw [hfr] at hclosed hopen
  have hkey : ENNReal.ofReal (b ^ d) * volume (Metric.ball (0 : Euclidean d) 1) -
      ENNReal.ofReal (a ^ d) * volume (Metric.ball (0 : Euclidean d) 1) =
      ENNReal.ofReal (b ^ d - a ^ d) * volume (Metric.ball (0 : Euclidean d) 1) := by
    rw [ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ a ^ d)]
    exact (ENNReal.sub_mul (fun _ _ =>
      ((measure_mono Metric.ball_subset_closedBall).trans_lt
        measure_closedBall_lt_top).ne)).symm
  rw [radialAnnulusIcc_eq_diff,
    measure_sdiff hsub measurableSet_ball.nullMeasurableSet hfin, hclosed, hopen,
    hkey]

/-- The radii intervals of the family are pairwise disjoint, hence so are the
annuli. -/
theorem radialAnnulus_annulusStar_disjoint (d : ℕ) {k m n : ℕ} (h : m ≠ n) :
    Disjoint (radialAnnulusIcc d ((2 : ℝ) ^ k + 8 * m + 1) ((2 : ℝ) ^ k + 8 * m + 7))
      (radialAnnulusIcc d ((2 : ℝ) ^ k + 8 * n + 1) ((2 : ℝ) ^ k + 8 * n + 7)) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  exact (Set.disjoint_left.mp (annulusStar_disjoint (k := k) h)) hxm hxn

/-- The union of the fattened annuli carrying the test function. -/
def testStarSet (d k : ℕ) : Set (Euclidean d) :=
  ⋃ n ∈ (Finset.Icc 1 (2 ^ (k - 5)) : Finset ℕ), {x : Euclidean d | ‖x‖ ∈ annulusStar k n}

/-- The union of the core annuli on which the maximal function is at least
one. -/
def testCoreSet (d k : ℕ) : Set (Euclidean d) :=
  ⋃ n ∈ (Finset.Icc 1 (2 ^ (k - 5)) : Finset ℕ), {x : Euclidean d | ‖x‖ ∈ annulusCore k n}

theorem measurableSet_testStarSet (d k : ℕ) : MeasurableSet (testStarSet d k) := by
  unfold testStarSet
  exact Finset.measurableSet_biUnion _ fun n _ => measurableSet_radialAnnulusIcc d _ _

theorem measurableSet_testCoreSet (d k : ℕ) : MeasurableSet (testCoreSet d k) := by
  unfold testCoreSet
  exact Finset.measurableSet_biUnion _ fun n _ => measurableSet_radialAnnulusIcc d _ _

/-- The radial lift of the test profile is the indicator of the union of the
fattened annuli. -/
theorem testProfile_lift_eq_indicator (d k : ℕ) :
    (fun x : Euclidean d => testProfile k ‖x‖) =
      (testStarSet d k).indicator (fun _ => (1 : ℂ)) := by
  funext x
  by_cases hx : ∃ n ∈ Finset.Icc 1 (2 ^ (k - 5)), ‖x‖ ∈ annulusStar k n
  · obtain ⟨n, hn, hxn⟩ := hx
    have hmem : x ∈ testStarSet d k := by
      unfold testStarSet
      exact Set.mem_biUnion hn hxn
    rw [testProfile_eq_one hn hxn, Set.indicator_of_mem hmem]
  · have hzero : testProfile k ‖x‖ = 0 := by
      unfold testProfile
      refine Finset.sum_eq_zero fun n hn => ?_
      refine Set.indicator_of_notMem ?_ _
      intro hxn
      exact hx ⟨n, hn, hxn⟩
    have hnot : x ∉ testStarSet d k := by
      unfold testStarSet
      intro hmem
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hmem
      exact hx hmem
    rw [hzero, Set.indicator_of_notMem hnot]

/-- The `L^p` norm of the test function is the `p`-th root of the volume of
the union of the fattened annuli. -/
theorem eLpNorm_testProfile_lift (d k : ℕ) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x : Euclidean d => testProfile k ‖x‖) (ENNReal.ofReal p) volume =
      volume (testStarSet d k) ^ (1 / p) := by
  rw [testProfile_lift_eq_indicator,
    eLpNorm_indicator_const (measurableSet_testStarSet d k)
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  simp

/-- On the union of the core annuli the maximal function is at least one, so
its `L^q` norm dominates the `q`-th root of that volume. -/
theorem le_eLpNorm_M_testProfile_lift {d k : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {q : ℝ} (hq : 0 < q) :
    volume (testCoreSet d k) ^ (1 / q) ≤
      eLpNorm (M E (fun x : Euclidean d => testProfile k ‖x‖))
        (ENNReal.ofReal q) volume := by
  obtain ⟨t, htE⟩ := hEne
  have htIcc : t ∈ Icc (1 : ℝ) 2 := hE htE
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one htIcc.1
  have hpoint : ∀ x : Euclidean d,
      ‖(testCoreSet d k).indicator (fun _ => (1 : ℂ)) x‖ₑ ≤
        ‖M E (fun y : Euclidean d => testProfile k ‖y‖) x‖ₑ := by
    intro x
    by_cases hx : x ∈ testCoreSet d k
    · have hx' : ∃ n ∈ (Finset.Icc 1 (2 ^ (k - 5)) : Finset ℕ),
          ‖x‖ ∈ annulusCore k n := by
        unfold testCoreSet at hx
        simpa only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] using hx
      obtain ⟨n, hn, hxn⟩ := hx'
      have havg : _root_.Spherical.sphericalAverage t
          (fun y : Euclidean d => testProfile k ‖y‖) x = 1 :=
        sphericalAverage_testProfile_eq_one hd hn hxn htIcc
      have hone : (1 : ENNReal) ≤ M E (fun y : Euclidean d => testProfile k ‖y‖) x := by
        unfold M _root_.Spherical.restrictedSphericalMaximal
        refine le_iSup_of_le t (le_iSup_of_le ⟨htE, htpos⟩ ?_)
        rw [havg]
        simp
      calc
        ‖(testCoreSet d k).indicator (fun _ => (1 : ℂ)) x‖ₑ = 1 := by
          rw [Set.indicator_of_mem hx]
          simp
        _ ≤ _ := hone
    · rw [Set.indicator_of_notMem hx]
      simp
  have heq : eLpNorm ((testCoreSet d k).indicator (fun _ => (1 : ℂ)))
      (ENNReal.ofReal q) volume = volume (testCoreSet d k) ^ (1 / q) := by
    rw [eLpNorm_indicator_const (measurableSet_testCoreSet d k)
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le]
    simp
  rw [← heq]
  exact eLpNorm_mono_enorm hpoint

/-- All the fattened annuli lie between the radii `2^k` and `2^{k+1}`. -/
theorem testStarSet_subset_shell {d k : ℕ} (hk : 4 ≤ k) :
    testStarSet d k ⊆ radialAnnulusIcc d ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) := by
  intro x hx
  have hx' : ∃ n ∈ (Finset.Icc 1 (2 ^ (k - 5)) : Finset ℕ), ‖x‖ ∈ annulusStar k n := by
    unfold testStarSet at hx
    simpa only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] using hx
  obtain ⟨n, hn, hxn⟩ := hx'
  rw [Finset.mem_Icc] at hn
  rw [annulusStar, mem_Icc] at hxn
  have hncast : (n : ℝ) ≤ 2 ^ (k - 5) := by exact_mod_cast hn.2
  have hpow : ((2 : ℝ) ^ (k - 5)) * 8 + 7 ≤ (2 : ℝ) ^ k := by
    have hsplit : (2 : ℝ) ^ k = 2 ^ (k - 5) * 2 ^ 5 ∨ k < 5 := by
      rcases Nat.lt_or_ge k 5 with h | h
      · exact Or.inr h
      · left
        rw [← pow_add]
        congr 1
        omega
    rcases hsplit with hsplit | hlt
    · rw [hsplit]
      have h1 : (1 : ℝ) ≤ 2 ^ (k - 5) := one_le_pow₀ (by norm_num)
      nlinarith [h1]
    · interval_cases k
      · norm_num
  rw [radialAnnulusIcc, mem_setOf_eq, mem_Icc]
  refine ⟨by nlinarith [hxn.1, hn.1], ?_⟩
  have hupper : (2 : ℝ) ^ k + 8 * n + 7 ≤ (2 : ℝ) ^ (k + 1) := by
    rw [pow_succ]
    nlinarith [hncast, hpow]
  linarith [hxn.2, hupper]

/-- The volume of the union of the fattened annuli is at most the volume of
that shell. -/
theorem volume_testStarSet_le {d k : ℕ} (hd : 0 < d) (hk : 4 ≤ k) :
    volume (testStarSet d k) ≤
      ENNReal.ofReal (((2 : ℝ) ^ (k + 1)) ^ d - ((2 : ℝ) ^ k) ^ d) *
        volume (Metric.ball (0 : Euclidean d) 1) := by
  calc
    volume (testStarSet d k) ≤
        volume (radialAnnulusIcc d ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) :=
      measure_mono (testStarSet_subset_shell hk)
    _ = _ := volume_radialAnnulusIcc hd (by positivity)
        (by exact pow_le_pow_right₀ (by norm_num) (by omega))

/-- The core annuli are pairwise disjoint. -/
theorem pairwiseDisjoint_testCore (d k : ℕ) :
    ((Finset.Icc 1 (2 ^ (k - 5)) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun n => {x : Euclidean d | ‖x‖ ∈ annulusCore k n}) := by
  intro m _ n _ hmn
  rw [Function.onFun, Set.disjoint_left]
  intro x hxm hxn
  have hm : ‖x‖ ∈ annulusStar k m := annulusCore_subset_annulusStar k m hxm
  have hn : ‖x‖ ∈ annulusStar k n := annulusCore_subset_annulusStar k n hxn
  exact (Set.disjoint_left.mp (annulusStar_disjoint (k := k) hmn)) hm hn

/-- A lower bound for the volume of the union of the core annuli: each
contributes at least `2 · (2^k)^{d-1}` times the unit ball volume. -/
theorem volume_testCoreSet_ge {d k : ℕ} (hd : 0 < d) :
    ((2 ^ (k - 5) : ℕ) : ENNReal) *
        (ENNReal.ofReal (2 * ((2 : ℝ) ^ k) ^ (d - 1)) *
          volume (Metric.ball (0 : Euclidean d) 1)) ≤
      volume (testCoreSet d k) := by
  have hterm : ∀ n ∈ (Finset.Icc 1 (2 ^ (k - 5)) : Finset ℕ),
      ENNReal.ofReal (2 * ((2 : ℝ) ^ k) ^ (d - 1)) *
          volume (Metric.ball (0 : Euclidean d) 1) ≤
        volume {x : Euclidean d | ‖x‖ ∈ annulusCore k n} := by
    intro n hn
    have hlow : (0 : ℝ) ≤ (2 : ℝ) ^ k + 8 * n + 3 := by positivity
    have hle : (2 : ℝ) ^ k + 8 * n + 3 ≤ (2 : ℝ) ^ k + 8 * n + 5 := by linarith
    have hvol : volume {x : Euclidean d | ‖x‖ ∈ annulusCore k n} =
        ENNReal.ofReal (((2 : ℝ) ^ k + 8 * n + 5) ^ d -
            ((2 : ℝ) ^ k + 8 * n + 3) ^ d) *
          volume (Metric.ball (0 : Euclidean d) 1) :=
      volume_radialAnnulusIcc hd hlow hle
    rw [hvol]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    have hpow := brrs_pow_sub_pow_ge hlow hle m
    have hmono : ((2 : ℝ) ^ k) ^ m ≤ ((2 : ℝ) ^ k + 8 * n + 3) ^ m := by
      refine pow_le_pow_left₀ (by positivity) ?_ m
      have : (0 : ℝ) ≤ 8 * n := by positivity
      linarith
    have harith : ((2 : ℝ) ^ k + 8 * n + 3) ^ m *
        (((2 : ℝ) ^ k + 8 * n + 5) - ((2 : ℝ) ^ k + 8 * n + 3)) =
        ((2 : ℝ) ^ k + 8 * n + 3) ^ m * 2 := by ring
    simp only [Nat.add_sub_cancel]
    nlinarith [hpow, hmono]
  calc
    ((2 ^ (k - 5) : ℕ) : ENNReal) *
        (ENNReal.ofReal (2 * ((2 : ℝ) ^ k) ^ (d - 1)) *
          volume (Metric.ball (0 : Euclidean d) 1)) =
        ∑ _n ∈ (Finset.Icc 1 (2 ^ (k - 5)) : Finset ℕ),
          ENNReal.ofReal (2 * ((2 : ℝ) ^ k) ^ (d - 1)) *
            volume (Metric.ball (0 : Euclidean d) 1) := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp [nsmul_eq_mul]
    _ ≤ ∑ n ∈ (Finset.Icc 1 (2 ^ (k - 5)) : Finset ℕ),
          volume {x : Euclidean d | ‖x‖ ∈ annulusCore k n} :=
      Finset.sum_le_sum hterm
    _ = volume (testCoreSet d k) := by
      unfold testCoreSet
      exact (measure_biUnion_finset (pairwiseDisjoint_testCore d k)
        (fun n _ => measurableSet_radialAnnulusIcc d _ _)).symm

/-- The core volume bound in the normalized form `2^{kd}/16` times the unit
ball volume. -/
theorem volume_testCoreSet_ge' {d k : ℕ} (hd : 0 < d) (hk : 5 ≤ k) :
    ENNReal.ofReal ((2 : ℝ) ^ (k * d) / 16) *
        volume (Metric.ball (0 : Euclidean d) 1) ≤ volume (testCoreSet d k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  refine le_trans (le_of_eq ?_) (volume_testCoreSet_ge hd)
  have hcast : ((2 ^ (j + 5 - 5) : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ j) := by
    simp only [Nat.add_sub_cancel]
    rw [← ENNReal.ofReal_natCast]
    congr 1
    push_cast
    ring
  have key : (2 : ℝ) ^ ((j + 5) * (m + 1)) / 16 =
      (2 : ℝ) ^ j * (2 * ((2 : ℝ) ^ (j + 5)) ^ (m + 1 - 1)) := by
    simp only [Nat.add_sub_cancel]
    rw [← pow_mul, show (j + 5) * (m + 1) = (j + 5) * m + (j + 5) by ring, pow_add,
      show (2 : ℝ) ^ (j + 5) = 2 ^ j * 32 by rw [pow_add]; norm_num]
    ring
  rw [hcast, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), key]

/-- The star volume bound in the normalized form `2^{kd}(2^d - 1)` times the
unit ball volume. -/
theorem volume_testStarSet_le' {d k : ℕ} (hd : 0 < d) (hk : 4 ≤ k) :
    volume (testStarSet d k) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (k * d) * (2 ^ d - 1)) *
        volume (Metric.ball (0 : Euclidean d) 1) := by
  refine le_trans (volume_testStarSet_le hd hk) (le_of_eq ?_)
  congr 2
  rw [← pow_mul, ← pow_mul, show (k + 1) * d = k * d + d by ring, pow_add]
  ring

set_option maxHeartbeats 1000000 in
/-- **BRS (3.1).**  The test functions witness the lower bound
`‖M_E f_k‖_q ≳ 2^{-kd(1/p - 1/q)} ‖f_k‖_p`. -/
theorem le_eLpNorm_M_testProfile_ratio {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 5 ≤ k →
      ENNReal.ofReal (c * (2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q)))) *
          eLpNorm (fun x : Euclidean d => testProfile k ‖x‖) (ENNReal.ofReal p) volume ≤
        eLpNorm (M E (fun x : Euclidean d => testProfile k ‖x‖))
          (ENNReal.ofReal q) volume := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V := by
    rw [hV]
    exact ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  have hVeq : volume (Metric.ball (0 : Euclidean d) 1) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hVtop]
  have hd1 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hC1 : 0 < ((2 : ℝ) ^ d - 1 + 1) * V := by positivity
  set C1 : ℝ := (2 ^ d - 1) * V with hC1def
  have hC1pos : 0 < C1 := by
    rw [hC1def]
    have h2 : (1 : ℝ) < 2 ^ d := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
      simp only [pow_one] at this
      nlinarith
    have : (0 : ℝ) < 2 ^ d - 1 := by linarith
    positivity
  set C2 : ℝ := V / 16 with hC2def
  have hC2pos : 0 < C2 := by
    rw [hC2def]
    positivity
  refine ⟨C2 ^ (1 / q) / C1 ^ (1 / p), by positivity, ?_⟩
  intro k hk
  -- the two volume bounds, in `ofReal` form
  have hstar : eLpNorm (fun x : Euclidean d => testProfile k ‖x‖)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (((2 : ℝ) ^ (k * d) * C1) ^ (1 / p)) := by
    rw [eLpNorm_testProfile_lift d k hp]
    have hle : volume (testStarSet d k) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (k * d) * C1) := by
      refine le_trans (volume_testStarSet_le' hd (by omega)) (le_of_eq ?_)
      rw [hVeq, ← ENNReal.ofReal_mul (by positivity), hC1def]
      congr 1
      ring
    calc
      volume (testStarSet d k) ^ (1 / p) ≤
          (ENNReal.ofReal ((2 : ℝ) ^ (k * d) * C1)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hle (by positivity)
      _ = ENNReal.ofReal (((2 : ℝ) ^ (k * d) * C1) ^ (1 / p)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
  have hcore : ENNReal.ofReal (((2 : ℝ) ^ (k * d) * C2) ^ (1 / q)) ≤
      eLpNorm (M E (fun x : Euclidean d => testProfile k ‖x‖))
        (ENNReal.ofReal q) volume := by
    have hge : ENNReal.ofReal ((2 : ℝ) ^ (k * d) * C2) ≤ volume (testCoreSet d k) := by
      refine le_trans (le_of_eq ?_) (volume_testCoreSet_ge' hd hk)
      rw [hVeq, ← ENNReal.ofReal_mul (by positivity), hC2def]
      congr 1
      ring
    calc
      ENNReal.ofReal (((2 : ℝ) ^ (k * d) * C2) ^ (1 / q)) =
          (ENNReal.ofReal ((2 : ℝ) ^ (k * d) * C2)) ^ (1 / q) :=
        (ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)).symm
      _ ≤ volume (testCoreSet d k) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hge (by positivity)
      _ ≤ _ := le_eLpNorm_M_testProfile_lift hd hE hEne hq
  -- the real-number inequality between the two explicit bounds
  have hpow : ∀ a : ℝ, 0 < a → ((2 : ℝ) ^ (k * d) * a) ^ (1 / p) =
      (2 : ℝ) ^ (((k : ℝ) * d) / p) * a ^ (1 / p) := by
    intro a ha
    rw [Real.mul_rpow (by positivity) ha.le, ← Real.rpow_natCast (2 : ℝ) (k * d),
      ← Real.rpow_mul (by norm_num)]
    congr 2
    · push_cast
      ring
  have hpowq : ∀ a : ℝ, 0 < a → ((2 : ℝ) ^ (k * d) * a) ^ (1 / q) =
      (2 : ℝ) ^ (((k : ℝ) * d) / q) * a ^ (1 / q) := by
    intro a ha
    rw [Real.mul_rpow (by positivity) ha.le, ← Real.rpow_natCast (2 : ℝ) (k * d),
      ← Real.rpow_mul (by norm_num)]
    congr 2
    · push_cast
      ring
  have hreal : (C2 ^ (1 / q) / C1 ^ (1 / p)) *
        (2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q))) *
        ((2 : ℝ) ^ (k * d) * C1) ^ (1 / p) =
      ((2 : ℝ) ^ (k * d) * C2) ^ (1 / q) := by
    rw [hpow C1 hC1pos, hpowq C2 hC2pos]
    have hsplit : (2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q))) *
        (2 : ℝ) ^ (((k : ℝ) * d) / p) = (2 : ℝ) ^ (((k : ℝ) * d) / q) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      field_simp
      ring
    calc
      (C2 ^ (1 / q) / C1 ^ (1 / p)) *
            (2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q))) *
            ((2 : ℝ) ^ (((k : ℝ) * d) / p) * C1 ^ (1 / p)) =
          ((2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q))) *
            (2 : ℝ) ^ (((k : ℝ) * d) / p)) *
            (C2 ^ (1 / q) * (C1 ^ (1 / p) / C1 ^ (1 / p))) := by ring
      _ = (2 : ℝ) ^ (((k : ℝ) * d) / q) * C2 ^ (1 / q) := by
          rw [hsplit, div_self (by positivity : C1 ^ (1 / p) ≠ 0)]
          ring
  calc
    ENNReal.ofReal (C2 ^ (1 / q) / C1 ^ (1 / p) *
          (2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q)))) *
        eLpNorm (fun x : Euclidean d => testProfile k ‖x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C2 ^ (1 / q) / C1 ^ (1 / p) *
          (2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q)))) *
          ENNReal.ofReal (((2 : ℝ) ^ (k * d) * C1) ^ (1 / p)) :=
      mul_le_mul' le_rfl hstar
    _ = ENNReal.ofReal (((2 : ℝ) ^ (k * d) * C2) ^ (1 / q)) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← hreal]
    _ ≤ _ := hcore

theorem isNormRadial_testProfile_lift (d k : ℕ) :
    _root_.Auto.RadialFourierTransform.IsNormRadial
      (fun x : Euclidean d => testProfile k ‖x‖) := by
  intro x y hxy
  simp only [hxy]

theorem measurable_testProfile_lift (d k : ℕ) :
    Measurable (fun x : Euclidean d => testProfile k ‖x‖) :=
  (measurable_testProfile k).comp continuous_norm.measurable

theorem volume_testStarSet_lt_top {d k : ℕ} (hd : 0 < d) (hk : 4 ≤ k) :
    volume (testStarSet d k) < ⊤ := by
  refine lt_of_le_of_lt (volume_testStarSet_le' hd hk) ?_
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((measure_mono Metric.ball_subset_closedBall).trans_lt measure_closedBall_lt_top)

theorem volume_testStarSet_pos {d k : ℕ} (hd : 0 < d) : 0 < volume (testStarSet d k) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hone : (1 : ℕ) ∈ (Finset.Icc 1 (2 ^ (k - 5)) : Finset ℕ) := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, Nat.one_le_two_pow⟩
  have hsub : {x : Euclidean d | ‖x‖ ∈ annulusStar k 1} ⊆ testStarSet d k := by
    unfold testStarSet
    exact Set.subset_biUnion_of_mem
      (u := fun n : ℕ => {x : Euclidean d | ‖x‖ ∈ annulusStar k n}) hone
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  have hlow : (0 : ℝ) ≤ (2 : ℝ) ^ k + 8 * (1 : ℕ) + 1 := by positivity
  have hle : (2 : ℝ) ^ k + 8 * (1 : ℕ) + 1 ≤ (2 : ℝ) ^ k + 8 * (1 : ℕ) + 7 := by
    push_cast
    linarith
  rw [show {x : Euclidean d | ‖x‖ ∈ annulusStar k 1} =
      radialAnnulusIcc d ((2 : ℝ) ^ k + 8 * (1 : ℕ) + 1)
        ((2 : ℝ) ^ k + 8 * (1 : ℕ) + 7) from rfl,
    volume_radialAnnulusIcc hd hlow hle]
  refine ENNReal.mul_pos ?_ ?_
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have hstrict : (2 : ℝ) ^ k + 8 * (1 : ℕ) + 1 < (2 : ℝ) ^ k + 8 * (1 : ℕ) + 7 := by
      push_cast
      linarith
    have := pow_lt_pow_left₀ hstrict hlow hd.ne'
    linarith
  · exact (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos).ne'

theorem memLp_testProfile_lift {d k : ℕ} (hd : 0 < d) (hk : 4 ≤ k) {p : ℝ}
    (hp : 0 < p) :
    MemLp (fun x : Euclidean d => testProfile k ‖x‖) (ENNReal.ofReal p) volume := by
  refine ⟨(measurable_testProfile_lift d k).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_testProfile_lift d k hp]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
    (volume_testStarSet_lt_top hd hk).ne

set_option maxHeartbeats 1000000 in
/-- **BRS Lemma 3.1.**  A radial `L^p → L^q` bound for the spherical maximal
operator with dilations in `E ⊆ [1,2]` forces `p ≤ q`. -/
theorem le_of_hasRadialStrongType {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : HasRadialStrongType d E (ENNReal.ofReal p) (ENNReal.ofReal q)) : p ≤ q := by
  by_contra hcon
  have hqp : q < p := lt_of_not_ge hcon
  set δ : ℝ := 1 / q - 1 / p with hδ
  have hδpos : 0 < δ := by
    rw [hδ, sub_pos]
    exact one_div_lt_one_div_of_lt hq hqp
  obtain ⟨C, hC, hbound⟩ := h
  obtain ⟨c, hc, hratio⟩ := le_eLpNorm_M_testProfile_ratio hd hE hEne hp hq
  -- the geometric factor stays bounded by `C / c`
  have hkey : ∀ k : ℕ, 5 ≤ k → c * (2 : ℝ) ^ ((k : ℝ) * d * δ) ≤ C := by
    intro k hk
    have hk4 : 4 ≤ k := by omega
    have hmem := memLp_testProfile_lift (d := d) (k := k) hd hk4 hp
    have hrad := isNormRadial_testProfile_lift d k
    obtain ⟨-, hupper⟩ := hbound _ hmem hrad
    have hlower := hratio k hk
    have hNpos : 0 < eLpNorm (fun x : Euclidean d => testProfile k ‖x‖)
        (ENNReal.ofReal p) volume := by
      rw [eLpNorm_testProfile_lift d k hp]
      exact ENNReal.rpow_pos (volume_testStarSet_pos hd)
        (volume_testStarSet_lt_top hd hk4).ne
    have hNtop : eLpNorm (fun x : Euclidean d => testProfile k ‖x‖)
        (ENNReal.ofReal p) volume ≠ ⊤ := hmem.eLpNorm_lt_top.ne
    have hchain : ENNReal.ofReal (c * (2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q)))) *
        eLpNorm (fun x : Euclidean d => testProfile k ‖x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun x : Euclidean d => testProfile k ‖x‖) (ENNReal.ofReal p) volume :=
      le_trans hlower hupper
    have hchain' : eLpNorm (fun x : Euclidean d => testProfile k ‖x‖)
          (ENNReal.ofReal p) volume *
          ENNReal.ofReal (c * (2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q)))) ≤
        eLpNorm (fun x : Euclidean d => testProfile k ‖x‖) (ENNReal.ofReal p) volume *
          ENNReal.ofReal C := by
      rw [mul_comm _ (ENNReal.ofReal
          (c * (2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q))))),
        mul_comm _ (ENNReal.ofReal C)]
      exact hchain
    have hcancel : ENNReal.ofReal (c * (2 : ℝ) ^ (-((k : ℝ) * d * (1 / p - 1 / q)))) ≤
        ENNReal.ofReal C :=
      (ENNReal.mul_le_mul_iff_right hNpos.ne' hNtop).mp hchain'
    have hreal := (ENNReal.ofReal_le_ofReal_iff hC.le).mp hcancel
    have hexp : -((k : ℝ) * d * (1 / p - 1 / q)) = (k : ℝ) * d * δ := by
      rw [hδ]
      ring
    rwa [hexp] at hreal
  -- but the geometric factor is unbounded
  have hbase : (1 : ℝ) < (2 : ℝ) ^ ((d : ℝ) * δ) := by
    refine Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr ?_
    refine Or.inl ⟨by norm_num, ?_⟩
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / c) hbase
  have hk : 5 ≤ n + 5 := by omega
  have hkey' := hkey (n + 5) hk
  have hpow : (2 : ℝ) ^ (((n + 5 : ℕ) : ℝ) * d * δ) =
      ((2 : ℝ) ^ ((d : ℝ) * δ)) ^ (n + 5) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((d : ℝ) * δ)) (n + 5), ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  rw [hpow] at hkey'
  have hmono : ((2 : ℝ) ^ ((d : ℝ) * δ)) ^ n ≤ ((2 : ℝ) ^ ((d : ℝ) * δ)) ^ (n + 5) :=
    pow_le_pow_right₀ hbase.le (by omega)
  have hCc : C / c < ((2 : ℝ) ^ ((d : ℝ) * δ)) ^ (n + 5) := lt_of_lt_of_le hn hmono
  rw [div_lt_iff₀ hc] at hCc
  nlinarith [hkey', hCc]

/-! ## The thin shell test function of Lemma 3.2(i) -/

/-- The radial lift of an interval indicator is the indicator of the
corresponding annulus. -/
theorem indicator_lift_eq (d : ℕ) (a b : ℝ) :
    (fun x : Euclidean d => (Icc a b).indicator (fun _ => (1 : ℂ)) ‖x‖) =
      (radialAnnulusIcc d a b).indicator (fun _ => (1 : ℂ)) := by
  funext x
  by_cases hx : ‖x‖ ∈ Icc a b
  · have hx' : x ∈ radialAnnulusIcc d a b := hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
  · have hx' : x ∉ radialAnnulusIcc d a b := hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']

theorem measurable_indicator_lift (d : ℕ) (a b : ℝ) :
    Measurable (fun x : Euclidean d => (Icc a b).indicator (fun _ => (1 : ℂ)) ‖x‖) := by
  rw [indicator_lift_eq]
  exact measurable_const.indicator (measurableSet_radialAnnulusIcc d a b)

theorem isNormRadial_indicator_lift (d : ℕ) (a b : ℝ) :
    _root_.Auto.RadialFourierTransform.IsNormRadial
      (fun x : Euclidean d => (Icc a b).indicator (fun _ => (1 : ℂ)) ‖x‖) := by
  intro x y hxy
  simp only [hxy]

/-- The `L^p` norm of an annulus indicator. -/
theorem eLpNorm_indicator_lift (d : ℕ) (a b : ℝ) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x : Euclidean d => (Icc a b).indicator (fun _ => (1 : ℂ)) ‖x‖)
        (ENNReal.ofReal p) volume =
      volume (radialAnnulusIcc d a b) ^ (1 / p) := by
  rw [indicator_lift_eq,
    eLpNorm_indicator_const (measurableSet_radialAnnulusIcc d a b)
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  simp

/-- A sphere of radius `t₀` centred within distance `δ` of the origin stays in
the shell of radii `[t₀ - δ, t₀ + δ]`, so the average of the shell indicator
is one. -/
theorem sphericalAverage_shell_eq_one {d : ℕ} (hd : 0 < d) {t₀ δ : ℝ}
    (ht₀ : 0 ≤ t₀) {x : Euclidean d} (hx : ‖x‖ ≤ δ) :
    _root_.Spherical.sphericalAverage t₀
        (fun y : Euclidean d =>
          (Icc (t₀ - δ) (t₀ + δ)).indicator (fun _ => (1 : ℂ)) ‖y‖) x = 1 := by
  have hpoint : ∀ ω : Metric.sphere (0 : Euclidean d) 1,
      (Icc (t₀ - δ) (t₀ + δ)).indicator (fun _ => (1 : ℂ))
        ‖x + t₀ • (ω : Euclidean d)‖ = 1 := by
    intro ω
    have hω : ‖(ω : Euclidean d)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have hsmul : ‖t₀ • (ω : Euclidean d)‖ = t₀ := by
      rw [norm_smul, Real.norm_eq_abs, hω, mul_one, abs_of_nonneg ht₀]
    have hupper : ‖x + t₀ • (ω : Euclidean d)‖ ≤ t₀ + δ := by
      calc
        ‖x + t₀ • (ω : Euclidean d)‖ ≤ ‖x‖ + ‖t₀ • (ω : Euclidean d)‖ :=
          norm_add_le _ _
        _ = ‖x‖ + t₀ := by rw [hsmul]
        _ ≤ t₀ + δ := by linarith
    have hlower : t₀ - δ ≤ ‖x + t₀ • (ω : Euclidean d)‖ := by
      have h : ‖t₀ • (ω : Euclidean d)‖ ≤ ‖x + t₀ • (ω : Euclidean d)‖ + ‖x‖ := by
        have hsub := norm_sub_le (x + t₀ • (ω : Euclidean d)) x
        rwa [add_sub_cancel_left] at hsub
      rw [hsmul] at h
      linarith
    have hmem : ‖x + t₀ • (ω : Euclidean d)‖ ∈ Icc (t₀ - δ) (t₀ + δ) :=
      ⟨hlower, hupper⟩
    exact Set.indicator_of_mem hmem _
  rw [_root_.Spherical.sphericalAverage,
    integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const,
    unitSphereMeasure_real_univ hd, one_smul]

/-- Where the maximal function is at least one, its `L^q` norm dominates the
`q`-th root of the volume. -/
theorem le_eLpNorm_of_one_le_on {d : ℕ} {E : Set ℝ} {f : Euclidean d → ℂ}
    {S : Set (Euclidean d)} (hS : MeasurableSet S)
    (hone : ∀ x ∈ S, (1 : ENNReal) ≤ M E f x) {q : ℝ} (hq : 0 < q) :
    volume S ^ (1 / q) ≤ eLpNorm (M E f) (ENNReal.ofReal q) volume := by
  have hpoint : ∀ x : Euclidean d,
      ‖S.indicator (fun _ => (1 : ℂ)) x‖ₑ ≤ ‖M E f x‖ₑ := by
    intro x
    by_cases hx : x ∈ S
    · calc
        ‖S.indicator (fun _ => (1 : ℂ)) x‖ₑ = 1 := by
          rw [Set.indicator_of_mem hx]
          simp
        _ ≤ M E f x := hone x hx
    · rw [Set.indicator_of_notMem hx]
      simp
  have heq : eLpNorm (S.indicator (fun _ => (1 : ℂ))) (ENNReal.ofReal q) volume =
      volume S ^ (1 / q) := by
    rw [eLpNorm_indicator_const hS
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le]
    simp
  rw [← heq]
  exact eLpNorm_mono_enorm hpoint

/-- The volume of a ball, in the normalized form used below. -/
theorem volume_closedBall_eq {d : ℕ} (hd : 0 < d) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (Metric.closedBall (0 : Euclidean d) δ) =
      ENNReal.ofReal (δ ^ d) * volume (Metric.ball (0 : Euclidean d) 1) := by
  have hfr : Module.finrank ℝ (Euclidean d) = d := finrank_euclideanSpace_fin
  have h := Measure.addHaar_closedBall (volume : Measure (Euclidean d))
    (0 : Euclidean d) hδ
  rw [hfr] at h
  exact h

/-- A shell of half-width `δ` at radius in `[1,2]` has volume `O(δ)`. -/
theorem volume_thin_shell_le {d : ℕ} (hd : 0 < d) {t₀ δ : ℝ} (ht₀ : 1 ≤ t₀)
    (ht₀' : t₀ ≤ 2) (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    volume (radialAnnulusIcc d (t₀ - δ) (t₀ + δ)) ≤
      ENNReal.ofReal (2 * d * 3 ^ (d - 1) * δ) *
        volume (Metric.ball (0 : Euclidean d) 1) := by
  have hlow : (0 : ℝ) ≤ t₀ - δ := by linarith
  have hle : t₀ - δ ≤ t₀ + δ := by linarith
  rw [volume_radialAnnulusIcc hd hlow hle]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hpowle : (t₀ - δ) ^ d ≤ (t₀ + δ) ^ d := pow_le_pow_left₀ hlow hle d
  have hmax : max |t₀ + δ| |t₀ - δ| ≤ 3 := by
    refine max_le ?_ ?_
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_nonneg hlow]
      linarith
  have hmaxnonneg : (0 : ℝ) ≤ max |t₀ + δ| |t₀ - δ| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  calc
    (t₀ + δ) ^ d - (t₀ - δ) ^ d = |(t₀ + δ) ^ d - (t₀ - δ) ^ d| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hpowle)]
    _ ≤ |(t₀ + δ) - (t₀ - δ)| * (d : ℝ) * max |t₀ + δ| |t₀ - δ| ^ (d - 1) :=
      abs_pow_sub_pow_le (t₀ + δ) (t₀ - δ) d
    _ ≤ (2 * δ) * (d : ℝ) * 3 ^ (d - 1) := by
      have hsep : |(t₀ + δ) - (t₀ - δ)| = 2 * δ := by
        rw [abs_of_nonneg (by linarith)]
        ring
      rw [hsep]
      gcongr
    _ = 2 * (d : ℝ) * 3 ^ (d - 1) * δ := by ring

set_option maxHeartbeats 1000000 in
/-- The thin-shell test inequality behind Lemma 3.2(i): a radial bound with
constant `C` forces the displayed inequality at every half-width `δ ≤ 1`. -/
theorem shell_test_inequality {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ f : Euclidean d → ℂ, MemLp f (ENNReal.ofReal p) volume →
      _root_.Auto.RadialFourierTransform.IsNormRadial f →
        eLpNorm (M E f) (ENNReal.ofReal q) volume ≤
          ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    (δ ^ d * (volume (Metric.ball (0 : Euclidean d) 1)).toReal) ^ (1 / q) ≤
      C * ((2 * d * 3 ^ (d - 1) * δ) *
        (volume (Metric.ball (0 : Euclidean d) 1)).toReal) ^ (1 / p) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨t₀, ht₀E⟩ := hEne
  have ht₀ : t₀ ∈ Icc (1 : ℝ) 2 := hE ht₀E
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  have hVeq : volume (Metric.ball (0 : Euclidean d) 1) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hVtop]
  set f : Euclidean d → ℂ := fun y =>
    (Icc (t₀ - δ) (t₀ + δ)).indicator (fun _ => (1 : ℂ)) ‖y‖ with hf
  have hannvol : volume (radialAnnulusIcc d (t₀ - δ) (t₀ + δ)) ≤
      ENNReal.ofReal ((2 * d * 3 ^ (d - 1) * δ) * V) := by
    refine le_trans (volume_thin_shell_le hd ht₀.1 ht₀.2 hδ hδ') (le_of_eq ?_)
    rw [hVeq, ← ENNReal.ofReal_mul (by positivity)]
  have hnormf : eLpNorm f (ENNReal.ofReal p) volume =
      volume (radialAnnulusIcc d (t₀ - δ) (t₀ + δ)) ^ (1 / p) :=
    eLpNorm_indicator_lift d _ _ hp
  have hmem : MemLp f (ENNReal.ofReal p) volume := by
    refine ⟨(measurable_indicator_lift d _ _).aestronglyMeasurable, ?_⟩
    rw [hnormf]
    refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
    exact (lt_of_le_of_lt hannvol ENNReal.ofReal_lt_top).ne
  have hrad := isNormRadial_indicator_lift d (t₀ - δ) (t₀ + δ)
  -- lower bound on the maximal function over the small ball
  have hone : ∀ x ∈ Metric.closedBall (0 : Euclidean d) δ, (1 : ENNReal) ≤ M E f x := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have havg : _root_.Spherical.sphericalAverage t₀ f x = 1 :=
      sphericalAverage_shell_eq_one hd (le_trans zero_le_one ht₀.1) hx
    unfold M _root_.Spherical.restrictedSphericalMaximal
    refine le_iSup_of_le t₀ (le_iSup_of_le ⟨ht₀E, lt_of_lt_of_le zero_lt_one ht₀.1⟩ ?_)
    rw [havg]
    simp
  have hlow : ENNReal.ofReal ((δ ^ d * V) ^ (1 / q)) ≤
      eLpNorm (M E f) (ENNReal.ofReal q) volume := by
    refine le_trans (le_of_eq ?_)
      (le_eLpNorm_of_one_le_on measurableSet_closedBall hone hq)
    rw [volume_closedBall_eq hd hδ.le, hVeq, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  have hup : eLpNorm f (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (((2 * d * 3 ^ (d - 1) * δ) * V) ^ (1 / p)) := by
    rw [hnormf, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    exact ENNReal.rpow_le_rpow hannvol (by positivity)
  have hchain : ENNReal.ofReal ((δ ^ d * V) ^ (1 / q)) ≤
      ENNReal.ofReal C *
        ENNReal.ofReal (((2 * d * 3 ^ (d - 1) * δ) * V) ^ (1 / p)) :=
    le_trans hlow (le_trans (hbound f hmem hrad) (mul_le_mul' le_rfl hup))
  rw [← ENNReal.ofReal_mul hC.le] at hchain
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain

set_option maxHeartbeats 1000000 in
/-- **BRS Lemma 3.2(i).**  A radial `L^p → L^q` bound for the spherical maximal
operator with dilations in a nonempty `E ⊆ [1,2]` forces `q ≤ pd`. -/
theorem le_mul_of_hasRadialStrongType {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : HasRadialStrongType d E (ENNReal.ofReal p) (ENNReal.ofReal q)) :
    q ≤ p * d := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨C, hC, hbound'⟩ := h
  have hbound : ∀ f : Euclidean d → ℂ, MemLp f (ENNReal.ofReal p) volume →
      _root_.Auto.RadialFourierTransform.IsNormRadial f →
        eLpNorm (M E f) (ENNReal.ofReal q) volume ≤
          ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume :=
    fun f hf hrad => (hbound' f hf hrad).2
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  set K : ℝ := 2 * d * 3 ^ (d - 1) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  set u : ℝ := (2 : ℝ)⁻¹ with hu
  have hu0 : 0 < u := by rw [hu]; norm_num
  have hu1 : u < 1 := by rw [hu]; norm_num
  -- the exponent gap
  have hgap : (d : ℝ) / q - 1 / p < 0 := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    rw [sub_neg, div_lt_div_iff₀ hq hp]
    nlinarith [hcon]
  set a : ℝ := u ^ ((d : ℝ) / q) with ha
  set b : ℝ := u ^ ((1 : ℝ) / p) with hb
  have hapos : 0 < a := Real.rpow_pos_of_pos hu0 _
  have hbpos : 0 < b := Real.rpow_pos_of_pos hu0 _
  -- the ratio exceeds one
  have hratio : (1 : ℝ) < a / b := by
    rw [ha, hb, ← Real.rpow_sub hu0]
    exact (Real.one_lt_rpow_iff_of_pos hu0).mpr (Or.inr ⟨hu1, hgap⟩)
  -- the family of inequalities
  have hfam : ∀ k : ℕ, (a / b) ^ k ≤ C * (K * V) ^ (1 / p) / V ^ (1 / q) := by
    intro k
    have hδpos : (0 : ℝ) < u ^ k := pow_pos hu0 k
    have hδle : u ^ k ≤ 1 := pow_le_one₀ hu0.le hu1.le
    have hineq := shell_test_inequality hd hE hEne hp hq hC hbound hδpos hδle
    rw [← hV, ← hK] at hineq
    -- rewrite both sides in terms of `a` and `b`
    have hleft : ((u ^ k) ^ d * V) ^ (1 / q) = a ^ k * V ^ (1 / q) := by
      rw [Real.mul_rpow (by positivity) hVpos.le, ha]
      congr 1
      rw [← pow_mul, ← Real.rpow_natCast u (k * d), ← Real.rpow_mul hu0.le,
        ← Real.rpow_natCast (u ^ ((d : ℝ) / q)) k, ← Real.rpow_mul hu0.le]
      congr 1
      push_cast
      field_simp
    have hright : (K * u ^ k * V) ^ (1 / p) = (K * V) ^ (1 / p) * b ^ k := by
      rw [show K * u ^ k * V = (K * V) * u ^ k by ring,
        Real.mul_rpow (by positivity) (by positivity), hb]
      congr 1
      rw [← Real.rpow_natCast u k, ← Real.rpow_mul hu0.le,
        ← Real.rpow_natCast (u ^ ((1 : ℝ) / p)) k, ← Real.rpow_mul hu0.le]
      congr 1
      ring
    rw [hleft, hright] at hineq
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      a ^ k * V ^ (1 / q) ≤ C * ((K * V) ^ (1 / p) * b ^ k) := hineq
      _ = C * (K * V) ^ (1 / p) * b ^ k := by ring
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (C * (K * V) ^ (1 / p) / V ^ (1 / q)) hratio
  exact absurd (hfam n) (not_le.mpr hn)

/-! ## The origin-ball test function of Lemma 3.2(ii) -/

/-- The radial annulus from `0` to `δ` is the closed ball. -/
theorem radialAnnulusIcc_zero (d : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    radialAnnulusIcc d 0 δ = Metric.closedBall (0 : Euclidean d) δ := by
  ext x
  simp only [radialAnnulusIcc, mem_setOf_eq, mem_Icc, Metric.mem_closedBall,
    dist_zero_right]
  exact ⟨fun h => h.2, fun h => ⟨norm_nonneg x, h⟩⟩

set_option maxHeartbeats 1000000 in
/-- **The cap estimate behind (3.2).**  If the sphere of radius `t` about `x`
passes within `δ/2` of the origin, then the spherical average of the indicator
of the ball `B(0,δ)` is at least a constant times `δ^{d-1}`. -/
theorem le_sphericalAverage_ballProfile {d : ℕ} (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (t δ : ℝ), 0 < δ → δ ≤ 1 → 1 ≤ t → t ≤ 2 →
      ∀ x : Euclidean d, |‖x‖ - t| ≤ δ / 2 →
        ENNReal.ofReal (c * δ ^ (d - 1)) ≤
          ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t
            (fun y : Euclidean d => (Icc 0 δ).indicator (fun _ => (1 : ℂ)) ‖y‖) x‖ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨c₀, hc₀pos, hc₀top, hcap⟩ := exists_stein_unitSurfaceMeasure_cap_ge_power n
  have hmass : 0 < surfaceMass (n + 1) := surfaceMass_pos (by omega)
  set c : ℝ := (c₀.toReal / 6 ^ n) / surfaceMass (n + 1) with hc
  have hc₀real : 0 < c₀.toReal := ENNReal.toReal_pos hc₀pos.ne' hc₀top
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  refine ⟨c, hcpos, ?_⟩
  intro t δ hδ hδ1 ht1 ht2 x hx
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hxnorm : 0 < ‖x‖ := by
    rw [abs_le] at hx
    have : t - δ / 2 ≤ ‖x‖ := by linarith [hx.1]
    have hlow : 0 < t - δ / 2 := by linarith
    linarith
  have hxle : ‖x‖ ≤ 2 + 1 := by
    rw [abs_le] at hx
    linarith [hx.2]
  -- the inward cap of radius `δ / 4`
  set v : Euclidean (n + 1) := steinInwardRadialDirection x with hv
  have hvnorm : ‖v‖ = 1 := norm_steinInwardRadialDirection hxnorm
  set A : Set (Metric.sphere (0 : Euclidean (n + 1)) 1) :=
    steinSphericalCap (n + 1) v (δ / 6) with hA
  have hAmeas : MeasurableSet A := measurableSet_steinSphericalCap _ _ _
  -- points of the cap are carried into the ball
  have hone : ∀ ω ∈ A, (Icc 0 δ).indicator (fun _ => (1 : ℝ))
      ‖x + t • (ω : Euclidean (n + 1))‖ = 1 := by
    intro ω hω
    have hclose : ‖x + ‖x‖ • (ω : Euclidean (n + 1))‖ < ‖x‖ * (δ / 6) :=
      stein_inward_cap_translate_subset_ball hxnorm hω
    have hωnorm : ‖(ω : Euclidean (n + 1))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have hdiff : ‖x + t • (ω : Euclidean (n + 1))‖ ≤
        ‖x + ‖x‖ • (ω : Euclidean (n + 1))‖ + |t - ‖x‖| := by
      have hsplit : x + t • (ω : Euclidean (n + 1)) =
          (x + ‖x‖ • (ω : Euclidean (n + 1))) +
            (t - ‖x‖) • (ω : Euclidean (n + 1)) := by
        module
      calc
        ‖x + t • (ω : Euclidean (n + 1))‖ ≤
            ‖x + ‖x‖ • (ω : Euclidean (n + 1))‖ +
              ‖(t - ‖x‖) • (ω : Euclidean (n + 1))‖ := by
          rw [hsplit]
          exact norm_add_le _ _
        _ = ‖x + ‖x‖ • (ω : Euclidean (n + 1))‖ + |t - ‖x‖| := by
          rw [norm_smul, Real.norm_eq_abs, hωnorm, mul_one]
    have habs : |t - ‖x‖| ≤ δ / 2 := by
      rw [abs_sub_comm]
      exact hx
    have hbound : ‖x + t • (ω : Euclidean (n + 1))‖ ≤ δ := by
      have h1 : ‖x‖ * (δ / 6) ≤ 3 * (δ / 6) := by
        have := hxle
        nlinarith [hδ.le]
      linarith [hdiff, habs, hclose.le, h1]
    have hmem : ‖x + t • (ω : Euclidean (n + 1))‖ ∈ Icc (0 : ℝ) δ :=
      ⟨norm_nonneg _, hbound⟩
    exact Set.indicator_of_mem hmem _
  -- integrability of the slice
  have hgmeas : Measurable
      (fun y : Euclidean (n + 1) => (Icc 0 δ).indicator (fun _ => (1 : ℝ)) ‖y‖) :=
    (measurable_const.indicator measurableSet_Icc).comp continuous_norm.measurable
  have hgb : ∀ y : Euclidean (n + 1),
      ‖(Icc 0 δ).indicator (fun _ => (1 : ℝ)) ‖y‖‖ ≤ 1 := by
    intro y
    by_cases hmem : ‖y‖ ∈ Icc (0 : ℝ) δ
    · rw [Set.indicator_of_mem hmem]
      norm_num
    · rw [Set.indicator_of_notMem hmem]
      norm_num
  have hint := stein_integrable_sphere_comp_of_bounded_measurable hgmeas hgb t x
  have hnonneg : ∀ ω : Metric.sphere (0 : Euclidean (n + 1)) 1,
      0 ≤ (Icc 0 δ).indicator (fun _ => (1 : ℝ)) ‖x + t • (ω : Euclidean (n + 1))‖ := by
    intro ω
    by_cases hmem : ‖x + t • (ω : Euclidean (n + 1))‖ ∈ Icc (0 : ℝ) δ
    · rw [Set.indicator_of_mem hmem]
      norm_num
    · rw [Set.indicator_of_notMem hmem]
  have hcapbound := hcap v hvnorm (δ / 6) (by positivity) (by linarith)
  have hfrac := stein_cap_fraction_le_ennreal_norm_normalizedSphericalAverage
    (by omega : 0 < n + 1)
    (fun y : Euclidean (n + 1) => (Icc 0 δ).indicator (fun _ => (1 : ℝ)) ‖y‖)
    t x A hAmeas hint hnonneg hone
  -- the average agrees with the normalized one
  have hbridge : _root_.Spherical.sphericalAverage t
      (fun y : Euclidean (n + 1) => (Icc 0 δ).indicator (fun _ => (1 : ℂ)) ‖y‖) x =
      normalizedSphericalAverage (n + 1)
        (fun y : Euclidean (n + 1) =>
          (((Icc 0 δ).indicator (fun _ => (1 : ℝ)) ‖y‖ : ℝ) : ℂ)) t x := by
    rw [_root_.Auto.Spherical.PowerWeights.sphericalAverage_eq_normalizedSphericalAverage]
    congr 1
    funext y
    by_cases hmem : ‖y‖ ∈ Icc (0 : ℝ) δ
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      norm_num
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      norm_num
  rw [hbridge]
  refine le_trans ?_ hfrac
  calc
    ENNReal.ofReal (c * δ ^ n) =
        ENNReal.ofReal (c₀.toReal * (δ / 6) ^ n) /
          ENNReal.ofReal (surfaceMass (n + 1)) := by
      have hreal : c * δ ^ n = (c₀.toReal * (δ / 6) ^ n) / surfaceMass (n + 1) := by
        rw [hc, div_pow]
        field_simp
      rw [hreal, ENNReal.ofReal_div_of_pos hmass]
    _ ≤ c₀ * ENNReal.ofReal ((δ / 6) ^ n) /
          ENNReal.ofReal (surfaceMass (n + 1)) := by
      refine ENNReal.div_le_div_right ?_ _
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hc₀top]
    _ ≤ unitSurfaceMeasure (n + 1) A / ENNReal.ofReal (surfaceMass (n + 1)) :=
      ENNReal.div_le_div_right hcapbound _

/-- A constant lower bound for the maximal function on a measurable set gives
a lower bound for its `L^q` norm. -/
theorem le_eLpNorm_of_const_le_on {d : ℕ} {E : Set ℝ} {f : Euclidean d → ℂ}
    {S : Set (Euclidean d)} (hS : MeasurableSet S) {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x ∈ S, ENNReal.ofReal c ≤ M E f x) {q : ℝ} (hq : 0 < q) :
    ENNReal.ofReal c * volume S ^ (1 / q) ≤
      eLpNorm (M E f) (ENNReal.ofReal q) volume := by
  have hpoint : ∀ x : Euclidean d,
      ‖S.indicator (fun _ => (c : ℂ)) x‖ₑ ≤ ‖M E f x‖ₑ := by
    intro x
    by_cases hx : x ∈ S
    · calc
        ‖S.indicator (fun _ => (c : ℂ)) x‖ₑ = ENNReal.ofReal c := by
          rw [Set.indicator_of_mem hx]
          rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
        _ ≤ M E f x := hle x hx
    · rw [Set.indicator_of_notMem hx]
      simp
  have heq : eLpNorm (S.indicator (fun _ => (c : ℂ))) (ENNReal.ofReal q) volume =
      ENNReal.ofReal c * volume S ^ (1 / q) := by
    rw [eLpNorm_indicator_const hS
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [← heq]
  exact eLpNorm_mono_enorm hpoint

/-- The annuli attached to a `δ`-separated family of radii are pairwise
disjoint. -/
theorem pairwiseDisjoint_separated_annuli (d : ℕ) {δ : ℝ} (hδ : 0 < δ) {T : Finset ℝ}
    (hsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s|) :
    ((T : Set ℝ)).PairwiseDisjoint
      (fun t => radialAnnulusIcc d (t - δ / 4) (t + δ / 4)) := by
  intro t ht s hs hts
  rw [Function.onFun, Set.disjoint_left]
  intro x hxt hxs
  rw [radialAnnulusIcc, mem_setOf_eq, mem_Icc] at hxt hxs
  have hgap := hsep t ht s hs hts
  rcases le_total t s with h | h
  · rw [abs_of_nonpos (by linarith : t - s ≤ 0)] at hgap
    linarith [hxt.2, hxs.1]
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)] at hgap
    linarith [hxs.2, hxt.1]

/-- The union of the annuli attached to a `δ`-separated family of radii in
`[1,2]` has volume at least a constant times the cardinality times `δ`. -/
theorem volume_biUnion_separated_annuli_ge {d : ℕ} (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {T : Finset ℝ} (hT : ∀ t ∈ T, t ∈ Icc (1 : ℝ) 2)
    (hsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s|) :
    (T.card : ENNReal) *
        (ENNReal.ofReal ((3 / 4 : ℝ) ^ (d - 1) * (δ / 2)) *
          volume (Metric.ball (0 : Euclidean d) 1)) ≤
      volume (⋃ t ∈ T, radialAnnulusIcc d (t - δ / 4) (t + δ / 4)) := by
  have hterm : ∀ t ∈ T,
      ENNReal.ofReal ((3 / 4 : ℝ) ^ (d - 1) * (δ / 2)) *
          volume (Metric.ball (0 : Euclidean d) 1) ≤
        volume (radialAnnulusIcc d (t - δ / 4) (t + δ / 4)) := by
    intro t ht
    have htmem := hT t ht
    have hlow : (0 : ℝ) ≤ t - δ / 4 := by
      have := htmem.1
      linarith
    have hle : t - δ / 4 ≤ t + δ / 4 := by linarith
    rw [volume_radialAnnulusIcc hd hlow hle]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    have hpow := brrs_pow_sub_pow_ge hlow hle m
    have hbase : (3 / 4 : ℝ) ≤ t - δ / 4 := by
      have := htmem.1
      linarith
    have hmono : ((3 : ℝ) / 4) ^ m ≤ (t - δ / 4) ^ m :=
      pow_le_pow_left₀ (by norm_num) hbase m
    simp only [Nat.add_sub_cancel]
    nlinarith [hpow, hmono, hδ.le]
  calc
    (T.card : ENNReal) *
        (ENNReal.ofReal ((3 / 4 : ℝ) ^ (d - 1) * (δ / 2)) *
          volume (Metric.ball (0 : Euclidean d) 1)) =
        ∑ _t ∈ T, ENNReal.ofReal ((3 / 4 : ℝ) ^ (d - 1) * (δ / 2)) *
          volume (Metric.ball (0 : Euclidean d) 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ T, volume (radialAnnulusIcc d (t - δ / 4) (t + δ / 4)) :=
      Finset.sum_le_sum hterm
    _ = volume (⋃ t ∈ T, radialAnnulusIcc d (t - δ / 4) (t + δ / 4)) :=
      (measure_biUnion_finset (pairwiseDisjoint_separated_annuli d hδ hsep)
        (fun t _ => measurableSet_radialAnnulusIcc d _ _)).symm

set_option maxHeartbeats 1600000 in
/-- **BRS (3.2), Lemma 3.2(ii)**, in separated-set form: for every `δ`-separated
subset `T` of `E`, the radial operator norm is at least
`(card T)^{1/q} δ^{d-1+1/q-d/p}` up to a constant. -/
theorem le_eLpNorm_ratio_separated {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ T : Finset ℝ,
      (↑T : Set ℝ) ⊆ E → (∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s|) →
        ENNReal.ofReal (c * (T.card : ℝ) ^ (1 / q) *
              δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p)) *
            eLpNorm (fun y : Euclidean d => (Icc 0 δ).indicator (fun _ => (1 : ℂ)) ‖y‖)
              (ENNReal.ofReal p) volume ≤
          eLpNorm (M E (fun y : Euclidean d =>
            (Icc 0 δ).indicator (fun _ => (1 : ℂ)) ‖y‖)) (ENNReal.ofReal q) volume := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hpinv : (0 : ℝ) ≤ 1 / p := le_of_lt (div_pos one_pos hp)
  have hqinv : (0 : ℝ) ≤ 1 / q := le_of_lt (div_pos one_pos hq)
  obtain ⟨c0, hc0, hcap⟩ := le_sphericalAverage_ballProfile hd
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  have hVeq : volume (Metric.ball (0 : Euclidean d) 1) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hVtop]
  set c1 : ℝ := (3 / 4 : ℝ) ^ (d - 1) / 2 with hc1
  have hc1pos : 0 < c1 := by
    rw [hc1]
    have hbase : (0 : ℝ) < (3 / 4 : ℝ) ^ (d - 1) := pow_pos (by norm_num) _
    linarith
  refine ⟨c0 * (c1 * V) ^ (1 / q) / V ^ (1 / p),
    div_pos (mul_pos hc0 (Real.rpow_pos_of_pos (mul_pos hc1pos hVpos) _))
      (Real.rpow_pos_of_pos hVpos _), ?_⟩
  intro δ hδ hδ1 T hTE hsep
  have hcard : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  have hδd : (0 : ℝ) ≤ δ ^ d := pow_nonneg hδ.le d
  have hδd1 : (0 : ℝ) ≤ δ ^ (d - 1) := pow_nonneg hδ.le _
  set f : Euclidean d → ℂ :=
    fun y => (Icc 0 δ).indicator (fun _ => (1 : ℂ)) ‖y‖ with hf
  set S : Set (Euclidean d) :=
    ⋃ t ∈ T, radialAnnulusIcc d (t - δ / 4) (t + δ / 4) with hS
  have hSmeas : MeasurableSet S := by
    rw [hS]
    exact Finset.measurableSet_biUnion _ fun t _ => measurableSet_radialAnnulusIcc d _ _
  have hlarge : ∀ x ∈ S, ENNReal.ofReal (c0 * δ ^ (d - 1)) ≤ M E f x := by
    intro x hx
    have hx2 : ∃ t ∈ T, x ∈ radialAnnulusIcc d (t - δ / 4) (t + δ / 4) := by
      rw [hS] at hx
      simpa only [Set.mem_iUnion, exists_prop] using hx
    obtain ⟨t, htT, hxt⟩ := hx2
    have htE : t ∈ E := hTE htT
    have htIcc : t ∈ Icc (1 : ℝ) 2 := hE htE
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one htIcc.1
    have hclose : |‖x‖ - t| ≤ δ / 2 := by
      rw [radialAnnulusIcc, mem_setOf_eq, mem_Icc] at hxt
      rw [abs_le]
      constructor
      · linarith [hxt.1]
      · linarith [hxt.2]
    have havg := hcap t δ hδ hδ1 htIcc.1 htIcc.2 x hclose
    refine le_trans havg ?_
    unfold M _root_.Spherical.restrictedSphericalMaximal
    exact le_iSup_of_le t (le_iSup_of_le ⟨htE, htpos⟩ le_rfl)
  have hlow : ENNReal.ofReal (c0 * δ ^ (d - 1)) * volume S ^ (1 / q) ≤
      eLpNorm (M E f) (ENNReal.ofReal q) volume :=
    le_eLpNorm_of_const_le_on hSmeas (mul_nonneg hc0.le hδd1) hlarge hq
  have hvol : ENNReal.ofReal ((T.card : ℝ) * (c1 * δ) * V) ≤ volume S := by
    have hkey : ENNReal.ofReal ((T.card : ℝ) * (c1 * δ) * V) =
        (T.card : ENNReal) *
          (ENNReal.ofReal ((3 / 4 : ℝ) ^ (d - 1) * (δ / 2)) *
            ENNReal.ofReal V) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hcard (mul_nonneg hc1pos.le hδ.le)),
        ENNReal.ofReal_mul hcard, ENNReal.ofReal_natCast, mul_assoc]
      congr 2
      rw [hc1]
      ring
    rw [hkey, ← hVeq, hS]
    exact volume_biUnion_separated_annuli_ge hd hδ hδ1 (fun t ht => hE (hTE ht)) hsep
  have hnorm : eLpNorm f (ENNReal.ofReal p) volume =
      ENNReal.ofReal ((δ ^ d * V) ^ (1 / p)) := by
    rw [hf, eLpNorm_indicator_lift d 0 δ hp, radialAnnulusIcc_zero d hδ.le,
      volume_closedBall_eq hd hδ.le, hVeq, ← ENNReal.ofReal_mul hδd,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hδd hVpos.le) hpinv]
  have hreal : (c0 * (c1 * V) ^ (1 / q) / V ^ (1 / p)) * (T.card : ℝ) ^ (1 / q) *
        δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) * (δ ^ d * V) ^ (1 / p) ≤
      c0 * δ ^ (d - 1) * ((T.card : ℝ) * (c1 * δ) * V) ^ (1 / q) := by
    have hδpow : (δ : ℝ) ^ (d - 1) = δ ^ ((d : ℝ) - 1) := by
      rw [← Real.rpow_natCast δ (d - 1)]
      congr 1
      have h1 : (1 : ℕ) ≤ d := hd
      push_cast [Nat.cast_sub h1]
      ring
    have hsplitp : (δ ^ d * V) ^ (1 / p) = δ ^ ((d : ℝ) / p) * V ^ (1 / p) := by
      rw [Real.mul_rpow hδd hVpos.le, ← Real.rpow_natCast δ d,
        ← Real.rpow_mul hδ.le]
      congr 2
      ring
    have hsplitq : ((T.card : ℝ) * (c1 * δ) * V) ^ (1 / q) =
        (T.card : ℝ) ^ (1 / q) * δ ^ ((1 : ℝ) / q) * (c1 * V) ^ (1 / q) := by
      rw [show (T.card : ℝ) * (c1 * δ) * V = ((T.card : ℝ) * δ) * (c1 * V) by ring,
        Real.mul_rpow (mul_nonneg hcard hδ.le) (mul_nonneg hc1pos.le hVpos.le),
        Real.mul_rpow hcard hδ.le]
    rw [hδpow, hsplitp, hsplitq]
    have hcollect : δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) * δ ^ ((d : ℝ) / p) =
        δ ^ ((d : ℝ) - 1) * δ ^ ((1 : ℝ) / q) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 1
      ring
    have hVcancel : V ^ (1 / p) / V ^ (1 / p) = 1 :=
      div_self (ne_of_gt (Real.rpow_pos_of_pos hVpos _))
    calc
      c0 * (c1 * V) ^ (1 / q) / V ^ (1 / p) * (T.card : ℝ) ^ (1 / q) *
            δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) *
            (δ ^ ((d : ℝ) / p) * V ^ (1 / p)) =
          (c0 * (T.card : ℝ) ^ (1 / q) * (c1 * V) ^ (1 / q)) *
            (δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) * δ ^ ((d : ℝ) / p)) *
            (V ^ (1 / p) / V ^ (1 / p)) := by ring
      _ = c0 * δ ^ ((d : ℝ) - 1) *
            ((T.card : ℝ) ^ (1 / q) * δ ^ ((1 : ℝ) / q) * (c1 * V) ^ (1 / q)) := by
          rw [hcollect, hVcancel]
          ring
      _ ≤ c0 * δ ^ ((d : ℝ) - 1) *
            ((T.card : ℝ) ^ (1 / q) * δ ^ ((1 : ℝ) / q) * (c1 * V) ^ (1 / q)) := le_rfl
  have hAnn : (0 : ℝ) ≤ c0 * (c1 * V) ^ (1 / q) / V ^ (1 / p) *
      (T.card : ℝ) ^ (1 / q) * δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) :=
    mul_nonneg (mul_nonneg (le_of_lt
      (div_pos (mul_pos hc0 (Real.rpow_pos_of_pos (mul_pos hc1pos hVpos) _))
        (Real.rpow_pos_of_pos hVpos _))) (Real.rpow_nonneg hcard _))
      (Real.rpow_nonneg hδ.le _)
  calc
    ENNReal.ofReal (c0 * (c1 * V) ^ (1 / q) / V ^ (1 / p) * (T.card : ℝ) ^ (1 / q) *
          δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p)) *
        eLpNorm f (ENNReal.ofReal p) volume =
        ENNReal.ofReal ((c0 * (c1 * V) ^ (1 / q) / V ^ (1 / p)) *
          (T.card : ℝ) ^ (1 / q) * δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) *
            (δ ^ d * V) ^ (1 / p)) := by
      rw [hnorm, ← ENNReal.ofReal_mul hAnn]
    _ ≤ ENNReal.ofReal (c0 * δ ^ (d - 1) *
          ((T.card : ℝ) * (c1 * δ) * V) ^ (1 / q)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (c0 * δ ^ (d - 1)) *
          ENNReal.ofReal (((T.card : ℝ) * (c1 * δ) * V) ^ (1 / q)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hc0.le hδd1)]
    _ ≤ ENNReal.ofReal (c0 * δ ^ (d - 1)) * volume S ^ (1 / q) := by
      refine mul_le_mul' le_rfl ?_
      rw [← ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (mul_nonneg hcard (mul_nonneg hc1pos.le hδ.le)) hVpos.le) hqinv]
      exact ENNReal.rpow_le_rpow hvol hqinv
    _ ≤ _ := hlow

/-! ## Separated sets and covering numbers

A maximal `δ`-separated subset of `E` is in particular a `δ`-cover of `E`, so
its cardinality dominates the covering number at radius `δ`, hence the
entropy number at scale `2δ`. -/

/-- A maximal `δ`-separated subset of `E` covers `E` at radius `δ`. -/
theorem isCover_of_isMaximalSeparatedSubset {E : Set ℝ} {δ : ℝ≥0} (hδ : 0 < δ)
    {T : Finset ℝ} (hT : IsMaximalSeparatedSubset E (δ : ℝ) T) :
    Metric.IsCover δ E (↑T : Set ℝ) := by
  intro x hx
  have hδ' : (0 : ℝ) < (δ : ℝ) := hδ
  obtain ⟨t, htT, hlt⟩ :=
    IsMaximalSeparatedSubset.exists_mem_abs_sub_lt hT hδ' hx
  refine ⟨t, htT, ?_⟩
  show edist x t ≤ (δ : ℝ≥0∞)
  rw [edist_dist, Real.dist_eq]
  calc
    ENNReal.ofReal |x - t| ≤ ENNReal.ofReal (δ : ℝ) :=
      ENNReal.ofReal_le_ofReal hlt.le
    _ = (δ : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-- The covering number at radius `δ` is at most the cardinality of any
maximal `δ`-separated subset. -/
theorem externalCoveringNumber_le_card_of_isMaximalSeparatedSubset {E : Set ℝ}
    {δ : ℝ≥0} (hδ : 0 < δ) {T : Finset ℝ}
    (hT : IsMaximalSeparatedSubset E (δ : ℝ) T) :
    Metric.externalCoveringNumber δ E ≤ (T.card : ℕ∞) := by
  have hcover := isCover_of_isMaximalSeparatedSubset hδ hT
  calc
    Metric.externalCoveringNumber δ E ≤ (↑T : Set ℝ).encard := by
      exact iInf₂_le (↑T : Set ℝ) hcover
    _ = (T.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard T

/-- The BRS entropy number at scale `2δ` is at most the cardinality of any
maximal `δ`-separated subset. -/
theorem brrsEntropyNumber_le_card_of_isMaximalSeparatedSubset {E : Set ℝ}
    {δ : ℝ≥0} (hδ : 0 < δ) {T : Finset ℝ}
    (hT : IsMaximalSeparatedSubset E (δ : ℝ) T) :
    _root_.Auto.Spherical.LegendreAssouad.brrsEntropyNumber E (2 * δ) ≤
      (T.card : ℝ≥0∞) := by
  have hhalf : (2 * δ) / 2 = δ := by
    rw [mul_comm]
    field_simp
  rw [_root_.Auto.Spherical.LegendreAssouad.brrsEntropyNumber, hhalf]
  exact_mod_cast externalCoveringNumber_le_card_of_isMaximalSeparatedSubset hδ hT


/-! ## Covering numbers and the dimensional necessary condition -/

section CoveringNecessary

open Auto.FractalDimensions

/-- A maximal `δ`-separated subset of `E` gives an interval cover at scale
`2δ`, so it dominates the interval covering number there. -/
theorem intervalCoveringNumber_le_card_of_isMaximalSeparatedSubset {E : Set ℝ}
    {δ : ℝ} (hδ : 0 < δ) {T : Finset ℝ} (hT : IsMaximalSeparatedSubset E δ T) :
    intervalCoveringNumber E (2 * δ) ≤ T.card := by
  refine intervalCoveringNumber_le_card ?_
  intro x hx
  obtain ⟨t, htT, hlt⟩ := IsMaximalSeparatedSubset.exists_mem_abs_sub_lt hT hδ hx
  have h := abs_lt.mp hlt
  refine Set.mem_biUnion htT ?_
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩ <;> [linarith [h.2]; linarith [h.1]]

/-- Every `E ⊆ [1,2]` admits a maximal `δ`-separated finite subset. -/
theorem exists_isMaximalSeparatedSubset {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    {δ : ℝ} (hδ : 0 < δ) : ∃ T : Finset ℝ, IsMaximalSeparatedSubset E δ T := by
  obtain ⟨T, hT, -⟩ :=
    exists_isMaximalSeparatedSubset_superset_of_isSeparated (U := (∅ : Finset ℝ))
      hE hδ (by simp) (by intro s hs; simp at hs)
  exact ⟨T, hT⟩

/-- A nonempty set has positive interval covering number. -/
theorem intervalCoveringNumber_pos {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hEne : E.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    0 < intervalCoveringNumber E δ := by
  by_contra hcon
  push Not at hcon
  have hzero : intervalCoveringNumber E δ = 0 := Nat.le_zero.mp hcon
  obtain ⟨ι, hι, hcard⟩ :=
    exists_intervalCover_card_eq_intervalCoveringNumber hE hδ
  have hempty : ι = ∅ := Finset.card_eq_zero.mp (by rw [hcard, hzero])
  obtain ⟨x, hx⟩ := hEne
  have hmem := hι hx
  rw [hempty] at hmem
  simp at hmem

/-- The scalar form of (3.2) available under a radial `L^p -> L^q` bound:
the covering number of `E` at scale `2δ` obeys
`N(E,2δ)^{1/q} δ^{d-1+1/q-d/p} ≤ K` for all `0 < δ ≤ 1`. -/
theorem coveringNumber_test_bound_of_hasRadialStrongType {d : ℕ} (hd : 0 < d)
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : HasRadialStrongType d E (ENNReal.ofReal p) (ENNReal.ofReal q)) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ((intervalCoveringNumber E (2 * δ) : ℝ)) ^ (1 / q) *
          δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) ≤ K := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨C, hC, hbound⟩ := h
  obtain ⟨c, hc, h32⟩ := le_eLpNorm_ratio_separated hd hE hp hq
  refine ⟨C / c, div_pos hC hc, ?_⟩
  intro δ hδ hδ1
  obtain ⟨T, hT⟩ := exists_isMaximalSeparatedSubset hE hδ
  have hsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s| := by
    intro t ht s hs hts
    exact hT.2.1 (by simpa using ht) (by simpa using hs) hts
  set f : Euclidean d → ℂ :=
    fun y => (Icc 0 δ).indicator (fun _ => (1 : ℂ)) ‖y‖ with hf
  have hnormf : eLpNorm f (ENNReal.ofReal p) volume =
      volume (radialAnnulusIcc d 0 δ) ^ (1 / p) :=
    eLpNorm_indicator_lift d _ _ hp
  have hballvol : volume (radialAnnulusIcc d 0 δ) =
      volume (Metric.closedBall (0 : Euclidean d) δ) := by
    rw [radialAnnulusIcc_zero d hδ.le]
  have hvoltop : volume (radialAnnulusIcc d 0 δ) ≠ ⊤ := by
    rw [hballvol]; exact measure_closedBall_lt_top.ne
  have hvolpos : 0 < volume (radialAnnulusIcc d 0 δ) := by
    rw [hballvol]
    exact Metric.measure_closedBall_pos volume (0 : Euclidean d) hδ
  have hNpos : 0 < eLpNorm f (ENNReal.ofReal p) volume := by
    rw [hnormf]
    exact ENNReal.rpow_pos hvolpos hvoltop
  have hNtop : eLpNorm f (ENNReal.ofReal p) volume ≠ ⊤ := by
    rw [hnormf]
    exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) hvoltop).ne
  have hmem : MemLp f (ENNReal.ofReal p) volume := by
    refine ⟨(measurable_indicator_lift d _ _).aestronglyMeasurable, ?_⟩
    rw [hnormf]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hvoltop
  have hrad := isNormRadial_indicator_lift d 0 δ
  have hchain :
      ENNReal.ofReal (c * (T.card : ℝ) ^ (1 / q) *
            δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p)) *
          eLpNorm f (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume :=
    le_trans (h32 δ hδ hδ1 T hT.1 hsep) ((hbound f hmem hrad).2)
  rw [mul_comm _ (eLpNorm f (ENNReal.ofReal p) volume),
    mul_comm _ (eLpNorm f (ENNReal.ofReal p) volume)] at hchain
  have hcancel : ENNReal.ofReal (c * (T.card : ℝ) ^ (1 / q) *
      δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p)) ≤ ENNReal.ofReal C :=
    (ENNReal.mul_le_mul_iff_right hNpos.ne' hNtop).mp hchain
  have hreal := (ENNReal.ofReal_le_ofReal_iff hC.le).mp hcancel
  -- pass from the separated set to the covering number
  have hcov : (intervalCoveringNumber E (2 * δ) : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast intervalCoveringNumber_le_card_of_isMaximalSeparatedSubset hδ hT
  have hmono : ((intervalCoveringNumber E (2 * δ) : ℝ)) ^ (1 / q) ≤
      (T.card : ℝ) ^ (1 / q) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcov (by positivity)
  have hδpow : (0 : ℝ) < δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) :=
    Real.rpow_pos_of_pos hδ _
  rw [le_div_iff₀ hc]
  calc
    ((intervalCoveringNumber E (2 * δ) : ℝ)) ^ (1 / q) *
          δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) * c
        ≤ (T.card : ℝ) ^ (1 / q) * δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) * c := by
      have := mul_le_mul_of_nonneg_right hmono hδpow.le
      exact mul_le_mul_of_nonneg_right this hc.le
    _ = c * (T.card : ℝ) ^ (1 / q) * δ ^ ((d : ℝ) - 1 + 1 / q - (d : ℝ) / p) := by
      ring
    _ ≤ C := hreal

/-- **The dimensional necessary condition of BRS Lemma 3.2(ii).**  A radial
`L^p -> L^q` bound for the spherical maximal operator with dilations in a
nonempty `E ⊆ [1,2]` of upper Minkowski dimension `β` forces
`(1-β)/q + d - 1 - d/p ≥ 0`. -/
theorem dim_le_of_hasRadialStrongType {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {β : ℝ}
    (hβ : upperMinkowskiDimension E = β) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : HasRadialStrongType d E (ENNReal.ofReal p) (ENNReal.ofReal q)) :
    0 ≤ (1 - β) / q + (d : ℝ) - 1 - (d : ℝ) / p := by
  have hqne : q ≠ 0 := hq.ne'
  have hpne : p ≠ 0 := hp.ne'
  set B : ℝ := (d : ℝ) - 1 + 1 / q - (d : ℝ) / p with hBdef
  obtain ⟨K, hK, hbound⟩ :=
    coveringNumber_test_bound_of_hasRadialStrongType hd hE hp hq h
  have hβ0 : 0 ≤ β := hβ ▸ upperMinkowskiDimension_nonneg_of_subset_Icc hE
  by_contra hcon
  push Not at hcon
  have hEq : (1 - β) / q + (d : ℝ) - 1 - (d : ℝ) / p = B - β / q := by
    rw [hBdef]
    field_simp
    ring
  have h2 : B < β / q := by
    rw [hEq] at hcon
    linarith
  have hqB : q * B < β := by
    rw [lt_div_iff₀ hq] at h2
    calc q * B = B * q := mul_comm _ _
      _ < β := h2
  rcases lt_or_ge B 0 with hB | hB
  · -- the covering number is at least one, and `δ ^ B` is unbounded
    set δ : ℝ := (K + 1) ^ (1 / B) with hδdef
    have hδpos : 0 < δ := Real.rpow_pos_of_pos (by linarith) _
    have hδle : δ ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
        (le_of_lt (div_neg_of_pos_of_neg one_pos hB))
    have hδB : δ ^ B = K + 1 := by
      rw [hδdef, ← Real.rpow_mul (by linarith), one_div_mul_cancel hB.ne,
        Real.rpow_one]
    have hone : (1 : ℝ) ≤ ((intervalCoveringNumber E (2 * δ) : ℝ)) ^ (1 / q) := by
      have hNpos : 0 < intervalCoveringNumber E (2 * δ) :=
        intervalCoveringNumber_pos hE hEne (by linarith)
      have hN1 : (1 : ℝ) ≤ (intervalCoveringNumber E (2 * δ) : ℝ) := by
        exact_mod_cast hNpos
      calc (1 : ℝ) = (1 : ℝ) ^ (1 / q) := (Real.one_rpow _).symm
        _ ≤ _ := Real.rpow_le_rpow zero_le_one hN1 (by positivity)
    have hb := hbound δ hδpos hδle
    rw [hδB] at hb
    nlinarith [hb, hone, hK]
  · -- the dimension witness beats the bound at small scales
    have hα0 : 0 ≤ q * B := mul_nonneg hq.le hB
    obtain ⟨ε, hε, hwit⟩ :=
      exists_upperMinkowski_coveringNumber_lower_witness_at_small_scale hE hβ hα0 hqB
    have hεne : ε ≠ 0 := hε.ne'
    have h2B : (0 : ℝ) < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) _
    set M : ℝ := K * (2 : ℝ) ^ B with hM
    have hMpos : 0 < M := by
      rw [hM]; exact mul_pos hK h2B
    set δ₀ : ℝ := M ^ (-(q / ε)) with hδ₀
    have hδ₀pos : 0 < δ₀ := Real.rpow_pos_of_pos hMpos _
    obtain ⟨δ, hδpos, hδlt₀, hδlt1, hwitδ⟩ := hwit 1 one_pos δ₀ hδ₀pos
    have hb := hbound (δ / 2) (by positivity) (by linarith)
    rw [show 2 * (δ / 2) = δ by ring] at hb
    have hδrp : (0 : ℝ) < δ ^ (-(q * B + ε)) := Real.rpow_pos_of_pos hδpos _
    have hNlow : δ ^ (-(q * B + ε) / q) ≤
        ((intervalCoveringNumber E δ : ℝ)) ^ (1 / q) := by
      have h1 : δ ^ (-(q * B + ε)) ≤ (intervalCoveringNumber E δ : ℝ) := by
        have h1' := hwitδ
        rw [one_mul] at h1'
        exact h1'.le
      calc δ ^ (-(q * B + ε) / q)
          = (δ ^ (-(q * B + ε))) ^ (1 / q) := by
            rw [← Real.rpow_mul hδpos.le]
            congr 1
            field_simp
        _ ≤ _ := Real.rpow_le_rpow hδrp.le h1 (by positivity)
    have hhalf : (δ / 2) ^ B = δ ^ B / (2 : ℝ) ^ B :=
      Real.div_rpow hδpos.le (by norm_num : (0:ℝ) ≤ 2) B
    rw [hhalf] at hb
    have hcomb : δ ^ (-(q * B + ε) / q) * δ ^ B = δ ^ (-(ε / q)) := by
      rw [← Real.rpow_add hδpos]
      congr 1
      field_simp
      ring
    have hstep : δ ^ (-(ε / q)) / (2 : ℝ) ^ B ≤ K := by
      calc δ ^ (-(ε / q)) / (2 : ℝ) ^ B
          = (δ ^ (-(q * B + ε) / q) * δ ^ B) / (2 : ℝ) ^ B := by rw [hcomb]
        _ = δ ^ (-(q * B + ε) / q) * (δ ^ B / (2 : ℝ) ^ B) := by ring
        _ ≤ ((intervalCoveringNumber E δ : ℝ)) ^ (1 / q) *
              (δ ^ B / (2 : ℝ) ^ B) :=
            mul_le_mul_of_nonneg_right hNlow (by positivity)
        _ ≤ K := hb
    have hneg : -(ε / q) < 0 := by
      have hpos : 0 < ε / q := div_pos hε hq
      linarith
    have hδ₀eq : δ₀ ^ (-(ε / q)) = M := by
      rw [hδ₀, ← Real.rpow_mul hMpos.le,
        show -(q / ε) * -(ε / q) = 1 by field_simp, Real.rpow_one]
    have hbig : M < δ ^ (-(ε / q)) := by
      have h1 : δ₀ ^ (-(ε / q)) < δ ^ (-(ε / q)) :=
        Real.rpow_lt_rpow_of_neg hδpos hδlt₀ hneg
      rw [hδ₀eq] at h1
      exact h1
    rw [div_le_iff₀ h2B] at hstep
    rw [hM] at hbig
    linarith

end CoveringNecessary


/-! ## The exponent triangle and the endpoint exclusions -/

/-- A convex combination of three points lies in their convex hull. -/
theorem mem_convexHull_triple {A B C P : ℝ × ℝ} {s t u : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hsum : s + t + u = 1)
    (hP : P = s • A + t • B + u • C) :
    P ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)) := by
  have hA : A ∈ ({A, B, C} : Set (ℝ × ℝ)) := by simp
  have hB : B ∈ ({A, B, C} : Set (ℝ × ℝ)) := by simp
  have hC : C ∈ ({A, B, C} : Set (ℝ × ℝ)) := by simp
  have key := (convex_convexHull ℝ ({A, B, C} : Set (ℝ × ℝ))).sum_mem
    (t := (Finset.univ : Finset (Fin 3))) (w := ![s, t, u]) (z := ![A, B, C])
    (by
      intro i _
      fin_cases i <;> simpa using ‹_›)
    (by
      rw [Fin.sum_univ_three]
      simpa using hsum)
    (by
      intro i _
      fin_cases i
      · simpa using subset_convexHull ℝ _ hA
      · simpa using subset_convexHull ℝ _ hB
      · simpa using subset_convexHull ℝ _ hC)
  rw [Fin.sum_univ_three] at key
  simpa [hP] using key

/-- The triangle `Δ_β` contains every point of the reciprocal-exponent plane
satisfying the three necessary conditions of BRS §3. -/
theorem mem_Delta_of_conditions {d : ℕ} (hd : 2 ≤ d) {β : ℝ} (hβ0 : 0 ≤ β)
    {x y : ℝ} (hyx : y ≤ x) (hxy : x ≤ (d : ℝ) * y)
    (hc : 0 ≤ (1 - β) * y + ((d : ℝ) - 1) - (d : ℝ) * x) :
    (x, y) ∈ Delta d β := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd1pos : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) < (d : ℝ) - 1 + β := by linarith
  have hB : (0 : ℝ) < (d : ℝ) ^ 2 - 1 + β := by nlinarith
  set s : ℝ := ((d : ℝ) * y - x) * ((d : ℝ) - 1 + β) / ((d : ℝ) - 1) ^ 2 with hsdef
  set t : ℝ := (x - y) * ((d : ℝ) ^ 2 - 1 + β) / ((d : ℝ) - 1) ^ 2 with htdef
  have hs : 0 ≤ s := by
    rw [hsdef]
    have : (0 : ℝ) ≤ (d : ℝ) * y - x := by linarith
    positivity
  have ht : 0 ≤ t := by
    rw [htdef]
    have : (0 : ℝ) ≤ x - y := by linarith
    positivity
  have hsum : s + t = ((d : ℝ) * x - (1 - β) * y) / ((d : ℝ) - 1) := by
    rw [hsdef, htdef]
    field_simp
    ring
  have hu : 0 ≤ 1 - s - t := by
    rw [sub_sub, hsum, sub_nonneg, div_le_one hd1pos]
    linarith
  refine mem_convexHull_triple hu hs ht (by ring) ?_
  have hx : s * (((d : ℝ) - 1) / ((d : ℝ) - 1 + β)) +
      t * ((d : ℝ) * ((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1 + β)) = x := by
    rw [hsdef, htdef]
    field_simp
    ring
  have hy : s * (((d : ℝ) - 1) / ((d : ℝ) - 1 + β)) +
      t * (((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1 + β)) = y := by
    rw [hsdef, htdef]
    field_simp
    ring
  simp only [Q1, Q2, P3rad, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_zero,
    zero_add]
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [← hx]
  · rw [← hy]

/-- Where the maximal function is at least one on a set of positive measure,
its `L^∞` norm is at least one. -/
theorem le_eLpNorm_top_of_one_le_on {d : ℕ} {E : Set ℝ} {f : Euclidean d → ℂ}
    {S : Set (Euclidean d)} (hS : volume S ≠ 0)
    (hone : ∀ x ∈ S, (1 : ENNReal) ≤ M E f x) :
    1 ≤ eLpNorm (M E f) ⊤ volume := by
  have hpoint : ∀ x : Euclidean d,
      ‖S.indicator (fun _ => (1 : ℂ)) x‖ₑ ≤ ‖M E f x‖ₑ := by
    intro x
    by_cases hx : x ∈ S
    · calc
        ‖S.indicator (fun _ => (1 : ℂ)) x‖ₑ = 1 := by
          rw [Set.indicator_of_mem hx]
          simp
        _ ≤ M E f x := hone x hx
    · rw [Set.indicator_of_notMem hx]
      simp
  have h := eLpNorm_mono_enorm (p := ⊤) (μ := (volume : Measure (Euclidean d))) hpoint
  rwa [eLpNorm_exponent_top, eLpNormEssSup_indicator_const_eq S (1 : ℂ) hS,
    enorm_one] at h

/-- There is no radial `L^p → L^∞` bound for a nonempty set of dilations:
the thin shell test function has small `L^p` norm but its maximal function is
at least one on a ball. -/
theorem not_hasRadialStrongType_top_right {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p : ℝ} (hp : 0 < p)
    (h : HasRadialStrongType d E (ENNReal.ofReal p) ⊤) : False := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨C, hC, hbound⟩ := h
  obtain ⟨t₀, ht₀E⟩ := hEne
  have ht₀ : t₀ ∈ Icc (1 : ℝ) 2 := hE ht₀E
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  have hVeq : volume (Metric.ball (0 : Euclidean d) 1) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hVtop]
  set W : ℝ := 2 * d * 3 ^ (d - 1) * V with hW
  have hWpos : 0 < W := by
    rw [hW]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  set δ : ℝ := min 1 ((1 / C) ^ p / (2 * W)) with hδdef
  have hCp : (0 : ℝ) < (1 / C) ^ p := Real.rpow_pos_of_pos (by positivity) p
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδle : δ ≤ 1 := min_le_left _ _
  -- the test function
  set f : Euclidean d → ℂ := fun y =>
    (Icc (t₀ - δ) (t₀ + δ)).indicator (fun _ => (1 : ℂ)) ‖y‖ with hf
  have hannvol : volume (radialAnnulusIcc d (t₀ - δ) (t₀ + δ)) ≤
      ENNReal.ofReal (W * δ) := by
    refine le_trans (volume_thin_shell_le hd ht₀.1 ht₀.2 hδpos hδle) (le_of_eq ?_)
    rw [hVeq, ← ENNReal.ofReal_mul (by positivity), hW]
    congr 1
    ring
  have hnormf : eLpNorm f (ENNReal.ofReal p) volume =
      volume (radialAnnulusIcc d (t₀ - δ) (t₀ + δ)) ^ (1 / p) :=
    eLpNorm_indicator_lift d _ _ hp
  have hmem : MemLp f (ENNReal.ofReal p) volume := by
    refine ⟨(measurable_indicator_lift d _ _).aestronglyMeasurable, ?_⟩
    rw [hnormf]
    refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
    exact (lt_of_le_of_lt hannvol ENNReal.ofReal_lt_top).ne
  have hrad := isNormRadial_indicator_lift d (t₀ - δ) (t₀ + δ)
  have hone : ∀ x ∈ Metric.closedBall (0 : Euclidean d) δ, (1 : ENNReal) ≤ M E f x := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have havg : _root_.Spherical.sphericalAverage t₀ f x = 1 :=
      sphericalAverage_shell_eq_one hd (le_trans zero_le_one ht₀.1) hx
    unfold M _root_.Spherical.restrictedSphericalMaximal
    refine le_iSup_of_le t₀ (le_iSup_of_le ⟨ht₀E, lt_of_lt_of_le zero_lt_one ht₀.1⟩ ?_)
    rw [havg]
    simp
  have hballpos : volume (Metric.closedBall (0 : Euclidean d) δ) ≠ 0 :=
    (Metric.measure_closedBall_pos volume (0 : Euclidean d) hδpos).ne'
  have hlow : (1 : ENNReal) ≤ eLpNorm (M E f) ⊤ volume :=
    le_eLpNorm_top_of_one_le_on hballpos hone
  have hup : eLpNorm f (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((W * δ) ^ (1 / p)) := by
    rw [hnormf, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    exact ENNReal.rpow_le_rpow hannvol (by positivity)
  have hchain : (1 : ENNReal) ≤ ENNReal.ofReal (C * (W * δ) ^ (1 / p)) := by
    calc (1 : ENNReal) ≤ eLpNorm (M E f) ⊤ volume := hlow
      _ ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume :=
          (hbound f hmem hrad).2
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((W * δ) ^ (1 / p)) :=
          mul_le_mul' le_rfl hup
      _ = ENNReal.ofReal (C * (W * δ) ^ (1 / p)) := by
          rw [← ENNReal.ofReal_mul hC.le]
  have hreal : (1 : ℝ) ≤ C * (W * δ) ^ (1 / p) := by
    have := ENNReal.one_le_ofReal.mp hchain
    exact this
  -- but the small scale makes the right-hand side less than one
  have hWδ : W * δ < (1 / C) ^ p := by
    have h1 : W * δ ≤ W * ((1 / C) ^ p / (2 * W)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hWpos.le
    have h2 : W * ((1 / C) ^ p / (2 * W)) = (1 / C) ^ p / 2 := by
      field_simp
    rw [h2] at h1
    linarith
  have hsmall : C * (W * δ) ^ (1 / p) < 1 := by
    have h1 : (W * δ) ^ (1 / p) < ((1 / C) ^ p) ^ (1 / p) :=
      Real.rpow_lt_rpow (by positivity) hWδ (by positivity)
    have h2 : ((1 / C) ^ p) ^ (1 / p) = 1 / C := by
      rw [← Real.rpow_mul (by positivity), mul_one_div, div_self hp.ne',
        Real.rpow_one]
    rw [h2] at h1
    calc C * (W * δ) ^ (1 / p) < C * (1 / C) := by
          exact mul_lt_mul_of_pos_left h1 hC
      _ = 1 := by field_simp
  linarith

/-- There is no radial `L^∞ → L^q` bound for finite `q`: the indicator of a
large ball is bounded, but its maximal function is at least one on a ball of
comparable radius, whose volume is unbounded. -/
theorem not_hasRadialStrongType_top_left {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {q : ℝ} (hq : 0 < q)
    (h : HasRadialStrongType d E ⊤ (ENNReal.ofReal q)) : False := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨C, hC, hbound⟩ := h
  obtain ⟨t₀, ht₀E⟩ := hEne
  have ht₀ : t₀ ∈ Icc (1 : ℝ) 2 := hE ht₀E
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  have hVeq : volume (Metric.ball (0 : Euclidean d) 1) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hVtop]
  have hCq : (0 : ℝ) < C ^ q := Real.rpow_pos_of_pos hC q
  set R : ℝ := C ^ q / V + 1 with hR
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hR]
    have : (0 : ℝ) ≤ C ^ q / V := by positivity
    linarith
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  set f : Euclidean d → ℂ := fun y =>
    (Icc (t₀ - R) (t₀ + R)).indicator (fun _ => (1 : ℂ)) ‖y‖ with hf
  have hnormle : eLpNorm f ⊤ volume ≤ 1 := by
    rw [hf, eLpNorm_exponent_top, indicator_lift_eq]
    simpa using
      eLpNormEssSup_indicator_const_le (μ := (volume : Measure (Euclidean d)))
        (radialAnnulusIcc d (t₀ - R) (t₀ + R)) (1 : ℂ)
  have hmem : MemLp f ⊤ volume := by
    refine ⟨(measurable_indicator_lift d _ _).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt hnormle ENNReal.one_lt_top
  have hrad := isNormRadial_indicator_lift d (t₀ - R) (t₀ + R)
  have hone : ∀ x ∈ Metric.closedBall (0 : Euclidean d) R, (1 : ENNReal) ≤ M E f x := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have havg : _root_.Spherical.sphericalAverage t₀ f x = 1 :=
      sphericalAverage_shell_eq_one hd (le_trans zero_le_one ht₀.1) hx
    unfold M _root_.Spherical.restrictedSphericalMaximal
    refine le_iSup_of_le t₀ (le_iSup_of_le ⟨ht₀E, lt_of_lt_of_le zero_lt_one ht₀.1⟩ ?_)
    rw [havg]
    simp
  have hlow := le_eLpNorm_of_one_le_on (E := E) (f := f)
    (S := Metric.closedBall (0 : Euclidean d) R) measurableSet_closedBall hone hq
  have hvol : volume (Metric.closedBall (0 : Euclidean d) R) =
      ENNReal.ofReal (R ^ d * V) := by
    rw [volume_closedBall_eq hd hRpos.le, hVeq, ← ENNReal.ofReal_mul (by positivity)]
  have hchain : ENNReal.ofReal ((R ^ d * V) ^ (1 / q)) ≤ ENNReal.ofReal C := by
    calc ENNReal.ofReal ((R ^ d * V) ^ (1 / q))
        = volume (Metric.closedBall (0 : Euclidean d) R) ^ (1 / q) := by
          rw [hvol, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      _ ≤ eLpNorm (M E f) (ENNReal.ofReal q) volume := hlow
      _ ≤ ENNReal.ofReal C * eLpNorm f ⊤ volume := (hbound f hmem hrad).2
      _ ≤ ENNReal.ofReal C * 1 := mul_le_mul' le_rfl hnormle
      _ = ENNReal.ofReal C := mul_one _
  have hreal := (ENNReal.ofReal_le_ofReal_iff hC.le).mp hchain
  have hRd : R ≤ R ^ d := by
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ d := pow_le_pow_right₀ hR1 (by omega)
  have h1 : R * V ≤ R ^ d * V := mul_le_mul_of_nonneg_right hRd hVpos.le
  have h2 : (R * V) ^ (1 / q) ≤ C :=
    le_trans (Real.rpow_le_rpow (by positivity) h1 (by positivity)) hreal
  have h3 : R * V ≤ C ^ q := by
    have h4 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) (1 / q)) h2 hq.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hq.ne', Real.rpow_one] at h4
  rw [hR] at h3
  have h5 : C ^ q + V ≤ C ^ q := by
    calc C ^ q + V = (C ^ q / V + 1) * V := by field_simp
      _ ≤ C ^ q := h3
  linarith


/-! ## Corollary 3.3 -/

section Corollary33

open Auto.FractalDimensions

/-- **BRS Corollary 3.3.**  The radial type set of a nonempty compact set of
dilations `E ⊆ [1,2]` of upper Minkowski dimension `β` is contained in the
closed triangle `Δ_β`. -/
theorem radialTypeSet_subset_Delta {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {β : ℝ}
    (hβ : upperMinkowskiDimension E = β) :
    radialTypeSet d E ⊆ Delta d β := by
  have hd0 : 0 < d := lt_of_lt_of_le two_pos hd
  have hβ0 : 0 ≤ β := hβ ▸ upperMinkowskiDimension_nonneg_of_subset_Icc hE
  intro z hz
  obtain ⟨p, q, hp1, hq1, hzeq, hstrong⟩ := hz
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq1).ne'
  by_cases hptop : p = ⊤
  · by_cases hqtop : q = ⊤
    · have hQ1 : Q1 ∈ Delta d β := subset_convexHull ℝ _ (by simp)
      rw [hzeq, hptop, hqtop]
      simpa [Q1] using hQ1
    · exfalso
      have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
      refine not_hasRadialStrongType_top_left hd0 hE hEne hqpos ?_
      rw [ENNReal.ofReal_toReal hqtop, ← hptop]
      exact hstrong
  · by_cases hqtop : q = ⊤
    · exfalso
      have hppos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
      refine not_hasRadialStrongType_top_right hd0 hE hEne hppos ?_
      rw [ENNReal.ofReal_toReal hptop, ← hqtop]
      exact hstrong
    · have hppos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
      have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
      have hs' : HasRadialStrongType d E (ENNReal.ofReal p.toReal)
          (ENNReal.ofReal q.toReal) := by
        rw [ENNReal.ofReal_toReal hptop, ENNReal.ofReal_toReal hqtop]
        exact hstrong
      have h1 : p.toReal ≤ q.toReal :=
        le_of_hasRadialStrongType hd0 hE hEne hppos hqpos hs'
      have h2 : q.toReal ≤ p.toReal * d :=
        le_mul_of_hasRadialStrongType hd0 hE hEne hppos hqpos hs'
      have h3 : 0 ≤ (1 - β) / q.toReal + (d : ℝ) - 1 - (d : ℝ) / p.toReal :=
        dim_le_of_hasRadialStrongType hd0 hE hEne hβ hppos hqpos hs'
      have hzz : z = (1 / p.toReal, 1 / q.toReal) := by
        rw [hzeq, ENNReal.toReal_inv, ENNReal.toReal_inv, inv_eq_one_div,
          inv_eq_one_div]
      rw [hzz]
      refine mem_Delta_of_conditions hd hβ0 ?_ ?_ ?_
      · exact one_div_le_one_div_of_le hppos h1
      · rw [mul_one_div, div_le_div_iff₀ hppos hqpos, one_mul,
          mul_comm ((d : ℝ)) p.toReal]
        exact h2
      · rw [div_eq_mul_one_div (1 - β), div_eq_mul_one_div ((d : ℝ))] at h3
        linarith

end Corollary33

/-! ## The Stein-type test function of Lemma 3.4 -/

/-- The lower endpoint `δ^{1/2}` of the support of the Stein profile. -/
def steinLower (δ : ℝ) : ℝ := δ ^ (1 / 2 : ℝ)

/-- The upper endpoint `δ^{1/4}` of the support of the Stein profile. -/
def steinUpper (δ : ℝ) : ℝ := δ ^ (1 / 4 : ℝ)

/-- The profile `s^{1-d} (log(1/s))^{(1-d)/d}` of the Stein test function of
BRS Lemma 3.4, cut off to the radii `δ^{1/2} ≤ s ≤ δ^{1/4}`. -/
def steinProfile (d : ℕ) (δ : ℝ) : ℝ → ℂ :=
  (Icc (steinLower δ) (steinUpper δ)).indicator
    (fun s => ((s ^ (1 - (d : ℝ)) *
      Real.log (1 / s) ^ ((1 - (d : ℝ)) / (d : ℝ)) : ℝ) : ℂ))

theorem steinLower_pos {δ : ℝ} (hδ : 0 < δ) : 0 < steinLower δ :=
  Real.rpow_pos_of_pos hδ _

theorem steinUpper_pos {δ : ℝ} (hδ : 0 < δ) : 0 < steinUpper δ :=
  Real.rpow_pos_of_pos hδ _

theorem steinLower_lt_steinUpper {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    steinLower δ < steinUpper δ :=
  Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by norm_num)

theorem steinUpper_lt_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : steinUpper δ < 1 :=
  Real.rpow_lt_one hδ.le hδ1 (by norm_num)

theorem measurable_steinProfile (d : ℕ) (δ : ℝ) : Measurable (steinProfile d δ) := by
  refine Measurable.indicator ?_ measurableSet_Icc
  have h1 : Measurable fun s : ℝ => s ^ (1 - (d : ℝ)) := by fun_prop
  have h2 : Measurable fun s : ℝ =>
      Real.log (1 / s) ^ ((1 - (d : ℝ)) / (d : ℝ)) := by fun_prop
  exact Complex.measurable_ofReal.comp (h1.mul h2)

/-- The pointwise algebra behind the normalization `‖g‖_{p_d} ≲ 1`: with
`p_d = d/(d-1)` the weighted `p_d`-th power of the profile is `1/(s log(1/s))`. -/
theorem stein_integrand_eq {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    s ^ (d - 1) * (s ^ (1 - (d : ℝ)) *
        Real.log (1 / s) ^ ((1 - (d : ℝ)) / (d : ℝ))) ^ ((d : ℝ) / ((d : ℝ) - 1))
      = s⁻¹ * (Real.log (1 / s))⁻¹ := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hne : (d : ℝ) - 1 ≠ 0 := ne_of_gt hd1
  have hdne : (d : ℝ) ≠ 0 := by positivity
  have hlog : 0 < Real.log (1 / s) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hs]
    linarith
  have hpow : s ^ (d - 1) = s ^ ((d : ℝ) - 1) := by
    rw [← Real.rpow_natCast s (d - 1)]
    have h1 : (1 : ℕ) ≤ d := le_trans (by norm_num) hd
    congr 1
    push_cast [Nat.cast_sub h1]
    ring
  have hA : (s ^ (1 - (d : ℝ))) ^ ((d : ℝ) / ((d : ℝ) - 1)) = s ^ (-(d : ℝ)) := by
    rw [← Real.rpow_mul hs.le]
    congr 1
    field_simp
    ring
  have hB : (Real.log (1 / s) ^ ((1 - (d : ℝ)) / (d : ℝ))) ^ ((d : ℝ) / ((d : ℝ) - 1))
      = Real.log (1 / s) ^ (-1 : ℝ) := by
    rw [← Real.rpow_mul hlog.le]
    congr 1
    field_simp
    ring
  calc s ^ (d - 1) * (s ^ (1 - (d : ℝ)) *
        Real.log (1 / s) ^ ((1 - (d : ℝ)) / (d : ℝ))) ^ ((d : ℝ) / ((d : ℝ) - 1))
      = s ^ ((d : ℝ) - 1) * (s ^ (-(d : ℝ)) * Real.log (1 / s) ^ (-1 : ℝ)) := by
        rw [hpow, Real.mul_rpow (Real.rpow_nonneg hs.le _)
          (Real.rpow_nonneg hlog.le _), hA, hB]
    _ = (s ^ ((d : ℝ) - 1) * s ^ (-(d : ℝ))) * Real.log (1 / s) ^ (-1 : ℝ) := by ring
    _ = s ^ (-1 : ℝ) * Real.log (1 / s) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hs]
        congr 2
        ring
    _ = s⁻¹ * (Real.log (1 / s))⁻¹ := by
        rw [Real.rpow_neg_one, Real.rpow_neg_one]

/-- The normalization of the Stein test profile: its weighted `p_d`-th power
integrates to at most one, uniformly in `δ`. -/
theorem lintegral_steinProfile_le {d : ℕ} (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    (∫⁻ r : Ioi (0 : ℝ), (ENNReal.ofReal ‖steinProfile d δ r.1‖) ^
        ((d : ℝ) / ((d : ℝ) - 1)) ∂Measure.volumeIoiPow (d - 1)) ≤ 1 := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  set p : ℝ := (d : ℝ) / ((d : ℝ) - 1) with hp
  have hppos : 0 < p := by rw [hp]; positivity
  set L : ℝ := Real.log (1 / δ) with hL
  have hLpos : 0 < L := by
    rw [hL]
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hδ]
    linarith
  set a : ℝ := steinLower δ with ha
  set b : ℝ := steinUpper δ with hb
  have hapos : 0 < a := steinLower_pos hδ
  have hbpos : 0 < b := steinUpper_pos hδ
  have hab : a < b := steinLower_lt_steinUpper hδ hδ1
  have hb1 : b < 1 := steinUpper_lt_one hδ hδ1
  have hLeq : L = -Real.log δ := by
    rw [hL, one_div, Real.log_inv]
  have hlogb : Real.log (1 / b) = L / 4 := by
    rw [hb, steinUpper, one_div, ← Real.rpow_neg hδ.le, Real.log_rpow hδ, hLeq]
    ring
  -- the pointwise bound
  have hmono : ∀ r : ℝ, ENNReal.ofReal r ^ (d - 1) *
      (ENNReal.ofReal ‖steinProfile d δ r‖) ^ p ≤
        (Icc a b).indicator (fun r : ℝ => ENNReal.ofReal (4 / L * r⁻¹)) r := by
    intro r
    by_cases hr : r ∈ Icc a b
    · have hrpos : 0 < r := lt_of_lt_of_le hapos hr.1
      have hr1 : r < 1 := lt_of_le_of_lt hr.2 hb1
      have hlogr : 0 < Real.log (1 / r) := by
        refine Real.log_pos ?_
        rw [lt_div_iff₀ hrpos]
        linarith
      have hval : ‖steinProfile d δ r‖ =
          r ^ (1 - (d : ℝ)) * Real.log (1 / r) ^ ((1 - (d : ℝ)) / (d : ℝ)) := by
        rw [steinProfile, ← ha, ← hb, Set.indicator_of_mem hr, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      have hlow : L / 4 ≤ Real.log (1 / r) := by
        rw [← hlogb, one_div, one_div, Real.log_inv, Real.log_inv, neg_le_neg_iff]
        exact Real.log_le_log hrpos hr.2
      have hinvle : (Real.log (1 / r))⁻¹ ≤ 4 / L := by
        rw [inv_le_comm₀ hlogr (by positivity)]
        calc (4 / L)⁻¹ = L / 4 := by rw [inv_div]
          _ ≤ Real.log (1 / r) := hlow
      rw [Set.indicator_of_mem hr, hval,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hppos.le,
        ← ENNReal.ofReal_pow hrpos.le, ← ENNReal.ofReal_mul (by positivity), hp,
        stein_integrand_eq hd hrpos hr1]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_comm (4 / L) r⁻¹]
      exact mul_le_mul_of_nonneg_left hinvle (by positivity)
    · have hzero : steinProfile d δ r = 0 := by
        rw [steinProfile, ← ha, ← hb, Set.indicator_of_notMem hr]
      rw [hzero, Set.indicator_of_notMem hr]
      simp [ENNReal.zero_rpow_of_pos hppos]
  -- integrate the bound
  have hmeas : Measurable fun r : ℝ =>
      (ENNReal.ofReal ‖steinProfile d δ r‖) ^ p := by
    exact (((measurable_steinProfile d δ).norm).ennreal_ofReal).pow_const _
  have hint : IntegrableOn (fun r : ℝ => 4 / L * r⁻¹) (Icc a b) volume := by
    apply ContinuousOn.integrableOn_Icc
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le hapos hx.1)
  have hintegral : (∫ r in Icc a b, 4 / L * r⁻¹) = 1 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hapos hbpos]
    have hba : Real.log (b / a) = L / 4 := by
      rw [ha, hb, steinLower, steinUpper, ← Real.rpow_sub hδ, Real.log_rpow hδ,
        hLeq]
      ring
    rw [hba]
    field_simp
  calc (∫⁻ r : Ioi (0 : ℝ), (ENNReal.ofReal ‖steinProfile d δ r.1‖) ^ p
        ∂Measure.volumeIoiPow (d - 1))
      = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (d - 1) *
          (ENNReal.ofReal ‖steinProfile d δ r‖) ^ p :=
        lintegral_volumeIoiPow (d - 1) _ hmeas
    _ ≤ ∫⁻ r in Ioi (0 : ℝ),
          (Icc a b).indicator (fun r : ℝ => ENNReal.ofReal (4 / L * r⁻¹)) r :=
        lintegral_mono hmono
    _ ≤ ∫⁻ r : ℝ, (Icc a b).indicator (fun r : ℝ => ENNReal.ofReal (4 / L * r⁻¹)) r :=
        lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ∫⁻ r in Icc a b, ENNReal.ofReal (4 / L * r⁻¹) :=
        lintegral_indicator measurableSet_Icc _
    _ = ENNReal.ofReal (∫ r in Icc a b, 4 / L * r⁻¹) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => by
            have hrpos : 0 < r := lt_of_lt_of_le hapos hr.1
            positivity))).symm
    _ = 1 := by rw [hintegral, ENNReal.ofReal_one]

theorem isNormRadial_steinProfile_lift (d : ℕ) (δ : ℝ) :
    _root_.Auto.RadialFourierTransform.IsNormRadial
      (fun x : Euclidean d => steinProfile d δ ‖x‖) := by
  intro x y hxy
  simp only [hxy]

theorem measurable_steinProfile_lift (d : ℕ) (δ : ℝ) :
    Measurable (fun x : Euclidean d => steinProfile d δ ‖x‖) :=
  (measurable_steinProfile d δ).comp measurable_norm

/-- **The Stein test function of BRS Lemma 3.4 is normalized in `L^{p_d}`**,
uniformly in `δ`. -/
theorem eLpNorm_steinProfile_lift_le {d : ℕ} (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    eLpNorm (fun x : Euclidean d => steinProfile d δ ‖x‖)
        (ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1))) volume ≤
      (ENNReal.ofReal (surfaceMass d)) ^ (((d : ℝ) - 1) / (d : ℝ)) := by
  have hd0 : 0 < d := lt_of_lt_of_le two_pos hd
  haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hppos : (0 : ℝ) < (d : ℝ) / ((d : ℝ) - 1) := by positivity
  obtain ⟨w, hw⟩ := exists_norm_eq (Euclidean d) (zero_le_one : (0:ℝ) ≤ 1)
  rw [eLpNorm_of_isNormRadial hd0 hppos _ (isNormRadial_steinProfile_lift d δ)
    (measurable_steinProfile_lift d δ) w hw]
  have hcongr : (∫⁻ r : Ioi (0 : ℝ),
        (ENNReal.ofReal ‖(fun x : Euclidean d => steinProfile d δ ‖x‖) (r.1 • w)‖) ^
          ((d : ℝ) / ((d : ℝ) - 1)) ∂Measure.volumeIoiPow (d - 1)) =
      ∫⁻ r : Ioi (0 : ℝ), (ENNReal.ofReal ‖steinProfile d δ r.1‖) ^
          ((d : ℝ) / ((d : ℝ) - 1)) ∂Measure.volumeIoiPow (d - 1) := by
    refine lintegral_congr fun r => ?_
    have hnorm : ‖r.1 • w‖ = r.1 := by
      rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos r.2]
    simp only [hnorm]
  rw [hcongr]
  have hone : (1 : ℝ) / ((d : ℝ) / ((d : ℝ) - 1)) = ((d : ℝ) - 1) / (d : ℝ) :=
    one_div_div _ _
  rw [hone]
  calc (ENNReal.ofReal (surfaceMass d)) ^ (((d : ℝ) - 1) / (d : ℝ)) *
        (∫⁻ r : Ioi (0 : ℝ), (ENNReal.ofReal ‖steinProfile d δ r.1‖) ^
          ((d : ℝ) / ((d : ℝ) - 1)) ∂Measure.volumeIoiPow (d - 1)) ^
            (((d : ℝ) - 1) / (d : ℝ))
      ≤ (ENNReal.ofReal (surfaceMass d)) ^ (((d : ℝ) - 1) / (d : ℝ)) *
          (1 : ENNReal) ^ (((d : ℝ) - 1) / (d : ℝ)) := by
        refine mul_le_mul' le_rfl ?_
        exact ENNReal.rpow_le_rpow (lintegral_steinProfile_le hd hδ hδ1) (by positivity)
    _ = (ENNReal.ofReal (surfaceMass d)) ^ (((d : ℝ) - 1) / (d : ℝ)) := by
        rw [ENNReal.one_rpow, mul_one]

theorem memLp_steinProfile_lift {d : ℕ} (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    MemLp (fun x : Euclidean d => steinProfile d δ ‖x‖)
      (ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1))) volume := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp : (0 : ℝ) ≤ ((d : ℝ) - 1) / (d : ℝ) := by
    apply div_nonneg <;> linarith
  refine ⟨(measurable_steinProfile_lift d δ).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (eLpNorm_steinProfile_lift_le hd hδ hδ1) ?_
  exact ENNReal.rpow_lt_top_of_nonneg hexp ENNReal.ofReal_ne_top

/-! ### A continuous version of the Stein test function

The sharp cutoff of BRS Lemma 3.4 is replaced by a trapezoidal one, which
changes neither the normalization nor the lower bound but keeps the profile
continuous, as required by the kernel representation (4.1). -/

/-- The trapezoidal cutoff: `0` outside `[a,b]`, `1` on `[2a, b/2]`. -/
def trapezoid (a b : ℝ) : ℝ → ℝ := fun s =>
  max 0 (min 1 (min ((s - a) / a) ((b - s) / (b / 2))))

theorem trapezoid_nonneg (a b : ℝ) (s : ℝ) : 0 ≤ trapezoid a b s := le_max_left _ _

theorem trapezoid_le_one (a b : ℝ) (s : ℝ) : trapezoid a b s ≤ 1 := by
  refine max_le zero_le_one ?_
  exact le_trans (min_le_left _ _) le_rfl

theorem continuous_trapezoid (a b : ℝ) : Continuous (trapezoid a b) := by
  unfold trapezoid
  fun_prop

theorem trapezoid_eq_zero_of_le {a b : ℝ} (ha : 0 < a) {s : ℝ} (hs : s ≤ a) :
    trapezoid a b s = 0 := by
  unfold trapezoid
  have h1 : (s - a) / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
  have h2 : min 1 (min ((s - a) / a) ((b - s) / (b / 2))) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h1)
  exact max_eq_left h2

theorem trapezoid_eq_zero_of_ge {a b : ℝ} (hb : 0 < b) {s : ℝ} (hs : b ≤ s) :
    trapezoid a b s = 0 := by
  unfold trapezoid
  have h1 : (b - s) / (b / 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h2 : min 1 (min ((s - a) / a) ((b - s) / (b / 2))) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h1)
  exact max_eq_left h2

theorem trapezoid_eq_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ℝ}
    (hs1 : 2 * a ≤ s) (hs2 : s ≤ b / 2) : trapezoid a b s = 1 := by
  unfold trapezoid
  have h1 : (1 : ℝ) ≤ (s - a) / a := by
    rw [le_div_iff₀ ha]
    linarith
  have h2 : (1 : ℝ) ≤ (b - s) / (b / 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [min_eq_left (le_min h1 h2), max_eq_right zero_le_one]

/-- The continuous Stein profile: the trapezoidal cutoff times the weight
`s^{1-d}(log(1/s))^{(1-d)/d}`, the latter frozen below `δ^{1/2}` and clipped
from below by `1` in the logarithm so that it is continuous everywhere. -/
def steinBump (d : ℕ) (δ : ℝ) : ℝ → ℝ := fun s =>
  trapezoid (steinLower δ) (steinUpper δ) s *
    ((max (steinLower δ) s) ^ (1 - (d : ℝ)) *
      (max 1 (Real.log (1 / max (steinLower δ) s))) ^ ((1 - (d : ℝ)) / (d : ℝ)))

/-- The complex-valued continuous Stein profile. -/
def steinFun (d : ℕ) (δ : ℝ) : ℝ → ℂ := fun s => ((steinBump d δ s : ℝ) : ℂ)

theorem steinBump_nonneg (d : ℕ) {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    0 ≤ steinBump d δ s := by
  have hpos : 0 < max (steinLower δ) s :=
    lt_of_lt_of_le (steinLower_pos hδ) (le_max_left _ _)
  refine mul_nonneg (trapezoid_nonneg _ _ _) (mul_nonneg ?_ ?_)
  · exact Real.rpow_nonneg hpos.le _
  · exact Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

theorem continuous_steinBump (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (steinBump d δ) := by
  have hlow : 0 < steinLower δ := steinLower_pos hδ
  have hbase : Continuous fun s : ℝ => max (steinLower δ) s :=
    continuous_const.max continuous_id
  have hbasepos : ∀ s : ℝ, 0 < max (steinLower δ) s := fun s =>
    lt_of_lt_of_le hlow (le_max_left _ _)
  have h1 : Continuous fun s : ℝ => (max (steinLower δ) s) ^ (1 - (d : ℝ)) := by
    refine hbase.rpow_const ?_
    intro s
    exact Or.inl (hbasepos s).ne'
  have hlog : Continuous fun s : ℝ => Real.log (1 / max (steinLower δ) s) := by
    refine Continuous.log (continuous_const.div hbase ?_) ?_
    · intro s
      exact (hbasepos s).ne'
    · intro s
      have : 0 < 1 / max (steinLower δ) s := by
        exact div_pos one_pos (hbasepos s)
      exact this.ne'
  have h2 : Continuous fun s : ℝ =>
      (max 1 (Real.log (1 / max (steinLower δ) s))) ^ ((1 - (d : ℝ)) / (d : ℝ)) := by
    refine (continuous_const.max hlog).rpow_const ?_
    intro s
    exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  exact (continuous_trapezoid _ _).mul (h1.mul h2)

theorem continuous_steinFun (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (steinFun d δ) :=
  Complex.continuous_ofReal.comp (continuous_steinBump d hδ)

/-- On the plateau of the cutoff the continuous profile is the exact Stein
weight. -/
theorem steinBump_eq_of_mem_plateau {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {s : ℝ} (hs1 : 2 * steinLower δ ≤ s) (hs2 : s ≤ steinUpper δ / 2)
    (hlog : 1 ≤ Real.log (1 / s)) :
    steinBump d δ s =
      s ^ (1 - (d : ℝ)) * Real.log (1 / s) ^ ((1 - (d : ℝ)) / (d : ℝ)) := by
  have hlow : 0 < steinLower δ := steinLower_pos hδ
  have hup : 0 < steinUpper δ := steinUpper_pos hδ
  have hmax : max (steinLower δ) s = s := max_eq_right (by linarith)
  rw [steinBump, trapezoid_eq_one hlow hup hs1 hs2, one_mul, hmax,
    max_eq_right hlog]

/-- The continuous profile is dominated by the sharp-cutoff profile. -/
theorem norm_steinFun_le_norm_steinProfile {d : ℕ} (hd : 2 ≤ d) {δ : ℝ}
    (hδ : 0 < δ) (_hδ1 : δ < 1) (s : ℝ) :
    ‖steinFun d δ s‖ ≤ ‖steinProfile d δ s‖ := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hexp : ((1 : ℝ) - (d : ℝ)) / (d : ℝ) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  have hlow : 0 < steinLower δ := steinLower_pos hδ
  have hup : 0 < steinUpper δ := steinUpper_pos hδ
  have hup1 : steinUpper δ < 1 := steinUpper_lt_one hδ _hδ1
  by_cases hs : s ∈ Icc (steinLower δ) (steinUpper δ)
  · have hspos : 0 < s := lt_of_lt_of_le hlow hs.1
    have hs1 : s < 1 := lt_of_le_of_lt hs.2 hup1
    have hlogpos : 0 < Real.log (1 / s) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hspos]
      linarith
    have hmax : max (steinLower δ) s = s := max_eq_right hs.1
    have hnormP : ‖steinProfile d δ s‖ =
        s ^ (1 - (d : ℝ)) * Real.log (1 / s) ^ ((1 - (d : ℝ)) / (d : ℝ)) := by
      rw [steinProfile, Set.indicator_of_mem hs, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    have hlogle : Real.log (1 / s) ≤ max 1 (Real.log (1 / s)) := le_max_right _ _
    have hrpow : (max 1 (Real.log (1 / s))) ^ ((1 - (d : ℝ)) / (d : ℝ)) ≤
        Real.log (1 / s) ^ ((1 - (d : ℝ)) / (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hlogpos hlogle hexp
    rw [steinFun, Complex.norm_real,
      Real.norm_of_nonneg (steinBump_nonneg d hδ s), hnormP, steinBump, hmax]
    calc trapezoid (steinLower δ) (steinUpper δ) s *
          (s ^ (1 - (d : ℝ)) * (max 1 (Real.log (1 / s))) ^ ((1 - (d : ℝ)) / (d : ℝ)))
        ≤ 1 * (s ^ (1 - (d : ℝ)) *
            (max 1 (Real.log (1 / s))) ^ ((1 - (d : ℝ)) / (d : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (trapezoid_le_one _ _ _) ?_
          positivity
      _ = s ^ (1 - (d : ℝ)) *
            (max 1 (Real.log (1 / s))) ^ ((1 - (d : ℝ)) / (d : ℝ)) := one_mul _
      _ ≤ s ^ (1 - (d : ℝ)) * Real.log (1 / s) ^ ((1 - (d : ℝ)) / (d : ℝ)) := by
          refine mul_le_mul_of_nonneg_left hrpow ?_
          positivity
  · have hzero : steinBump d δ s = 0 := by
      rw [steinBump]
      rcases not_and_or.mp (fun h => hs ⟨h.1, h.2⟩) with h | h
      · rw [trapezoid_eq_zero_of_le hlow (le_of_not_ge h), zero_mul]
      · rw [trapezoid_eq_zero_of_ge hup (le_of_not_ge h), zero_mul]
    rw [steinFun, hzero]
    simp

theorem measurable_steinFun_lift (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Measurable (fun x : Euclidean d => steinFun d δ ‖x‖) :=
  ((continuous_steinFun d hδ).measurable).comp measurable_norm

theorem isNormRadial_steinFun_lift (d : ℕ) (δ : ℝ) :
    _root_.Auto.RadialFourierTransform.IsNormRadial
      (fun x : Euclidean d => steinFun d δ ‖x‖) := by
  intro x y hxy
  simp only [hxy]

/-- The continuous Stein test function is normalized in `L^{p_d}` too. -/
theorem eLpNorm_steinFun_lift_le {d : ℕ} (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    eLpNorm (fun x : Euclidean d => steinFun d δ ‖x‖)
        (ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1))) volume ≤
      (ENNReal.ofReal (surfaceMass d)) ^ (((d : ℝ) - 1) / (d : ℝ)) := by
  refine le_trans (eLpNorm_mono_enorm ?_) (eLpNorm_steinProfile_lift_le hd hδ hδ1)
  intro x
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    (norm_steinFun_le_norm_steinProfile hd hδ hδ1 ‖x‖)

theorem memLp_steinFun_lift {d : ℕ} (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    MemLp (fun x : Euclidean d => steinFun d δ ‖x‖)
      (ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1))) volume := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp : (0 : ℝ) ≤ ((d : ℝ) - 1) / (d : ℝ) := by
    apply div_nonneg <;> linarith
  refine ⟨(measurable_steinFun_lift d hδ).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (eLpNorm_steinFun_lift_le hd hδ hδ1) ?_
  exact ENNReal.rpow_lt_top_of_nonneg hexp ENNReal.ofReal_ne_top

/-! ### The kernel lower bound behind Lemma 3.4 -/

/-- For dilations `t ∈ [1,2]`, radii `r` within `s/2` of `t`, and small `s`,
the kernel of (4.2) in ambient dimension `d+1` is at least `c s^{d-1}`. -/
theorem le_brsKernel {d : ℕ} {t r s : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2)
    (hs : 0 < s) (hs2 : s ≤ 1 / 2) (hrt : |r - t| ≤ s / 2) :
    (s / 36) ^ (d - 2) * (s / 18) ≤ brsKernel (d + 1) t r s := by
  have habs := abs_le.mp hrt
  have hr1 : 3 / 4 ≤ r := by
    have h1 : -(s / 2) ≤ r - t := habs.1
    have : s / 2 ≤ 1 / 4 := by linarith
    linarith
  have hr2 : r ≤ 9 / 4 := by
    have h1 : r - t ≤ s / 2 := habs.2
    have : s / 2 ≤ 1 / 4 := by linarith
    linarith
  have hrpos : 0 < r := by linarith
  have h4rtpos : 0 < 4 * r * t := by
    have : 0 < t := by linarith
    positivity
  have h4rt : 4 * r * t ≤ 18 := by nlinarith
  -- the two square roots
  have hnum1 : (1 : ℝ) ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) := by
    rw [Real.one_le_sqrt]
    nlinarith
  have hsq2 : (s / 2) ^ 2 ≤ s ^ 2 - (r - t) ^ 2 := by
    have hsq : (r - t) ^ 2 ≤ (s / 2) ^ 2 := sq_le_sq' habs.1 habs.2
    nlinarith
  have hnum2 : s / 2 ≤ Real.sqrt (s ^ 2 - (r - t) ^ 2) := by
    rw [show s / 2 = Real.sqrt ((s / 2) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hsq2
  have hprod : s / 2 ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) := by
    calc s / 2 = 1 * (s / 2) := (one_mul _).symm
      _ ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) := by
          refine mul_le_mul hnum1 hnum2 (by positivity) ?_
          exact le_trans zero_le_one hnum1
  have hbracket : s / 36 ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) / (4 * r * t) := by
    calc s / 36 = (s / 2) / 18 := by ring
      _ ≤ (s / 2) / (4 * r * t) := by gcongr
      _ ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) /
            (4 * r * t) := by gcongr
  have hlast : s / 18 ≤ s / (4 * r * t) := by
    exact div_le_div_of_nonneg_left hs.le h4rtpos h4rt
  rw [brsKernel_eq_of_pos]
  refine mul_le_mul ?_ hlast (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity) hbracket _

theorem log_one_div_eq {x : ℝ} : Real.log (1 / x) = -Real.log x := by
  rw [one_div, Real.log_inv]

theorem log_steinLower {δ : ℝ} (hδ : 0 < δ) :
    Real.log (steinLower δ) = -(Real.log (1 / δ) / 2) := by
  rw [steinLower, Real.log_rpow hδ, log_one_div_eq]
  ring

theorem log_steinUpper {δ : ℝ} (hδ : 0 < δ) :
    Real.log (steinUpper δ) = -(Real.log (1 / δ) / 4) := by
  rw [steinUpper, Real.log_rpow hδ, log_one_div_eq]
  ring

theorem log_four_le : Real.log 4 ≤ 3 / 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, Real.log_pow]
  have := Real.log_two_lt_d9
  push_cast
  linarith

/-- Under `12 ≤ log(1/δ)` the plateau of the trapezoid is nonempty. -/
theorem stein_plateau_le {δ : ℝ} (hδ : 0 < δ) (hL : 12 ≤ Real.log (1 / δ)) :
    2 * steinLower δ ≤ steinUpper δ / 2 := by
  have hlow : 0 < steinLower δ := steinLower_pos hδ
  have hup : 0 < steinUpper δ := steinUpper_pos hδ
  have hlog : Real.log (4 * steinLower δ) ≤ Real.log (steinUpper δ) := by
    rw [Real.log_mul (by norm_num) hlow.ne', log_steinLower hδ, log_steinUpper hδ]
    have := log_four_le
    linarith
  have h4 : 4 * steinLower δ ≤ steinUpper δ := by
    have := Real.log_le_log_iff (by positivity : (0:ℝ) < 4 * steinLower δ) hup
    exact (this.mp hlog)
  linarith

/-- The plateau lies below `1/2`, where the kernel bound applies. -/
theorem stein_plateau_lt_one {δ : ℝ} (hδ : 0 < δ) (_hL : 12 ≤ Real.log (1 / δ)) :
    steinUpper δ / 2 ≤ 1 / 2 := by
  have hup1 : steinUpper δ < 1 := by
    refine steinUpper_lt_one hδ ?_
    by_contra hcon
    push Not at hcon
    have : Real.log (1 / δ) ≤ 0 := by
      refine Real.log_nonpos (by positivity) ?_
      rw [div_le_one hδ]
      exact hcon
    linarith
  linarith

/-- The logarithm is at least `L/4` on the plateau, hence at least `3`. -/
theorem three_le_log_of_mem_plateau {δ : ℝ} (hδ : 0 < δ)
    (hL : 12 ≤ Real.log (1 / δ)) {s : ℝ} (hs : s ≤ steinUpper δ / 2) (hs0 : 0 < s) :
    Real.log (1 / δ) / 4 ≤ Real.log (1 / s) := by
  have hup : 0 < steinUpper δ := steinUpper_pos hδ
  have h1 : s ≤ steinUpper δ := by linarith
  have : Real.log s ≤ Real.log (steinUpper δ) := Real.log_le_log hs0 h1
  rw [log_steinUpper hδ] at this
  rw [log_one_div_eq]
  rw [log_one_div_eq] at this ⊢
  linarith

/-- The logarithm is at most `L/2` on the plateau. -/
theorem log_le_of_mem_plateau {δ : ℝ} (hδ : 0 < δ) {s : ℝ}
    (hs : 2 * steinLower δ ≤ s) :
    Real.log (1 / s) ≤ Real.log (1 / δ) / 2 := by
  have hlow : 0 < steinLower δ := steinLower_pos hδ
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith) hs
  have h1 : steinLower δ ≤ s := by linarith
  have h2 : Real.log (steinLower δ) ≤ Real.log s := Real.log_le_log hlow h1
  rw [log_steinLower hδ] at h2
  rw [log_one_div_eq]
  rw [log_one_div_eq] at h2 ⊢
  linarith

/-- **The logarithmic gain of Lemma 3.4.**  On the plateau of the cutoff the
weight `s^{-1}(log(1/s))^{-(d-1)/d}` integrates to at least `L^{1/d}/8`, where
`L = log(1/δ)`. -/
theorem le_integral_stein_weight {d : ℕ} (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    (hL : 12 ≤ Real.log (1 / δ)) :
    Real.log (1 / δ) ^ (1 / (d : ℝ)) / 8 ≤
      ∫ s in (2 * steinLower δ)..(steinUpper δ / 2),
        s⁻¹ * Real.log (1 / s) ^ (-(((d : ℝ) - 1) / (d : ℝ))) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hLpos : (0 : ℝ) < Real.log (1 / δ) := by linarith
  have hc0 : -(((d : ℝ) - 1) / (d : ℝ)) ≤ 0 := by
    simp only [neg_nonpos]
    apply div_nonneg <;> linarith
  have hlow : 0 < steinLower δ := steinLower_pos hδ
  have hup : 0 < steinUpper δ := steinUpper_pos hδ
  have hapos : (0 : ℝ) < 2 * steinLower δ := by linarith
  have hbpos : (0 : ℝ) < steinUpper δ / 2 := by linarith
  have hab : 2 * steinLower δ ≤ steinUpper δ / 2 := stein_plateau_le hδ hL
  -- pointwise lower bound on the plateau
  have hpoint : ∀ s ∈ Icc (2 * steinLower δ) (steinUpper δ / 2),
      (Real.log (1 / δ) / 2) ^ (-(((d : ℝ) - 1) / (d : ℝ))) * s⁻¹ ≤
        s⁻¹ * Real.log (1 / s) ^ (-(((d : ℝ) - 1) / (d : ℝ))) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hapos hs.1
    have hlogpos : 0 < Real.log (1 / s) := by
      have := three_le_log_of_mem_plateau hδ hL hs.2 hs0
      linarith
    have hle : Real.log (1 / s) ≤ Real.log (1 / δ) / 2 :=
      log_le_of_mem_plateau hδ hs.1
    have hrpow : (Real.log (1 / δ) / 2) ^ (-(((d : ℝ) - 1) / (d : ℝ))) ≤
        Real.log (1 / s) ^ (-(((d : ℝ) - 1) / (d : ℝ))) :=
      Real.rpow_le_rpow_of_nonpos hlogpos hle hc0
    calc (Real.log (1 / δ) / 2) ^ (-(((d : ℝ) - 1) / (d : ℝ))) * s⁻¹
        ≤ Real.log (1 / s) ^ (-(((d : ℝ) - 1) / (d : ℝ))) * s⁻¹ := by
          exact mul_le_mul_of_nonneg_right hrpow (by positivity)
      _ = s⁻¹ * Real.log (1 / s) ^ (-(((d : ℝ) - 1) / (d : ℝ))) := mul_comm _ _
  have hint1 : IntervalIntegrable
      (fun s : ℝ => (Real.log (1 / δ) / 2) ^ (-(((d : ℝ) - 1) / (d : ℝ))) * s⁻¹)
      volume (2 * steinLower δ) (steinUpper δ / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ continuousOn_id ?_)
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (lt_of_lt_of_le hapos hx.1).ne'
  have hint2 : IntervalIntegrable
      (fun s : ℝ => s⁻¹ * Real.log (1 / s) ^ (-(((d : ℝ) - 1) / (d : ℝ))))
      volume (2 * steinLower δ) (steinUpper δ / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    have hpos : ∀ x ∈ Set.uIcc (2 * steinLower δ) (steinUpper δ / 2), 0 < x := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact lt_of_lt_of_le hapos hx.1
    refine ContinuousOn.mul (ContinuousOn.inv₀ continuousOn_id ?_) ?_
    · intro x hx
      exact (hpos x hx).ne'
    · refine ContinuousOn.rpow_const ?_ ?_
      · refine ContinuousOn.log (ContinuousOn.div continuousOn_const continuousOn_id ?_) ?_
        · intro x hx
          exact (hpos x hx).ne'
        · intro x hx
          have := hpos x hx
          exact (div_pos one_pos this).ne'
      · intro x hx
        left
        have hxpos := hpos x hx
        have h3 : Real.log (1 / δ) / 4 ≤ Real.log (1 / x) := by
          rw [Set.uIcc_of_le hab] at hx
          exact three_le_log_of_mem_plateau hδ hL hx.2 hxpos
        have : 0 < Real.log (1 / x) := by linarith
        exact this.ne'
  have hmono := intervalIntegral.integral_mono_on hab hint1 hint2 hpoint
  refine le_trans ?_ hmono
  -- compute the elementary integral
  have hcomp : (∫ s in (2 * steinLower δ)..(steinUpper δ / 2),
        (Real.log (1 / δ) / 2) ^ (-(((d : ℝ) - 1) / (d : ℝ))) * s⁻¹) =
      (Real.log (1 / δ) / 2) ^ (-(((d : ℝ) - 1) / (d : ℝ))) *
        Real.log ((steinUpper δ / 2) / (2 * steinLower δ)) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hapos hbpos]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlogba : Real.log ((steinUpper δ / 2) / (2 * steinLower δ)) =
      Real.log (1 / δ) / 4 - Real.log 4 := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_div hup.ne' (two_ne_zero), Real.log_mul two_ne_zero hlow.ne',
      log_steinUpper hδ, log_steinLower hδ, hlog4]
    ring
  rw [hcomp, hlogba]
  -- the remaining arithmetic
  have h8 : Real.log (1 / δ) / 8 ≤ Real.log (1 / δ) / 4 - Real.log 4 := by
    have := log_four_le
    linarith
  have hbase : Real.log (1 / δ) ^ (-(((d : ℝ) - 1) / (d : ℝ))) ≤
      (Real.log (1 / δ) / 2) ^ (-(((d : ℝ) - 1) / (d : ℝ))) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hc0
    linarith
  have hadd : Real.log (1 / δ) ^ (-(((d : ℝ) - 1) / (d : ℝ))) * Real.log (1 / δ)
      = Real.log (1 / δ) ^ (1 / (d : ℝ)) := by
    have h1 : Real.log (1 / δ) ^ (-(((d : ℝ) - 1) / (d : ℝ))) *
        Real.log (1 / δ) ^ (1 : ℝ) =
          Real.log (1 / δ) ^ (-(((d : ℝ) - 1) / (d : ℝ)) + 1) :=
      (Real.rpow_add hLpos _ _).symm
    rw [Real.rpow_one] at h1
    rw [h1]
    congr 1
    field_simp
    ring
  have hkey : Real.log (1 / δ) ^ (1 / (d : ℝ)) / 8 =
      Real.log (1 / δ) ^ (-(((d : ℝ) - 1) / (d : ℝ))) *
        (Real.log (1 / δ) / 8) := by
    rw [← hadd]
    ring
  rw [hkey]
  refine mul_le_mul hbase h8 (by positivity) ?_
  exact Real.rpow_nonneg (by positivity) _

/-- The kernel lower bound, in terms of the ambient dimension `D`. -/
theorem le_brsKernel_dim {D : ℕ} {t r s : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2)
    (hs : 0 < s) (hs2 : s ≤ 1 / 2) (hrt : |r - t| ≤ s / 2) :
    (s / 36) ^ (D - 3) * (s / 18) ≤ brsKernel D t r s := by
  have habs := abs_le.mp hrt
  have hr1 : 3 / 4 ≤ r := by
    have : s / 2 ≤ 1 / 4 := by linarith
    linarith [habs.1]
  have hr2 : r ≤ 9 / 4 := by
    have : s / 2 ≤ 1 / 4 := by linarith
    linarith [habs.2]
  have hrpos : 0 < r := by linarith
  have h4rtpos : 0 < 4 * r * t := by
    have : 0 < t := by linarith
    positivity
  have h4rt : 4 * r * t ≤ 18 := by nlinarith
  have hnum1 : (1 : ℝ) ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) := by
    rw [Real.one_le_sqrt]
    nlinarith
  have hsq2 : (s / 2) ^ 2 ≤ s ^ 2 - (r - t) ^ 2 := by
    have hsq : (r - t) ^ 2 ≤ (s / 2) ^ 2 := sq_le_sq' habs.1 habs.2
    nlinarith
  have hnum2 : s / 2 ≤ Real.sqrt (s ^ 2 - (r - t) ^ 2) := by
    rw [show s / 2 = Real.sqrt ((s / 2) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hsq2
  have hprod : s / 2 ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) := by
    calc s / 2 = 1 * (s / 2) := (one_mul _).symm
      _ ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) := by
          refine mul_le_mul hnum1 hnum2 (by positivity) (le_trans zero_le_one hnum1)
  have hbracket : s / 36 ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) / (4 * r * t) := by
    calc s / 36 = (s / 2) / 18 := by ring
      _ ≤ (s / 2) / (4 * r * t) := by gcongr
      _ ≤ _ := by gcongr
  have hlast : s / 18 ≤ s / (4 * r * t) :=
    div_le_div_of_nonneg_left hs.le h4rtpos h4rt
  rw [brsKernel_eq_of_pos]
  refine mul_le_mul ?_ hlast (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity) hbracket _

/-- On the plateau, the kernel times the Stein profile dominates a constant
multiple of the logarithmic weight `s^{-1}(log(1/s))^{-(D-1)/D}`. -/
theorem le_kernel_mul_steinBump {D : ℕ} (hD : 3 ≤ D) {δ : ℝ} (hδ : 0 < δ)
    (hL : 12 ≤ Real.log (1 / δ)) {t r : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2)
    (hrt : |r - t| ≤ steinLower δ) {s : ℝ}
    (hs1 : 2 * steinLower δ ≤ s) (hs2 : s ≤ steinUpper δ / 2) :
    (1 / (36 ^ (D - 3) * 18)) *
        (s⁻¹ * Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ)))) ≤
      brsKernel D t r s * steinBump D δ s := by
  have hlow : 0 < steinLower δ := steinLower_pos hδ
  have hspos : 0 < s := lt_of_lt_of_le (by linarith) hs1
  have hshalf : s ≤ 1 / 2 := le_trans hs2 (stein_plateau_lt_one hδ hL)
  have hrts : |r - t| ≤ s / 2 := le_trans hrt (by linarith)
  have hlogplateau : Real.log (1 / δ) / 4 ≤ Real.log (1 / s) :=
    three_le_log_of_mem_plateau hδ hL hs2 hspos
  have hlogone : (1 : ℝ) ≤ Real.log (1 / s) := by linarith
  have hlogpos : 0 < Real.log (1 / s) := by linarith
  have hbump : steinBump D δ s =
      s ^ (1 - (D : ℝ)) * Real.log (1 / s) ^ ((1 - (D : ℝ)) / (D : ℝ)) := by
    refine steinBump_eq_of_mem_plateau hδ ?_ hs1 hs2 hlogone
    by_contra hcon
    push Not at hcon
    have : Real.log (1 / δ) ≤ 0 := by
      refine Real.log_nonpos (by positivity) ?_
      rw [div_le_one hδ]
      exact hcon
    linarith
  have hkernel : (s / 36) ^ (D - 3) * (s / 18) ≤ brsKernel D t r s :=
    le_brsKernel_dim ht1 ht2 hspos hshalf hrts
  have hbumpnonneg : 0 ≤ steinBump D δ s := steinBump_nonneg D hδ s
  -- the algebraic identity
  have hpowsucc : s ^ (D - 3) * s = s ^ ((D : ℝ) - 2) := by
    rw [← pow_succ]
    have hDD : D - 3 + 1 = D - 2 := by omega
    rw [hDD, ← Real.rpow_natCast s (D - 2)]
    congr 1
    have h2 : (2 : ℕ) ≤ D := by omega
    push_cast [Nat.cast_sub h2]
    ring
  have hcollapse : s ^ ((D : ℝ) - 2) * s ^ (1 - (D : ℝ)) = s⁻¹ := by
    rw [← Real.rpow_add hspos, show (D : ℝ) - 2 + (1 - (D : ℝ)) = -1 by ring,
      Real.rpow_neg_one]
  have hexp : ((1 : ℝ) - (D : ℝ)) / (D : ℝ) = -(((D : ℝ) - 1) / (D : ℝ)) := by
    ring
  have hident : (s / 36) ^ (D - 3) * (s / 18) *
      (s ^ (1 - (D : ℝ)) * Real.log (1 / s) ^ ((1 - (D : ℝ)) / (D : ℝ))) =
        (1 / (36 ^ (D - 3) * 18)) *
          (s⁻¹ * Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ)))) := by
    rw [hexp, div_pow]
    rw [show s ^ (D - 3) / (36 : ℝ) ^ (D - 3) * (s / 18) *
        (s ^ (1 - (D : ℝ)) * Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ)))) =
        (1 / ((36 : ℝ) ^ (D - 3) * 18)) *
          ((s ^ (D - 3) * s) * s ^ (1 - (D : ℝ)) *
            Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ)))) by ring]
    rw [hpowsucc, hcollapse]
  calc (1 / (36 ^ (D - 3) * 18)) *
        (s⁻¹ * Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ))))
      = (s / 36) ^ (D - 3) * (s / 18) *
          (s ^ (1 - (D : ℝ)) * Real.log (1 / s) ^ ((1 - (D : ℝ)) / (D : ℝ))) :=
        hident.symm
    _ = (s / 36) ^ (D - 3) * (s / 18) * steinBump D δ s := by rw [hbump]
    _ ≤ brsKernel D t r s * steinBump D δ s := by
        exact mul_le_mul_of_nonneg_right hkernel hbumpnonneg

theorem continuous_brsKernel (D : ℕ) {t r : ℝ} (hrt : 0 < 4 * r * t) :
    Continuous fun s : ℝ => brsKernel D t r s := by
  unfold brsKernel
  have hne : ((r + t) ^ 2 - (r - t) ^ 2) ≠ 0 := by
    rw [show (r + t) ^ 2 - (r - t) ^ 2 = 4 * r * t by ring]
    exact hrt.ne'
  fun_prop (disch := assumption)

theorem brsKernel_nonneg (D : ℕ) {t r s : ℝ} (hrt : 0 < 4 * r * t) (hs : 0 ≤ s) :
    0 ≤ brsKernel D t r s := by
  have hden : (0 : ℝ) < (r + t) ^ 2 - (r - t) ^ 2 := by
    rw [show (r + t) ^ 2 - (r - t) ^ 2 = 4 * r * t by ring]
    exact hrt
  unfold brsKernel
  have h1 : (0 : ℝ) ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) / ((r + t) ^ 2 - (r - t) ^ 2) := by
    positivity
  exact mul_nonneg (pow_nonneg h1 _) (by positivity)

theorem delta_lt_one_of_log {δ : ℝ} (hδ : 0 < δ) (hL : 12 ≤ Real.log (1 / δ)) :
    δ < 1 := by
  by_contra hcon
  push Not at hcon
  have : Real.log (1 / δ) ≤ 0 := by
    refine Real.log_nonpos (by positivity) ?_
    rw [div_le_one hδ]
    exact hcon
  linarith

theorem steinLower_le_half {δ : ℝ} (hδ : 0 < δ) (hL : 12 ≤ Real.log (1 / δ)) :
    steinLower δ ≤ 1 / 2 := by
  have hup : steinUpper δ / 2 ≤ 1 / 2 := stein_plateau_lt_one hδ hL
  have hplateau : 2 * steinLower δ ≤ steinUpper δ / 2 := stein_plateau_le hδ hL
  have hpos : 0 < steinLower δ := steinLower_pos hδ
  linarith

/-- **The interval-integral form of the Lemma 3.4 lower bound.** -/
theorem le_intervalIntegral_kernel_steinBump {D : ℕ} (hD : 3 ≤ D) {δ : ℝ}
    (hδ : 0 < δ) (hL : 12 ≤ Real.log (1 / δ)) {t r : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2)
    (hrt : |r - t| ≤ steinLower δ) :
    (1 / (36 ^ (D - 3) * 18)) * (Real.log (1 / δ) ^ (1 / (D : ℝ)) / 8) ≤
      ∫ s in |r - t|..(r + t), brsKernel D t r s * steinBump D δ s := by
  have hD2 : 2 ≤ D := by omega
  have hlow : 0 < steinLower δ := steinLower_pos hδ
  have hlowhalf : steinLower δ ≤ 1 / 2 := steinLower_le_half hδ hL
  have habs := abs_le.mp hrt
  have hr1 : 1 / 2 ≤ r := by linarith [habs.1]
  have hrpos : 0 < r := by linarith
  have h4rt : 0 < 4 * r * t := by
    have : 0 < t := by linarith
    positivity
  have hcont : Continuous fun s : ℝ => brsKernel D t r s * steinBump D δ s :=
    (continuous_brsKernel D h4rt).mul (continuous_steinBump D hδ)
  have hα : |r - t| ≤ 2 * steinLower δ := by linarith
  have hplateau : 2 * steinLower δ ≤ steinUpper δ / 2 := stein_plateau_le hδ hL
  have hβ : steinUpper δ / 2 ≤ r + t := by
    have := stein_plateau_lt_one hδ hL
    linarith
  have hnonneg : ∀ s : ℝ, 0 ≤ s → 0 ≤ brsKernel D t r s * steinBump D δ s :=
    fun s hs => mul_nonneg (brsKernel_nonneg D h4rt hs) (steinBump_nonneg D hδ s)
  have hint : ∀ u v : ℝ, IntervalIntegrable
      (fun s : ℝ => brsKernel D t r s * steinBump D δ s) volume u v := fun u v =>
    hcont.intervalIntegrable u v
  have hsplit1 : (∫ s in |r - t|..(2 * steinLower δ),
        brsKernel D t r s * steinBump D δ s) +
      (∫ s in (2 * steinLower δ)..(r + t), brsKernel D t r s * steinBump D δ s) =
      ∫ s in |r - t|..(r + t), brsKernel D t r s * steinBump D δ s :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hsplit2 : (∫ s in (2 * steinLower δ)..(steinUpper δ / 2),
        brsKernel D t r s * steinBump D δ s) +
      (∫ s in (steinUpper δ / 2)..(r + t), brsKernel D t r s * steinBump D δ s) =
      ∫ s in (2 * steinLower δ)..(r + t), brsKernel D t r s * steinBump D δ s :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hpos1 : 0 ≤ ∫ s in |r - t|..(2 * steinLower δ),
      brsKernel D t r s * steinBump D δ s := by
    refine intervalIntegral.integral_nonneg hα ?_
    intro s hs
    exact hnonneg s (le_trans (abs_nonneg _) hs.1)
  have hpos2 : 0 ≤ ∫ s in (steinUpper δ / 2)..(r + t),
      brsKernel D t r s * steinBump D δ s := by
    refine intervalIntegral.integral_nonneg hβ ?_
    intro s hs
    have hupos : 0 < steinUpper δ / 2 := by
      have := steinUpper_pos hδ
      linarith
    exact hnonneg s (le_trans hupos.le hs.1)
  have hweightint : IntervalIntegrable (fun s : ℝ =>
      (1 / (36 ^ (D - 3) * 18) : ℝ) *
        (s⁻¹ * Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ)))))
      volume (2 * steinLower δ) (steinUpper δ / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    have hpos : ∀ x ∈ Set.uIcc (2 * steinLower δ) (steinUpper δ / 2), 0 < x := by
      intro x hx
      rw [Set.uIcc_of_le hplateau] at hx
      exact lt_of_lt_of_le (by linarith) hx.1
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul
      (ContinuousOn.inv₀ continuousOn_id fun x hx => (hpos x hx).ne') ?_)
    refine ContinuousOn.rpow_const ?_ ?_
    · refine ContinuousOn.log
        (ContinuousOn.div continuousOn_const continuousOn_id
          fun x hx => (hpos x hx).ne') ?_
      intro x hx
      exact (div_pos one_pos (hpos x hx)).ne'
    · intro x hx
      left
      have hxpos := hpos x hx
      rw [Set.uIcc_of_le hplateau] at hx
      have h3 := three_le_log_of_mem_plateau hδ hL hx.2 hxpos
      have hlogpos : 0 < Real.log (1 / x) := by linarith
      exact hlogpos.ne'
  have hmono : (∫ s in (2 * steinLower δ)..(steinUpper δ / 2),
        (1 / (36 ^ (D - 3) * 18) : ℝ) *
          (s⁻¹ * Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ))))) ≤
      ∫ s in (2 * steinLower δ)..(steinUpper δ / 2),
        brsKernel D t r s * steinBump D δ s := by
    refine intervalIntegral.integral_mono_on hplateau hweightint (hint _ _) ?_
    intro s hs
    exact le_kernel_mul_steinBump hD hδ hL ht1 ht2 hrt hs.1 hs.2
  have hconst : (∫ s in (2 * steinLower δ)..(steinUpper δ / 2),
        (1 / (36 ^ (D - 3) * 18) : ℝ) *
          (s⁻¹ * Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ))))) =
      (1 / (36 ^ (D - 3) * 18) : ℝ) *
        ∫ s in (2 * steinLower δ)..(steinUpper δ / 2),
          s⁻¹ * Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ))) :=
    intervalIntegral.integral_const_mul _ _
  have hgain := le_integral_stein_weight (d := D) hD2 hδ hL
  have hcpos : (0 : ℝ) < 1 / (36 ^ (D - 3) * 18) := by positivity
  calc (1 / (36 ^ (D - 3) * 18) : ℝ) * (Real.log (1 / δ) ^ (1 / (D : ℝ)) / 8)
      ≤ (1 / (36 ^ (D - 3) * 18) : ℝ) *
          ∫ s in (2 * steinLower δ)..(steinUpper δ / 2),
            s⁻¹ * Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ))) :=
        mul_le_mul_of_nonneg_left hgain hcpos.le
    _ = ∫ s in (2 * steinLower δ)..(steinUpper δ / 2),
          (1 / (36 ^ (D - 3) * 18) : ℝ) *
            (s⁻¹ * Real.log (1 / s) ^ (-(((D : ℝ) - 1) / (D : ℝ)))) := hconst.symm
    _ ≤ ∫ s in (2 * steinLower δ)..(steinUpper δ / 2),
          brsKernel D t r s * steinBump D δ s := hmono
    _ ≤ ∫ s in (2 * steinLower δ)..(r + t),
          brsKernel D t r s * steinBump D δ s := by
        rw [← hsplit2]
        linarith
    _ ≤ ∫ s in |r - t|..(r + t), brsKernel D t r s * steinBump D δ s := by
        rw [← hsplit1]
        linarith

/-- The constant of the Lemma 3.4 lower bound in ambient dimension `d + 1`. -/
def steinLowerConst (d : ℕ) : ℝ :=
  ((surfaceMass (d + 1))⁻¹ * surfaceMass d * ((4 : ℝ) * 2 ^ (d - 2))) *
    ((1 / (36 ^ (d - 2) * 18)) * (1 / 8))

theorem steinLowerConst_pos {d : ℕ} (hd : 2 ≤ d) : 0 < steinLowerConst d := by
  have h1 : 0 < surfaceMass d := surfaceMass_pos (by omega)
  have h2 : 0 < surfaceMass (d + 1) := surfaceMass_pos (by omega)
  rw [steinLowerConst]
  positivity

/-- **The pointwise lower bound of BRS Lemma 3.4.**  If `‖x‖` is within
`δ^{1/2}` of a dilation `t ∈ [1,2]`, the spherical average of the Stein test
function at `x` is at least `c (log(1/δ))^{1/(d+1)}`. -/
theorem le_norm_sphericalAverage_steinFun {d : ℕ} (hd : 2 ≤ d) {δ : ℝ}
    (hδ : 0 < δ) (hL : 12 ≤ Real.log (1 / δ)) {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2)
    {x : Euclidean (d + 1)} (hx : |‖x‖ - t| ≤ steinLower δ) :
    steinLowerConst d * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1)) ≤
      ‖_root_.Spherical.sphericalAverage t (fun y => steinFun (d + 1) δ ‖y‖) x‖ := by
  have hD : 3 ≤ d + 1 := by omega
  have habs := abs_le.mp hx
  have hlowhalf : steinLower δ ≤ 1 / 2 := steinLower_le_half hδ hL
  have hnormpos : 0 < ‖x‖ := by linarith [habs.1]
  have hx0 : x ≠ 0 := norm_pos_iff.mp hnormpos
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hC1 : 0 < surfaceMass d := surfaceMass_pos (by omega)
  have hC2 : 0 < surfaceMass (d + 1) := surfaceMass_pos (by omega)
  set C : ℝ := (surfaceMass (d + 1))⁻¹ * surfaceMass d * ((4 : ℝ) * 2 ^ (d - 2))
    with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    positivity
  -- the interval-integral bound, with the exponents in ambient dimension d+1
  have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
  have hsub : d + 1 - 3 = d - 2 := by omega
  have hbound := le_intervalIntegral_kernel_steinBump (D := d + 1) hD hδ hL ht1 ht2
    (r := ‖x‖) hx
  rw [hcast, hsub] at hbound
  -- rewrite the spherical average
  have hintegrand : ∀ s : ℝ,
      ((brsKernel (d + 1) t ‖x‖ s : ℝ)) • steinFun (d + 1) δ s =
        ((brsKernel (d + 1) t ‖x‖ s * steinBump (d + 1) δ s : ℝ) : ℂ) := by
    intro s
    rw [steinFun, Complex.real_smul]
    push_cast
    ring
  rw [sphericalAverage_eq_kernel_integral hd (steinFun (d + 1) δ)
    (continuous_steinFun _ hδ) hx0 ht0]
  simp only [hintegrand]
  rw [intervalIntegral.integral_ofReal, ← hCdef, ← Complex.ofReal_mul,
    Complex.norm_real]
  have hIpos : 0 ≤ ∫ s in |‖x‖ - t|..(‖x‖ + t),
      brsKernel (d + 1) t ‖x‖ s * steinBump (d + 1) δ s := by
    refine le_trans ?_ hbound
    have hLpos : 0 < Real.log (1 / δ) := by linarith
    positivity
  rw [Real.norm_of_nonneg (by positivity)]
  calc steinLowerConst d * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1))
      = C * ((1 / (36 ^ (d - 2) * 18)) *
          (Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1)) / 8)) := by
        rw [steinLowerConst, hCdef]
        ring
    _ ≤ C * ∫ s in |‖x‖ - t|..(‖x‖ + t),
          brsKernel (d + 1) t ‖x‖ s * steinBump (d + 1) δ s :=
        mul_le_mul_of_nonneg_left hbound hCpos.le

theorem delta_le_steinLower {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ ≤ steinLower δ := by
  have h : δ ^ (1 : ℝ) ≤ δ ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num : (1 : ℝ) / 2 ≤ 1)
  rwa [Real.rpow_one] at h

/-- **BRS Lemma 3.4**, in separated-set form: for every `δ`-separated subset
`T` of `E` and every `δ ≤ e^{-12}`, the radial operator norm at the endpoint
exponent `p_D = D/(D-1)`, `D = d+1`, is at least
`(card T)^{1/q} δ^{1/q} (log(1/δ))^{1/D}` up to a constant. -/
theorem le_eLpNorm_ratio_stein {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {q : ℝ} (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → 12 ≤ Real.log (1 / δ) → ∀ T : Finset ℝ,
      (↑T : Set ℝ) ⊆ E → (∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s|) →
        ENNReal.ofReal (c * (T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) *
              Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1))) *
            eLpNorm (fun y : Euclidean (d + 1) => steinFun (d + 1) δ ‖y‖)
              (ENNReal.ofReal (((d : ℝ) + 1) / ((d : ℝ) + 1 - 1))) volume ≤
          eLpNorm (M E (fun y : Euclidean (d + 1) => steinFun (d + 1) δ ‖y‖))
            (ENNReal.ofReal q) volume := by
  have hd1 : 0 < d + 1 := by omega
  haveI : Nonempty (Fin (d + 1)) := ⟨⟨0, hd1⟩⟩
  have hqinv : (0 : ℝ) ≤ 1 / q := le_of_lt (div_pos one_pos hq)
  set V : ℝ := (volume (Metric.ball (0 : Euclidean (d + 1)) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean (d + 1)) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean (d + 1)) one_pos)) hVtop
  have hVeq : volume (Metric.ball (0 : Euclidean (d + 1)) 1) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hVtop]
  set c1 : ℝ := (3 / 4 : ℝ) ^ d / 2 with hc1
  have hc1pos : 0 < c1 := by
    rw [hc1]
    positivity
  set Sm : ℝ := surfaceMass (d + 1) with hSm
  have hSmpos : 0 < Sm := surfaceMass_pos hd1
  set K : ℝ := steinLowerConst d with hK
  have hKpos : 0 < K := steinLowerConst_pos hd
  refine ⟨K * (c1 * V) ^ (1 / q) / Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1)),
    div_pos (mul_pos hKpos (Real.rpow_pos_of_pos (mul_pos hc1pos hVpos) _))
      (Real.rpow_pos_of_pos hSmpos _), ?_⟩
  intro δ hδ hL T hTE hsep
  have hδ1 : δ < 1 := delta_lt_one_of_log hδ hL
  have hLpos : 0 < Real.log (1 / δ) := by linarith
  have hcard : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  set f : Euclidean (d + 1) → ℂ := fun y => steinFun (d + 1) δ ‖y‖ with hf
  set S : Set (Euclidean (d + 1)) :=
    ⋃ t ∈ T, radialAnnulusIcc (d + 1) (t - δ / 4) (t + δ / 4) with hS
  have hSmeas : MeasurableSet S := by
    rw [hS]
    exact Finset.measurableSet_biUnion _ fun t _ =>
      measurableSet_radialAnnulusIcc (d + 1) _ _
  -- the pointwise lower bound on `S`
  have hlarge : ∀ x ∈ S,
      ENNReal.ofReal (K * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1))) ≤ M E f x := by
    intro x hx
    obtain ⟨t, htT, hxt⟩ : ∃ t ∈ T,
        x ∈ radialAnnulusIcc (d + 1) (t - δ / 4) (t + δ / 4) := by
      rw [hS] at hx
      simpa only [Set.mem_iUnion, exists_prop] using hx
    have htE : t ∈ E := hTE htT
    have htIcc : t ∈ Icc (1 : ℝ) 2 := hE htE
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one htIcc.1
    have hclose : |‖x‖ - t| ≤ steinLower δ := by
      have hhalf : |‖x‖ - t| ≤ δ / 2 := by
        rw [radialAnnulusIcc, mem_setOf_eq, mem_Icc] at hxt
        rw [abs_le]
        exact ⟨by linarith [hxt.1], by linarith [hxt.2]⟩
      have := delta_le_steinLower hδ hδ1.le
      linarith
    have havg := le_norm_sphericalAverage_steinFun hd hδ hL htIcc.1 htIcc.2 hclose
    unfold M _root_.Spherical.restrictedSphericalMaximal
    refine le_iSup_of_le t (le_iSup_of_le ⟨htE, htpos⟩ ?_)
    exact ENNReal.ofReal_le_ofReal havg
  have hlow : ENNReal.ofReal (K * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1))) *
      volume S ^ (1 / q) ≤ eLpNorm (M E f) (ENNReal.ofReal q) volume :=
    le_eLpNorm_of_const_le_on hSmeas
      (mul_nonneg hKpos.le (Real.rpow_nonneg hLpos.le _)) hlarge hq
  -- the volume of `S`
  have hvol : ENNReal.ofReal ((T.card : ℝ) * (c1 * δ) * V) ≤ volume S := by
    have hkey : ENNReal.ofReal ((T.card : ℝ) * (c1 * δ) * V) =
        (T.card : ENNReal) *
          (ENNReal.ofReal ((3 / 4 : ℝ) ^ (d + 1 - 1) * (δ / 2)) *
            ENNReal.ofReal V) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hcard (mul_nonneg hc1pos.le hδ.le)),
        ENNReal.ofReal_mul hcard, ENNReal.ofReal_natCast, mul_assoc]
      congr 2
      rw [hc1, show d + 1 - 1 = d by omega]
      ring
    rw [hkey, ← hVeq, hS]
    exact volume_biUnion_separated_annuli_ge hd1 hδ hδ1.le
      (fun t ht => hE (hTE ht)) hsep
  -- the norm of the test function
  have hnorm : eLpNorm f (ENNReal.ofReal (((d : ℝ) + 1) / ((d : ℝ) + 1 - 1)))
      volume ≤ ENNReal.ofReal (Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1))) := by
    have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := Nat.cast_add_one d
    have hexpnn : (0 : ℝ) ≤ ((d : ℝ) + 1 - 1) / ((d : ℝ) + 1) := by
      rw [show ((d : ℝ) + 1 - 1) = (d : ℝ) by ring]
      positivity
    have hbound := eLpNorm_steinFun_lift_le (d := d + 1) (by omega) hδ hδ1
    rw [hcast] at hbound
    refine le_trans hbound (le_of_eq ?_)
    rw [hSm, ENNReal.ofReal_rpow_of_nonneg (surfaceMass_pos hd1).le hexpnn]
  -- exponent bookkeeping
  set A : ℝ := K * (c1 * V) ^ (1 / q) / Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1))
    with hA
  have hApos : 0 < A := by
    rw [hA]
    exact div_pos (mul_pos hKpos (Real.rpow_pos_of_pos (mul_pos hc1pos hVpos) _))
      (Real.rpow_pos_of_pos hSmpos _)
  have hcoefnonneg : (0 : ℝ) ≤ A * (T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) *
      Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hApos.le (Real.rpow_nonneg hcard _))
      (Real.rpow_nonneg hδ.le _)) (Real.rpow_nonneg hLpos.le _)
  have hreal : A * (T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) *
        Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1)) *
        Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1)) ≤
      K * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1)) *
        ((T.card : ℝ) * (c1 * δ) * V) ^ (1 / q) := by
    have hsplit : ((T.card : ℝ) * (c1 * δ) * V) ^ (1 / q) =
        (T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) * (c1 * V) ^ (1 / q) := by
      rw [show (T.card : ℝ) * (c1 * δ) * V = ((T.card : ℝ) * δ) * (c1 * V) by ring,
        Real.mul_rpow (mul_nonneg hcard hδ.le) (mul_nonneg hc1pos.le hVpos.le),
        Real.mul_rpow hcard hδ.le]
    have hcancel : Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1)) /
        Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1)) = 1 :=
      div_self (ne_of_gt (Real.rpow_pos_of_pos hSmpos _))
    rw [hsplit, hA]
    calc K * (c1 * V) ^ (1 / q) / Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1)) *
          (T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) *
          Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1)) *
          Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1))
        = K * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1)) *
            ((T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) * (c1 * V) ^ (1 / q)) *
            (Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1)) /
              Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1))) := by ring
      _ = K * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1)) *
            ((T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) * (c1 * V) ^ (1 / q)) := by
          rw [hcancel, mul_one]
      _ ≤ _ := le_rfl
  calc ENNReal.ofReal (A * (T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) *
          Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1))) *
        eLpNorm f (ENNReal.ofReal (((d : ℝ) + 1) / ((d : ℝ) + 1 - 1))) volume
      ≤ ENNReal.ofReal (A * (T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) *
            Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1))) *
          ENNReal.ofReal (Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1))) :=
        mul_le_mul' le_rfl hnorm
    _ = ENNReal.ofReal (A * (T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) *
          Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1)) *
          Sm ^ (((d : ℝ) + 1 - 1) / ((d : ℝ) + 1))) := by
        rw [← ENNReal.ofReal_mul hcoefnonneg]
    _ ≤ ENNReal.ofReal (K * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1)) *
          ((T.card : ℝ) * (c1 * δ) * V) ^ (1 / q)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (K * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1))) *
          ENNReal.ofReal (((T.card : ℝ) * (c1 * δ) * V) ^ (1 / q)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hKpos.le (Real.rpow_nonneg hLpos.le _))]
    _ = ENNReal.ofReal (K * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1))) *
          ENNReal.ofReal ((T.card : ℝ) * (c1 * δ) * V) ^ (1 / q) := by
        rw [ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg (mul_nonneg hcard (mul_nonneg hc1pos.le hδ.le)) hVpos.le)
          hqinv]
    _ ≤ ENNReal.ofReal (K * Real.log (1 / δ) ^ (1 / ((d : ℝ) + 1))) *
          volume S ^ (1 / q) := by
        exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hvol hqinv)
    _ ≤ eLpNorm (M E f) (ENNReal.ofReal q) volume := hlow

/-! ## The Seeger--Wainger--Wright decomposition, BRS (4.3)

For a radial function with profile `f₀`, BRS follows [SWW] and substitutes
`g(s) = f₀(s) s^{(d-1)/p}`, which turns `L^p(s^{d-1} ds)` into the unweighted
`L^p(ds)`.  The maximal operator is then dominated by a main term `𝔐_p`,
carrying the dilations `t` comparable to the radius `r`, plus two remainders
`R₁` (small dilations) and `R₂` (large dilations). -/

/-- The substitution `g(s) = f₀(s) s^{(d-1)/p}` of BRS Lemma 4.1. -/
def brsProfileSub (d : ℕ) (p : ℝ) (f₀ : ℝ → ℂ) : ℝ → ℂ :=
  fun s => ((s ^ (((d : ℝ) - 1) / p) : ℝ) : ℂ) * f₀ s

/-- The main term `𝔐_p` of BRS (4.3): the dilations comparable to the radius.
The exponent `(d-1)/p' - 1` is written with `1/p' = 1 - 1/p`. -/
def brsMainMaximal (d : ℕ) (E : Set ℝ) (p : ℝ) (g : ℝ → ℂ) (r : ℝ) : ENNReal :=
  ⨆ t ∈ E ∩ Ioo (r / 2) (3 * r / 2),
    ENNReal.ofReal (r ^ (1 - (d : ℝ)) *
      ‖∫ s in |r - t|..(r + t),
        ((s ^ (((d : ℝ) - 1) * (1 - 1 / p) - 1) : ℝ) : ℂ) * g s‖)

/-- The first remainder `R₁` of BRS (4.3): the dilations `t ≤ r/2`. -/
def brsRemainderOne (f₀ : ℝ → ℂ) (r : ℝ) : ENNReal :=
  ⨆ t ∈ Icc (1 : ℝ) 2 ∩ Iic (r / 2),
    ENNReal.ofReal (t⁻¹ * ‖∫ s in (r - t)..(r + t), f₀ s‖)

/-- The second remainder `R₂` of BRS (4.3): the dilations `t ≥ 3r/2`. -/
def brsRemainderTwo (f₀ : ℝ → ℂ) (r : ℝ) : ENNReal :=
  ⨆ t ∈ Icc (1 : ℝ) 2 ∩ Ici (3 * r / 2),
    ENNReal.ofReal (r⁻¹ * ‖∫ s in (t - r)..(t + r), f₀ s‖)

theorem brsProfileSub_apply (d : ℕ) (p : ℝ) (f₀ : ℝ → ℂ) (s : ℝ) :
    brsProfileSub d p f₀ s = ((s ^ (((d : ℝ) - 1) / p) : ℝ) : ℂ) * f₀ s := rfl

/-- Undoing the substitution: on positive radii the integrand of `𝔐_p`
applied to `g = brsProfileSub d p f₀` is `s^{d-2} f₀ s`. -/
theorem brsMainMaximal_integrand {d : ℕ} {p : ℝ} (hp : 0 < p) (f₀ : ℝ → ℂ)
    {s : ℝ} (hs : 0 < s) :
    ((s ^ (((d : ℝ) - 1) * (1 - 1 / p) - 1) : ℝ) : ℂ) *
        brsProfileSub d p f₀ s =
      ((s ^ ((d : ℝ) - 2) : ℝ) : ℂ) * f₀ s := by
  rw [brsProfileSub_apply]
  rw [show ((s ^ (((d : ℝ) - 1) * (1 - 1 / p) - 1) : ℝ) : ℂ) *
      (((s ^ (((d : ℝ) - 1) / p) : ℝ) : ℂ) * f₀ s) =
      (((s ^ (((d : ℝ) - 1) * (1 - 1 / p) - 1) * s ^ (((d : ℝ) - 1) / p) : ℝ)) : ℂ) *
        f₀ s by push_cast; ring]
  congr 2
  rw [← Real.rpow_add hs]
  congr 1
  field_simp
  ring

/-- Each of the three pieces is monotone in the profile, in the sense that a
pointwise bound on the integrands transfers.  This is the form in which the
decomposition is used. -/
theorem brsRemainderOne_le_of_le {f₀ h₀ : ℝ → ℂ} {r : ℝ}
    (h : ∀ t ∈ Icc (1 : ℝ) 2 ∩ Iic (r / 2),
      ‖∫ s in (r - t)..(r + t), f₀ s‖ ≤ ‖∫ s in (r - t)..(r + t), h₀ s‖) :
    brsRemainderOne f₀ r ≤ brsRemainderOne h₀ r := by
  refine iSup₂_mono fun t ht => ?_
  have hpos : (0 : ℝ) ≤ t⁻¹ := by
    have : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1.1
    positivity
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (h t ht) hpos)

/-- Natural powers of a positive real as real powers. -/
theorem pow_sub_eq_rpow {x : ℝ} (hx : 0 < x) {D k : ℕ} (h : k ≤ D) :
    x ^ (D - k) = x ^ ((D : ℝ) - (k : ℝ)) := by
  rw [← Real.rpow_natCast x (D - k)]
  congr 1
  push_cast [Nat.cast_sub h]
  ring

theorem brsKernel_sq_nonneg_left {t r s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ r + t) :
    (0 : ℝ) ≤ (r + t) ^ 2 - s ^ 2 := by
  have := pow_le_pow_left₀ hs0 hs2 2
  linarith

theorem brsKernel_sq_nonneg_right {t r s : ℝ} (hs1 : |r - t| ≤ s) :
    (0 : ℝ) ≤ s ^ 2 - (r - t) ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg (r - t)) hs1 2
  rw [sq_abs] at h
  linarith

/-- The product of the two square roots in the kernel (4.2) is the square root
of the product. -/
theorem brsKernel_sqrt_mul {t r s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ r + t) :
    Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) =
      Real.sqrt (((r + t) ^ 2 - s ^ 2) * (s ^ 2 - (r - t) ^ 2)) :=
  (Real.sqrt_mul (brsKernel_sq_nonneg_left hs0 hs2) _).symm

/-- **The kernel bound in the main range** `r/2 < t < 3r/2` of BRS Lemma 4.1:
the kernel is at most `C r^{1-D} s^{D-2}`. -/
theorem brsKernel_le_main {D : ℕ} (hD : 3 ≤ D) {t r s : ℝ} (hr : 0 < r)
    (ht1 : r / 2 < t) (ht2 : t < 3 * r / 2) (hs0 : 0 < s) (hs2 : s ≤ r + t) :
    brsKernel D t r s ≤ ((5 / 4 : ℝ) ^ (D - 3) / 2) *
      (r ^ (1 - (D : ℝ)) * s ^ ((D : ℝ) - 2)) := by
  have htpos : 0 < t := lt_trans (by positivity) ht1
  have h4rt : 0 < 4 * r * t := by positivity
  have h4rt2 : 2 * r ^ 2 ≤ 4 * r * t := by nlinarith
  have hrt : r + t ≤ 5 * r / 2 := by linarith
  -- the bracket
  have hsq1 : Real.sqrt ((r + t) ^ 2 - s ^ 2) ≤ r + t := by
    have h := Real.sqrt_le_sqrt
      (show (r + t) ^ 2 - s ^ 2 ≤ (r + t) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ r + t)] at h
  have hsq2 : Real.sqrt (s ^ 2 - (r - t) ^ 2) ≤ s := by
    have h := Real.sqrt_le_sqrt
      (show s ^ 2 - (r - t) ^ 2 ≤ s ^ 2 by nlinarith)
    rwa [Real.sqrt_sq hs0.le] at h
  have hnum : Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) ≤
      (5 * r / 2) * s := by
    refine mul_le_mul (le_trans hsq1 hrt) hsq2 (Real.sqrt_nonneg _) (by positivity)
  have hbracket : Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) / (4 * r * t) ≤ 5 * s / (4 * r) := by
    rw [div_le_div_iff₀ h4rt (by positivity)]
    nlinarith [Real.sqrt_nonneg ((r + t) ^ 2 - s ^ 2),
      Real.sqrt_nonneg (s ^ 2 - (r - t) ^ 2), hnum, h4rt2, hs0.le]
  have hbrnonneg : (0 : ℝ) ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) / (4 * r * t) := by positivity
  have hlast : s / (4 * r * t) ≤ s / (2 * r ^ 2) :=
    div_le_div_of_nonneg_left hs0.le (by positivity) h4rt2
  -- assemble
  have hkey : (5 * s / (4 * r)) ^ (D - 3) * (s / (2 * r ^ 2)) =
      ((5 / 4 : ℝ) ^ (D - 3) / 2) * (r ^ (1 - (D : ℝ)) * s ^ ((D : ℝ) - 2)) := by
    have hs3 : s ^ (D - 3) * s = s ^ (D - 2) := by
      rw [← pow_succ, show D - 3 + 1 = D - 2 by omega]
    have hr3 : r ^ (D - 3) * r ^ 2 = r ^ (D - 1) := by
      rw [← pow_add, show D - 3 + 2 = D - 1 by omega]
    have hsr : s ^ (D - 2) = s ^ ((D : ℝ) - 2) := by
      have := pow_sub_eq_rpow hs0 (D := D) (k := 2) (by omega)
      simpa using this
    have hrr : (r ^ (D - 1) : ℝ)⁻¹ = r ^ (1 - (D : ℝ)) := by
      have h1 : (r ^ (D - 1) : ℝ) = r ^ ((D : ℝ) - 1) := by
        have := pow_sub_eq_rpow hr (D := D) (k := 1) (by omega)
        simpa using this
      rw [h1, ← Real.rpow_neg hr.le]
      congr 1
      ring
    have hrne : r ≠ 0 := hr.ne'
    calc (5 * s / (4 * r)) ^ (D - 3) * (s / (2 * r ^ 2))
        = ((5 / 4 : ℝ) ^ (D - 3) / 2) * ((s ^ (D - 3) * s) / (r ^ (D - 3) * r ^ 2)) := by
          rw [show (5 * s / (4 * r) : ℝ) = (5 / 4) * (s / r) by ring, mul_pow, div_pow]
          ring
      _ = ((5 / 4 : ℝ) ^ (D - 3) / 2) * (s ^ (D - 2) / r ^ (D - 1)) := by
          rw [hs3, hr3]
      _ = ((5 / 4 : ℝ) ^ (D - 3) / 2) * (r ^ (1 - (D : ℝ)) * s ^ ((D : ℝ) - 2)) := by
          rw [← hrr, ← hsr]
          field_simp
  rw [brsKernel_eq_of_pos, ← hkey]
  refine mul_le_mul ?_ hlast (by positivity) (by positivity)
  exact pow_le_pow_left₀ hbrnonneg hbracket _

/-- **The kernel bound for small dilations** `t ≤ r/2` of BRS Lemma 4.1. -/
theorem brsKernel_le_small {D : ℕ} (hD : 3 ≤ D) {t r s : ℝ} (htpos : 0 < t)
    (ht : t ≤ r / 2) (hs1 : r - t ≤ s) (hs2 : s ≤ r + t) :
    brsKernel D t r s ≤ (3 * (5 / 4 : ℝ) ^ (D - 3) / 8) * t⁻¹ := by
  have hr : 0 < r := by linarith
  have h4rt : 0 < 4 * r * t := by positivity
  have hs0 : 0 ≤ s := by linarith
  have habs : |r - t| ≤ s := by
    rw [abs_le]
    constructor <;> linarith
  -- the bracket is bounded by 5/4
  have hprod : ((r + t) ^ 2 - s ^ 2) * (s ^ 2 - (r - t) ^ 2) ≤ (5 * t * r) ^ 2 := by
    have h1 : (r + t) ^ 2 - s ^ 2 = (r + t - s) * (r + t + s) := by ring
    have h2 : s ^ 2 - (r - t) ^ 2 = (s - r + t) * (s + r - t) := by ring
    have hb1 : r + t - s ≤ 2 * t := by linarith
    have hb2 : r + t + s ≤ 3 * r := by linarith
    have hb3 : s - r + t ≤ 2 * t := by linarith
    have hb4 : s + r - t ≤ 2 * r := by linarith
    have hn1 : 0 ≤ r + t - s := by linarith
    have hn2 : 0 ≤ s - r + t := by linarith
    have hn3 : 0 ≤ r + t + s := by linarith
    have hn4 : 0 ≤ s + r - t := by linarith
    have hAB : (r + t - s) * (r + t + s) ≤ 2 * t * (3 * r) :=
      mul_le_mul hb1 hb2 hn3 (by positivity)
    have hCD : (s - r + t) * (s + r - t) ≤ 2 * t * (2 * r) :=
      mul_le_mul hb3 hb4 hn4 (by positivity)
    rw [h1, h2]
    calc (r + t - s) * (r + t + s) * ((s - r + t) * (s + r - t))
        ≤ (2 * t * (3 * r)) * (2 * t * (2 * r)) :=
          mul_le_mul hAB hCD (mul_nonneg hn2 hn4) (by positivity)
      _ ≤ (5 * t * r) ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (((r + t) ^ 2 - s ^ 2) * (s ^ 2 - (r - t) ^ 2)) ≤
      5 * t * r := by
    have h := Real.sqrt_le_sqrt hprod
    rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 5 * t * r)] at h
  have hbracket : Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) / (4 * r * t) ≤ 5 / 4 := by
    rw [brsKernel_sqrt_mul hs0 hs2, div_le_iff₀ h4rt]
    nlinarith [hsqrt]
  have hbrnonneg : (0 : ℝ) ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) / (4 * r * t) := by positivity
  have hlast : s / (4 * r * t) ≤ 3 / 8 * t⁻¹ := by
    have hcalc : 3 / 8 * t⁻¹ * (4 * r * t) = 3 * r / 2 := by
      field_simp
      ring
    rw [div_le_iff₀ h4rt, hcalc]
    linarith
  rw [brsKernel_eq_of_pos]
  calc (Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) /
        (4 * r * t)) ^ (D - 3) * (s / (4 * r * t))
      ≤ (5 / 4 : ℝ) ^ (D - 3) * (3 / 8 * t⁻¹) := by
        refine mul_le_mul (pow_le_pow_left₀ hbrnonneg hbracket _) hlast
          (by positivity) (by positivity)
    _ = (3 * (5 / 4 : ℝ) ^ (D - 3) / 8) * t⁻¹ := by ring

/-- **The kernel bound for large dilations** `t ≥ 3r/2` of BRS Lemma 4.1. -/
theorem brsKernel_le_large {D : ℕ} (hD : 3 ≤ D) {t r s : ℝ} (hr : 0 < r)
    (ht : 3 * r / 2 ≤ t) (hs1 : t - r ≤ s) (hs2 : s ≤ t + r) :
    brsKernel D t r s ≤ (5 * (3 / 2 : ℝ) ^ (D - 3) / 12) * r⁻¹ := by
  have htpos : 0 < t := by linarith
  have h4rt : 0 < 4 * r * t := by positivity
  have hs0 : 0 ≤ s := by linarith
  have hs2' : s ≤ r + t := by linarith
  have habs : |r - t| ≤ s := by
    rw [abs_le]
    constructor <;> linarith
  have hprod : ((r + t) ^ 2 - s ^ 2) * (s ^ 2 - (r - t) ^ 2) ≤ (6 * r * t) ^ 2 := by
    have h1 : (r + t) ^ 2 - s ^ 2 = (r + t - s) * (r + t + s) := by ring
    have h2 : s ^ 2 - (r - t) ^ 2 = (s - t + r) * (s + t - r) := by ring
    have hb1 : r + t - s ≤ 2 * r := by linarith
    have hb2 : r + t + s ≤ 4 * t := by linarith
    have hb3 : s - t + r ≤ 2 * r := by linarith
    have hb4 : s + t - r ≤ 2 * t := by linarith
    have hn1 : 0 ≤ r + t - s := by linarith
    have hn2 : 0 ≤ s - t + r := by linarith
    have hn3 : 0 ≤ r + t + s := by linarith
    have hn4 : 0 ≤ s + t - r := by linarith
    have hAB : (r + t - s) * (r + t + s) ≤ 2 * r * (4 * t) :=
      mul_le_mul hb1 hb2 hn3 (by positivity)
    have hCD : (s - t + r) * (s + t - r) ≤ 2 * r * (2 * t) :=
      mul_le_mul hb3 hb4 hn4 (by positivity)
    rw [h1, h2]
    calc (r + t - s) * (r + t + s) * ((s - t + r) * (s + t - r))
        ≤ (2 * r * (4 * t)) * (2 * r * (2 * t)) :=
          mul_le_mul hAB hCD (mul_nonneg hn2 hn4) (by positivity)
      _ ≤ (6 * r * t) ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (((r + t) ^ 2 - s ^ 2) * (s ^ 2 - (r - t) ^ 2)) ≤
      6 * r * t := by
    have h := Real.sqrt_le_sqrt hprod
    rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 6 * r * t)] at h
  have hbracket : Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) / (4 * r * t) ≤ 3 / 2 := by
    rw [brsKernel_sqrt_mul hs0 hs2', div_le_iff₀ h4rt]
    nlinarith [hsqrt]
  have hbrnonneg : (0 : ℝ) ≤ Real.sqrt ((r + t) ^ 2 - s ^ 2) *
      Real.sqrt (s ^ 2 - (r - t) ^ 2) / (4 * r * t) := by positivity
  have hlast : s / (4 * r * t) ≤ 5 / 12 * r⁻¹ := by
    have hcalc : 5 / 12 * r⁻¹ * (4 * r * t) = 5 * t / 3 := by
      field_simp
      ring
    rw [div_le_iff₀ h4rt, hcalc]
    linarith
  rw [brsKernel_eq_of_pos]
  calc (Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) /
        (4 * r * t)) ^ (D - 3) * (s / (4 * r * t))
      ≤ (3 / 2 : ℝ) ^ (D - 3) * (5 / 12 * r⁻¹) := by
        refine mul_le_mul (pow_le_pow_left₀ hbrnonneg hbracket _) hlast
          (by positivity) (by positivity)
    _ = (5 * (3 / 2 : ℝ) ^ (D - 3) / 12) * r⁻¹ := by ring

/-- The pointwise modulus of a profile, as a complex-valued profile.  The
decomposition of BRS Lemma 4.1 is applied to it; this changes no `L^p` norm. -/
def absProfile (f₀ : ℝ → ℂ) : ℝ → ℂ := fun s => ((‖f₀ s‖ : ℝ) : ℂ)

theorem continuous_absProfile {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) :
    Continuous (absProfile f₀) :=
  Complex.continuous_ofReal.comp hf₀.norm

theorem norm_absProfile (f₀ : ℝ → ℂ) (s : ℝ) : ‖absProfile f₀ s‖ = ‖f₀ s‖ := by
  rw [absProfile, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

/-- The main-range kernel bound, extended to `s = 0`. -/
theorem brsKernel_le_main' {D : ℕ} (hD : 3 ≤ D) {t r s : ℝ} (hr : 0 < r)
    (ht1 : r / 2 < t) (ht2 : t < 3 * r / 2) (hs0 : 0 ≤ s) (hs2 : s ≤ r + t) :
    brsKernel D t r s ≤ ((5 / 4 : ℝ) ^ (D - 3) / 2) *
      (r ^ (1 - (D : ℝ)) * s ^ ((D : ℝ) - 2)) := by
  rcases eq_or_lt_of_le hs0 with h | h
  · have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    have hexp : ((D : ℝ) - 2) ≠ 0 := by
      intro hcon
      linarith [hcon]
    have hzero : brsKernel D t r s = 0 := by
      rw [brsKernel, ← h]
      simp
    rw [hzero, ← h, Real.zero_rpow hexp]
    positivity
  · exact brsKernel_le_main hD hr ht1 ht2 h hs2

/-- Undoing the substitution `g = f₀ s^{(d-1)/p}`, valid also at `s = 0`. -/
theorem brsMainMaximal_integrand_nonneg {D : ℕ} (hD : 3 ≤ D) {p : ℝ} (hp : 0 < p)
    (f₀ : ℝ → ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ((s ^ (((D : ℝ) - 1) * (1 - 1 / p) - 1) : ℝ) : ℂ) * brsProfileSub D p f₀ s =
      ((s ^ ((D : ℝ) - 2) : ℝ) : ℂ) * f₀ s := by
  rcases eq_or_lt_of_le hs with h | h
  · have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    have hexp1 : (((D : ℝ) - 1) / p) ≠ 0 := by
      have : (0 : ℝ) < ((D : ℝ) - 1) / p := by
        apply div_pos <;> linarith
      exact this.ne'
    have hexp2 : ((D : ℝ) - 2) ≠ 0 := by
      intro hcon
      linarith [hcon]
    rw [brsProfileSub, ← h, Real.zero_rpow hexp1, Real.zero_rpow hexp2]
    simp
  · exact brsMainMaximal_integrand hp f₀ h

/-- The norm of the integral of a nonnegative real integrand. -/
theorem norm_intervalIntegral_ofReal_nonneg {a b : ℝ} (hab : a ≤ b) (h : ℝ → ℝ)
    (hnn : ∀ s ∈ Icc a b, 0 ≤ h s) :
    ‖∫ s in a..b, ((h s : ℝ) : ℂ)‖ = ∫ s in a..b, h s := by
  rw [intervalIntegral.integral_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (intervalIntegral.integral_nonneg hab hnn)]

/-- The spherical average of a radial function is dominated by the kernel
integral of the modulus of its profile. -/
theorem norm_sphericalAverage_le_kernel_integral {d : ℕ} (hd : 2 ≤ d) (f₀ : ℝ → ℂ)
    (hf₀ : Continuous f₀) {x : Euclidean (d + 1)} (hx : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖ ≤
      ((surfaceMass (d + 1))⁻¹ * surfaceMass d * ((4 : ℝ) * 2 ^ (d - 2))) *
        ∫ s in |‖x‖ - t|..(‖x‖ + t), brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hCpos : (0 : ℝ) <
      (surfaceMass (d + 1))⁻¹ * surfaceMass d * ((4 : ℝ) * 2 ^ (d - 2)) := by
    have h1 : 0 < surfaceMass d := surfaceMass_pos (by omega)
    have h2 : 0 < surfaceMass (d + 1) := surfaceMass_pos (by omega)
    positivity
  have hab : |‖x‖ - t| ≤ ‖x‖ + t := by
    rw [abs_le]
    constructor <;> linarith
  have h4rt : 0 < 4 * ‖x‖ * t := by positivity
  rw [sphericalAverage_eq_kernel_integral hd f₀ hf₀ hx ht, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hCpos.le]
  refine mul_le_mul_of_nonneg_left ?_ hCpos.le
  calc ‖∫ s in |‖x‖ - t|..(‖x‖ + t),
        ((brsKernel (d + 1) t ‖x‖ s : ℝ)) • f₀ s‖
      ≤ ∫ s in |‖x‖ - t|..(‖x‖ + t),
          ‖((brsKernel (d + 1) t ‖x‖ s : ℝ)) • f₀ s‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ s in |‖x‖ - t|..(‖x‖ + t), brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖ := by
        refine intervalIntegral.integral_congr ?_
        intro s hs
        rw [Set.uIcc_of_le hab] at hs
        have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hs.1
        simp only []
        rw [norm_smul, Real.norm_of_nonneg (brsKernel_nonneg (d + 1) h4rt hs0)]

theorem continuous_rpow_const_of_nonneg {c : ℝ} (hc : 0 ≤ c) :
    Continuous fun s : ℝ => s ^ c :=
  continuous_iff_continuousAt.mpr fun x => Real.continuousAt_rpow_const x c (Or.inr hc)

/-- The constant of the spherical-average kernel representation. -/
def brsAvgConst (d : ℕ) : ℝ :=
  (surfaceMass (d + 1))⁻¹ * surfaceMass d * ((4 : ℝ) * 2 ^ (d - 2))

theorem brsAvgConst_pos {d : ℕ} (hd : 2 ≤ d) : 0 < brsAvgConst d := by
  have h1 : 0 < surfaceMass d := surfaceMass_pos (by omega)
  have h2 : 0 < surfaceMass (d + 1) := surfaceMass_pos (by omega)
  rw [brsAvgConst]
  positivity

/-- **The main-range estimate of BRS Lemma 4.1.**  For a dilation `t ∈ E`
comparable to the radius, the spherical average is dominated by `𝔐_p`. -/
theorem le_brsMainMaximal_of_mem {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ} {p : ℝ}
    (hp : 0 < p) (f₀ : ℝ → ℂ) (hf₀ : Continuous f₀) {x : Euclidean (d + 1)}
    (hx : x ≠ 0) {t : ℝ} (htE : t ∈ E) (ht1 : ‖x‖ / 2 < t) (ht2 : t < 3 * ‖x‖ / 2) :
    ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖ ≤
      ENNReal.ofReal (brsAvgConst d * ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2)) *
        brsMainMaximal (d + 1) E p
          (brsProfileSub (d + 1) p (absProfile f₀)) ‖x‖ := by
  have hD : 3 ≤ d + 1 := by omega
  have hDR : (3 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    push_cast
    linarith
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have htpos : 0 < t := lt_trans (by positivity) ht1
  have hab : |‖x‖ - t| ≤ ‖x‖ + t := by
    rw [abs_le]
    constructor <;> linarith
  have h4rt : 0 < 4 * ‖x‖ * t := by positivity
  have hexpnn : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) - 2 := by linarith
  have hCpos : 0 < brsAvgConst d := brsAvgConst_pos hd
  have hconstpos : (0 : ℝ) < (5 / 4 : ℝ) ^ (d + 1 - 3) / 2 := by positivity
  -- integrability of the two integrands
  have hcont1 : Continuous fun s : ℝ => brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖ :=
    (continuous_brsKernel (d + 1) h4rt).mul hf₀.norm
  have hcont2 : Continuous fun s : ℝ =>
      ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2) *
        (‖x‖ ^ (1 - ((d + 1 : ℕ) : ℝ)) * s ^ (((d + 1 : ℕ) : ℝ) - 2)) * ‖f₀ s‖ :=
    ((continuous_const.mul (continuous_const.mul
      (continuous_rpow_const_of_nonneg hexpnn))).mul hf₀.norm)
  -- the kernel bound, integrated
  have hmono : (∫ s in |‖x‖ - t|..(‖x‖ + t), brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖) ≤
      ∫ s in |‖x‖ - t|..(‖x‖ + t),
        ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2) *
          (‖x‖ ^ (1 - ((d + 1 : ℕ) : ℝ)) * s ^ (((d + 1 : ℕ) : ℝ) - 2)) * ‖f₀ s‖ := by
    refine intervalIntegral.integral_mono_on hab (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _) ?_
    intro s hs
    have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hs.1
    exact mul_le_mul_of_nonneg_right
      (brsKernel_le_main' (D := d + 1) hD hr ht1 ht2 hs0 hs.2) (norm_nonneg _)
  have hpull : (∫ s in |‖x‖ - t|..(‖x‖ + t),
        ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2) *
          (‖x‖ ^ (1 - ((d + 1 : ℕ) : ℝ)) * s ^ (((d + 1 : ℕ) : ℝ) - 2)) * ‖f₀ s‖) =
      ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2) *
        (‖x‖ ^ (1 - ((d + 1 : ℕ) : ℝ)) *
          ∫ s in |‖x‖ - t|..(‖x‖ + t),
            s ^ (((d + 1 : ℕ) : ℝ) - 2) * ‖f₀ s‖) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro s hs
    simp only []
    ring
  -- the term of `𝔐_p` at this `t`
  have hMterm : ‖∫ s in |‖x‖ - t|..(‖x‖ + t),
        ((s ^ ((((d + 1 : ℕ) : ℝ) - 1) * (1 - 1 / p) - 1) : ℝ) : ℂ) *
          brsProfileSub (d + 1) p (absProfile f₀) s‖ =
      ∫ s in |‖x‖ - t|..(‖x‖ + t), s ^ (((d + 1 : ℕ) : ℝ) - 2) * ‖f₀ s‖ := by
    have hcongr : (∫ s in |‖x‖ - t|..(‖x‖ + t),
          ((s ^ ((((d + 1 : ℕ) : ℝ) - 1) * (1 - 1 / p) - 1) : ℝ) : ℂ) *
            brsProfileSub (d + 1) p (absProfile f₀) s) =
        ∫ s in |‖x‖ - t|..(‖x‖ + t),
          ((s ^ (((d + 1 : ℕ) : ℝ) - 2) * ‖f₀ s‖ : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr ?_
      intro s hs
      rw [Set.uIcc_of_le hab] at hs
      have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hs.1
      simp only []
      rw [brsMainMaximal_integrand_nonneg hD hp (absProfile f₀) hs0, absProfile]
      push_cast
      ring
    rw [hcongr]
    refine norm_intervalIntegral_ofReal_nonneg hab _ ?_
    intro s hs
    have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hs.1
    have : (0 : ℝ) ≤ s ^ (((d + 1 : ℕ) : ℝ) - 2) := Real.rpow_nonneg hs0 _
    positivity
  -- the real-valued chain
  have hchain : ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖ ≤
      (brsAvgConst d * ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2)) *
        (‖x‖ ^ (1 - ((d + 1 : ℕ) : ℝ)) *
          ∫ s in |‖x‖ - t|..(‖x‖ + t),
            s ^ (((d + 1 : ℕ) : ℝ) - 2) * ‖f₀ s‖) := by
    have h1 := norm_sphericalAverage_le_kernel_integral hd f₀ hf₀ hx htpos
    rw [← brsAvgConst] at h1
    calc ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖
        ≤ brsAvgConst d *
            ∫ s in |‖x‖ - t|..(‖x‖ + t), brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖ := h1
      _ ≤ brsAvgConst d *
            ∫ s in |‖x‖ - t|..(‖x‖ + t),
              ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2) *
                (‖x‖ ^ (1 - ((d + 1 : ℕ) : ℝ)) *
                  s ^ (((d + 1 : ℕ) : ℝ) - 2)) * ‖f₀ s‖ :=
          mul_le_mul_of_nonneg_left hmono hCpos.le
      _ = (brsAvgConst d * ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2)) *
            (‖x‖ ^ (1 - ((d + 1 : ℕ) : ℝ)) *
              ∫ s in |‖x‖ - t|..(‖x‖ + t),
                s ^ (((d + 1 : ℕ) : ℝ) - 2) * ‖f₀ s‖) := by
          rw [hpull]
          ring
  -- conclude
  have hnonneg : (0 : ℝ) ≤ ‖x‖ ^ (1 - ((d + 1 : ℕ) : ℝ)) *
      ∫ s in |‖x‖ - t|..(‖x‖ + t), s ^ (((d + 1 : ℕ) : ℝ) - 2) * ‖f₀ s‖ := by
    refine mul_nonneg (Real.rpow_nonneg hr.le _) ?_
    refine intervalIntegral.integral_nonneg hab ?_
    intro s hs
    have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hs.1
    have : (0 : ℝ) ≤ s ^ (((d + 1 : ℕ) : ℝ) - 2) := Real.rpow_nonneg hs0 _
    positivity
  calc ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖
      ≤ ENNReal.ofReal ((brsAvgConst d * ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2)) *
          (‖x‖ ^ (1 - ((d + 1 : ℕ) : ℝ)) *
            ∫ s in |‖x‖ - t|..(‖x‖ + t),
              s ^ (((d + 1 : ℕ) : ℝ) - 2) * ‖f₀ s‖)) :=
        ENNReal.ofReal_le_ofReal hchain
    _ = ENNReal.ofReal (brsAvgConst d * ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2)) *
          ENNReal.ofReal (‖x‖ ^ (1 - ((d + 1 : ℕ) : ℝ)) *
            ∫ s in |‖x‖ - t|..(‖x‖ + t),
              s ^ (((d + 1 : ℕ) : ℝ) - 2) * ‖f₀ s‖) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (brsAvgConst d * ((5 / 4 : ℝ) ^ (d + 1 - 3) / 2)) *
          brsMainMaximal (d + 1) E p
            (brsProfileSub (d + 1) p (absProfile f₀)) ‖x‖ := by
        refine mul_le_mul' le_rfl ?_
        refine le_iSup₂_of_le t ⟨htE, ht1, ht2⟩ ?_
        rw [hMterm]

/-- **The small-dilation estimate of BRS Lemma 4.1**: for `t ≤ r/2` the
spherical average is dominated by `R₁`. -/
theorem le_brsRemainderOne_of_le {d : ℕ} (hd : 2 ≤ d) (f₀ : ℝ → ℂ)
    (hf₀ : Continuous f₀) {x : Euclidean (d + 1)} (hx : x ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) 2) (htr : t ≤ ‖x‖ / 2) :
    ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖ ≤
      ENNReal.ofReal (brsAvgConst d * (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8)) *
        brsRemainderOne (absProfile f₀) ‖x‖ := by
  have hD : 3 ≤ d + 1 := by omega
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hrt : t ≤ ‖x‖ / 2 := htr
  have habs : |‖x‖ - t| = ‖x‖ - t := abs_of_nonneg (by linarith)
  have hab : ‖x‖ - t ≤ ‖x‖ + t := by linarith
  have h4rt : 0 < 4 * ‖x‖ * t := by positivity
  have hCpos : 0 < brsAvgConst d := brsAvgConst_pos hd
  have hconstpos : (0 : ℝ) < 3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8 := by positivity
  have hcont1 : Continuous fun s : ℝ => brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖ :=
    (continuous_brsKernel (d + 1) h4rt).mul hf₀.norm
  have hcont2 : Continuous fun s : ℝ =>
      (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8) * t⁻¹ * ‖f₀ s‖ :=
    continuous_const.mul hf₀.norm
  have hmono : (∫ s in (‖x‖ - t)..(‖x‖ + t),
        brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖) ≤
      ∫ s in (‖x‖ - t)..(‖x‖ + t),
        (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8) * t⁻¹ * ‖f₀ s‖ := by
    refine intervalIntegral.integral_mono_on hab (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _) ?_
    intro s hs
    exact mul_le_mul_of_nonneg_right
      (brsKernel_le_small (D := d + 1) hD htpos hrt hs.1 hs.2) (norm_nonneg _)
  have hpull : (∫ s in (‖x‖ - t)..(‖x‖ + t),
        (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8) * t⁻¹ * ‖f₀ s‖) =
      (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8) *
        (t⁻¹ * ∫ s in (‖x‖ - t)..(‖x‖ + t), ‖f₀ s‖) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro s hs
    simp only []
    ring
  have hRterm : ‖∫ s in (‖x‖ - t)..(‖x‖ + t), absProfile f₀ s‖ =
      ∫ s in (‖x‖ - t)..(‖x‖ + t), ‖f₀ s‖ := by
    have : (fun s : ℝ => absProfile f₀ s) = fun s : ℝ => ((‖f₀ s‖ : ℝ) : ℂ) := rfl
    rw [this]
    exact norm_intervalIntegral_ofReal_nonneg hab _ fun s _ => norm_nonneg _
  have hchain : ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖ ≤
      (brsAvgConst d * (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8)) *
        (t⁻¹ * ∫ s in (‖x‖ - t)..(‖x‖ + t), ‖f₀ s‖) := by
    have h1 := norm_sphericalAverage_le_kernel_integral hd f₀ hf₀ hx htpos
    rw [← brsAvgConst, habs] at h1
    calc ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖
        ≤ brsAvgConst d *
            ∫ s in (‖x‖ - t)..(‖x‖ + t), brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖ := h1
      _ ≤ brsAvgConst d *
            ∫ s in (‖x‖ - t)..(‖x‖ + t),
              (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8) * t⁻¹ * ‖f₀ s‖ :=
          mul_le_mul_of_nonneg_left hmono hCpos.le
      _ = (brsAvgConst d * (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8)) *
            (t⁻¹ * ∫ s in (‖x‖ - t)..(‖x‖ + t), ‖f₀ s‖) := by
          rw [hpull]
          ring
  have hnonneg : (0 : ℝ) ≤ t⁻¹ * ∫ s in (‖x‖ - t)..(‖x‖ + t), ‖f₀ s‖ := by
    refine mul_nonneg (by positivity) ?_
    exact intervalIntegral.integral_nonneg hab fun s _ => norm_nonneg _
  calc ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖
      ≤ ENNReal.ofReal ((brsAvgConst d * (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8)) *
          (t⁻¹ * ∫ s in (‖x‖ - t)..(‖x‖ + t), ‖f₀ s‖)) :=
        ENNReal.ofReal_le_ofReal hchain
    _ = ENNReal.ofReal (brsAvgConst d * (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8)) *
          ENNReal.ofReal (t⁻¹ * ∫ s in (‖x‖ - t)..(‖x‖ + t), ‖f₀ s‖) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (brsAvgConst d * (3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8)) *
          brsRemainderOne (absProfile f₀) ‖x‖ := by
        refine mul_le_mul' le_rfl ?_
        refine le_iSup₂_of_le t ⟨ht, htr⟩ ?_
        rw [hRterm]

/-- **The large-dilation estimate of BRS Lemma 4.1**: for `t ≥ 3r/2` the
spherical average is dominated by `R₂`. -/
theorem le_brsRemainderTwo_of_le {d : ℕ} (hd : 2 ≤ d) (f₀ : ℝ → ℂ)
    (hf₀ : Continuous f₀) {x : Euclidean (d + 1)} (hx : x ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) 2) (htr : 3 * ‖x‖ / 2 ≤ t) :
    ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖ ≤
      ENNReal.ofReal (brsAvgConst d * (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12)) *
        brsRemainderTwo (absProfile f₀) ‖x‖ := by
  have hD : 3 ≤ d + 1 := by omega
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have habs : |‖x‖ - t| = t - ‖x‖ := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have hab : t - ‖x‖ ≤ t + ‖x‖ := by linarith
  have hsum : ‖x‖ + t = t + ‖x‖ := by ring
  have h4rt : 0 < 4 * ‖x‖ * t := by positivity
  have hCpos : 0 < brsAvgConst d := brsAvgConst_pos hd
  have hcont1 : Continuous fun s : ℝ => brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖ :=
    (continuous_brsKernel (d + 1) h4rt).mul hf₀.norm
  have hcont2 : Continuous fun s : ℝ =>
      (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12) * ‖x‖⁻¹ * ‖f₀ s‖ :=
    continuous_const.mul hf₀.norm
  have hmono : (∫ s in (t - ‖x‖)..(t + ‖x‖),
        brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖) ≤
      ∫ s in (t - ‖x‖)..(t + ‖x‖),
        (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12) * ‖x‖⁻¹ * ‖f₀ s‖ := by
    refine intervalIntegral.integral_mono_on hab (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _) ?_
    intro s hs
    exact mul_le_mul_of_nonneg_right
      (brsKernel_le_large (D := d + 1) hD hr htr hs.1 hs.2) (norm_nonneg _)
  have hpull : (∫ s in (t - ‖x‖)..(t + ‖x‖),
        (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12) * ‖x‖⁻¹ * ‖f₀ s‖) =
      (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12) *
        (‖x‖⁻¹ * ∫ s in (t - ‖x‖)..(t + ‖x‖), ‖f₀ s‖) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro s hs
    simp only []
    ring
  have hRterm : ‖∫ s in (t - ‖x‖)..(t + ‖x‖), absProfile f₀ s‖ =
      ∫ s in (t - ‖x‖)..(t + ‖x‖), ‖f₀ s‖ := by
    have h : (fun s : ℝ => absProfile f₀ s) = fun s : ℝ => ((‖f₀ s‖ : ℝ) : ℂ) := rfl
    rw [h]
    exact norm_intervalIntegral_ofReal_nonneg hab _ fun s _ => norm_nonneg _
  have hchain : ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖ ≤
      (brsAvgConst d * (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12)) *
        (‖x‖⁻¹ * ∫ s in (t - ‖x‖)..(t + ‖x‖), ‖f₀ s‖) := by
    have h1 := norm_sphericalAverage_le_kernel_integral hd f₀ hf₀ hx htpos
    rw [← brsAvgConst, habs, hsum] at h1
    calc ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖
        ≤ brsAvgConst d *
            ∫ s in (t - ‖x‖)..(t + ‖x‖), brsKernel (d + 1) t ‖x‖ s * ‖f₀ s‖ := h1
      _ ≤ brsAvgConst d *
            ∫ s in (t - ‖x‖)..(t + ‖x‖),
              (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12) * ‖x‖⁻¹ * ‖f₀ s‖ :=
          mul_le_mul_of_nonneg_left hmono hCpos.le
      _ = (brsAvgConst d * (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12)) *
            (‖x‖⁻¹ * ∫ s in (t - ‖x‖)..(t + ‖x‖), ‖f₀ s‖) := by
          rw [hpull]
          ring
  have hnonneg : (0 : ℝ) ≤ ‖x‖⁻¹ * ∫ s in (t - ‖x‖)..(t + ‖x‖), ‖f₀ s‖ := by
    refine mul_nonneg (by positivity) ?_
    exact intervalIntegral.integral_nonneg hab fun s _ => norm_nonneg _
  calc ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖
      ≤ ENNReal.ofReal ((brsAvgConst d * (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12)) *
          (‖x‖⁻¹ * ∫ s in (t - ‖x‖)..(t + ‖x‖), ‖f₀ s‖)) :=
        ENNReal.ofReal_le_ofReal hchain
    _ = ENNReal.ofReal (brsAvgConst d * (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12)) *
          ENNReal.ofReal (‖x‖⁻¹ * ∫ s in (t - ‖x‖)..(t + ‖x‖), ‖f₀ s‖) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (brsAvgConst d * (5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12)) *
          brsRemainderTwo (absProfile f₀) ‖x‖ := by
        refine mul_le_mul' le_rfl ?_
        refine le_iSup₂_of_le t ⟨ht, htr⟩ ?_
        rw [hRterm]

/-- **BRS Lemma 4.1** (Seeger--Wainger--Wright decomposition).  For `d + 1 ≥ 3`
and a continuous profile `f₀`, the spherical maximal function of the radial
function `f(y) = f₀(‖y‖)` is dominated pointwise by the sum of the main term
`𝔐_p`, applied to the substituted profile of `|f₀|`, and the two remainders
`R₁`, `R₂` applied to `|f₀|`. -/
theorem le_brsDecomposition {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f₀ : ℝ → ℂ, Continuous f₀ →
      ∀ x : Euclidean (d + 1), x ≠ 0 →
        M E (fun y => f₀ ‖y‖) x ≤ ENNReal.ofReal C *
          (brsMainMaximal (d + 1) E p
              (brsProfileSub (d + 1) p (absProfile f₀)) ‖x‖ +
            brsRemainderOne (absProfile f₀) ‖x‖ +
            brsRemainderTwo (absProfile f₀) ‖x‖) := by
  have hCpos : 0 < brsAvgConst d := brsAvgConst_pos hd
  set c1 : ℝ := (5 / 4 : ℝ) ^ (d + 1 - 3) / 2 with hc1
  set c2 : ℝ := 3 * (5 / 4 : ℝ) ^ (d + 1 - 3) / 8 with hc2
  set c3 : ℝ := 5 * (3 / 2 : ℝ) ^ (d + 1 - 3) / 12 with hc3
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  have hc2pos : 0 < c2 := by rw [hc2]; positivity
  have hc3pos : 0 < c3 := by rw [hc3]; positivity
  refine ⟨brsAvgConst d * (c1 + c2 + c3), by positivity, ?_⟩
  intro f₀ hf₀ x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set A : ENNReal := brsMainMaximal (d + 1) E p
    (brsProfileSub (d + 1) p (absProfile f₀)) ‖x‖ with hA
  set B : ENNReal := brsRemainderOne (absProfile f₀) ‖x‖ with hB
  set C : ENNReal := brsRemainderTwo (absProfile f₀) ‖x‖ with hC
  have hmono1 : ENNReal.ofReal (brsAvgConst d * c1) * A ≤
      ENNReal.ofReal (brsAvgConst d * (c1 + c2 + c3)) * (A + B + C) := by
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ?_
    · have : c1 ≤ c1 + c2 + c3 := by linarith
      exact mul_le_mul_of_nonneg_left this hCpos.le
    · exact le_trans (le_add_right le_rfl) (le_add_right le_rfl)
  have hmono2 : ENNReal.ofReal (brsAvgConst d * c2) * B ≤
      ENNReal.ofReal (brsAvgConst d * (c1 + c2 + c3)) * (A + B + C) := by
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ?_
    · have : c2 ≤ c1 + c2 + c3 := by linarith
      exact mul_le_mul_of_nonneg_left this hCpos.le
    · exact le_trans (le_add_left le_rfl) (le_add_right le_rfl)
  have hmono3 : ENNReal.ofReal (brsAvgConst d * c3) * C ≤
      ENNReal.ofReal (brsAvgConst d * (c1 + c2 + c3)) * (A + B + C) := by
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ?_
    · have : c3 ≤ c1 + c2 + c3 := by linarith
      exact mul_le_mul_of_nonneg_left this hCpos.le
    · exact le_add_left le_rfl
  unfold M _root_.Spherical.restrictedSphericalMaximal
  refine iSup₂_le fun t ht => ?_
  have htE : t ∈ E := ht.1
  have htIcc : t ∈ Icc (1 : ℝ) 2 := hE htE
  by_cases hsmall : t ≤ ‖x‖ / 2
  · refine le_trans ?_ hmono2
    rw [hB, hc2]
    exact le_brsRemainderOne_of_le hd f₀ hf₀ hx htIcc hsmall
  · push Not at hsmall
    by_cases hlarge : 3 * ‖x‖ / 2 ≤ t
    · refine le_trans ?_ hmono3
      rw [hC, hc3]
      exact le_brsRemainderTwo_of_le hd f₀ hf₀ hx htIcc hlarge
    · push Not at hlarge
      refine le_trans ?_ hmono1
      rw [hA, hc1]
      exact le_brsMainMaximal_of_mem hd hp f₀ hf₀ hx htE hsmall hlarge

/-- Enlarging the interval of integration of a nonnegative continuous
integrand. -/
theorem intervalIntegral_mono_subinterval {h : ℝ → ℝ} (hh : Continuous h)
    (hnn : ∀ s, 0 ≤ h s) {a b u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    (∫ s in u..v, h s) ≤ ∫ s in a..b, h s := by
  have hint : ∀ c e : ℝ, IntervalIntegrable h volume c e := fun c e =>
    hh.intervalIntegrable c e
  have hsplit1 : (∫ s in a..u, h s) + (∫ s in u..b, h s) = ∫ s in a..b, h s :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hsplit2 : (∫ s in u..v, h s) + (∫ s in v..b, h s) = ∫ s in u..b, h s :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hpos1 : 0 ≤ ∫ s in a..u, h s :=
    intervalIntegral.integral_nonneg hau fun s _ => hnn s
  have hpos2 : 0 ≤ ∫ s in v..b, h s :=
    intervalIntegral.integral_nonneg hvb fun s _ => hnn s
  linarith [hsplit1, hsplit2]

/-- **The elementary bound for `R₁`.**  Since `1 ≤ t ≤ r/2`, the interval of
integration lies in the window `[r/2, 3r/2]` and the factor `t⁻¹` is at most
one, so `R₁` is dominated by the window average of `|f₀|`. -/
theorem brsRemainderOne_le_window {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) (r : ℝ) :
    brsRemainderOne (absProfile f₀) r ≤
      ENNReal.ofReal (∫ s in (r / 2)..(3 * r / 2), ‖f₀ s‖) := by
  refine iSup₂_le fun t ht => ?_
  obtain ⟨htIcc, htr⟩ := ht
  have ht1 : (1 : ℝ) ≤ t := htIcc.1
  have htr' : t ≤ r / 2 := htr
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hr : 0 < r := by
    have h2 : (1 : ℝ) ≤ r / 2 := le_trans ht1 htr'
    linarith
  have hab : r - t ≤ r + t := by linarith
  have hRterm : ‖∫ s in (r - t)..(r + t), absProfile f₀ s‖ =
      ∫ s in (r - t)..(r + t), ‖f₀ s‖ := by
    have h : (fun s : ℝ => absProfile f₀ s) = fun s : ℝ => ((‖f₀ s‖ : ℝ) : ℂ) := rfl
    rw [h]
    exact norm_intervalIntegral_ofReal_nonneg hab _ fun s _ => norm_nonneg _
  have hwindow : (∫ s in (r - t)..(r + t), ‖f₀ s‖) ≤
      ∫ s in (r / 2)..(3 * r / 2), ‖f₀ s‖ := by
    refine intervalIntegral_mono_subinterval hf₀.norm (fun s => norm_nonneg _)
      (by linarith) hab (by linarith)
  have hinv : t⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr ht1
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hRterm]
  calc t⁻¹ * ∫ s in (r - t)..(r + t), ‖f₀ s‖
      ≤ 1 * ∫ s in (r - t)..(r + t), ‖f₀ s‖ := by
        refine mul_le_mul_of_nonneg_right hinv ?_
        exact intervalIntegral.integral_nonneg hab fun s _ => norm_nonneg _
    _ = ∫ s in (r - t)..(r + t), ‖f₀ s‖ := one_mul _
    _ ≤ ∫ s in (r / 2)..(3 * r / 2), ‖f₀ s‖ := hwindow

/-- `R₁` vanishes below the radius `2`, where no admissible dilation exists. -/
theorem brsRemainderOne_eq_zero_of_lt {f₀ : ℝ → ℂ} {r : ℝ} (hr : r < 2) :
    brsRemainderOne (absProfile f₀) r = 0 := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) (by simp)
  exfalso
  have ht1 : (1 : ℝ) ≤ t := ht.1.1
  have htr : t ≤ r / 2 := ht.2
  linarith

theorem continuous_brsProfileSub {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 0 < p)
    {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) : Continuous (brsProfileSub d p f₀) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp : (0 : ℝ) ≤ ((d : ℝ) - 1) / p := by
    apply div_nonneg <;> linarith
  exact (Complex.continuous_ofReal.comp
    (continuous_rpow_const_of_nonneg hexp)).mul hf₀

theorem norm_brsProfileSub {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 0 < p) (f₀ : ℝ → ℂ)
    {s : ℝ} (hs : 0 ≤ s) :
    ‖brsProfileSub d p f₀ s‖ = s ^ (((d : ℝ) - 1) / p) * ‖f₀ s‖ := by
  rw [brsProfileSub, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hs _)]

/-- The modulus of the profile, recovered from the substituted profile. -/
theorem norm_eq_of_brsProfileSub {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 0 < p)
    (f₀ : ℝ → ℂ) {s : ℝ} (hs : 0 < s) :
    ‖f₀ s‖ = s ^ (-(((d : ℝ) - 1) / p)) * ‖brsProfileSub d p f₀ s‖ := by
  rw [norm_brsProfileSub hd hp f₀ hs.le, ← mul_assoc, ← Real.rpow_add hs]
  simp

/-- **Step A of BRS Proposition 4.2.**  After the substitution
`g = f₀ s^{(d-1)/p}`, the remainder `R₁` is dominated by the unit-window
average of `|g|` times `(2/r)^{(d-1)/p}`. -/
theorem brsRemainderOne_le_substituted {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 1 ≤ p)
    {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) (r : ℝ) :
    brsRemainderOne (absProfile f₀) r ≤
      ENNReal.ofReal ((2 / r) ^ (((d : ℝ) - 1) / p) *
        ∫ s in (r - 2)..(r + 2), ‖brsProfileSub d p f₀ s‖) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp : (0 : ℝ) ≤ ((d : ℝ) - 1) / p := by
    apply div_nonneg <;> linarith
  have hgcont : Continuous (brsProfileSub d p f₀) :=
    continuous_brsProfileSub hd hp0 hf₀
  refine iSup₂_le fun t ht => ?_
  obtain ⟨htIcc, htr⟩ := ht
  have ht1 : (1 : ℝ) ≤ t := htIcc.1
  have ht2 : t ≤ 2 := htIcc.2
  have htr' : t ≤ r / 2 := htr
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hr2 : (2 : ℝ) ≤ r := by linarith
  have hrpos : 0 < r := by linarith
  have hhalf : 0 < r / 2 := by linarith
  have hab : r - t ≤ r + t := by linarith
  -- rewrite the norm of the integral
  have hRterm : ‖∫ s in (r - t)..(r + t), absProfile f₀ s‖ =
      ∫ s in (r - t)..(r + t), ‖f₀ s‖ := by
    have h : (fun s : ℝ => absProfile f₀ s) = fun s : ℝ => ((‖f₀ s‖ : ℝ) : ℂ) := rfl
    rw [h]
    exact norm_intervalIntegral_ofReal_nonneg hab _ fun s _ => norm_nonneg _
  -- the pointwise substitution bound on the range of integration
  have hpoint : ∀ s ∈ Icc (r - t) (r + t),
      ‖f₀ s‖ ≤ (2 / r) ^ (((d : ℝ) - 1) / p) * ‖brsProfileSub d p f₀ s‖ := by
    intro s hs
    have hslow : r / 2 ≤ s := by
      have := hs.1
      linarith
    have hspos : 0 < s := lt_of_lt_of_le hhalf hslow
    have hmono : s ^ (-(((d : ℝ) - 1) / p)) ≤ (r / 2) ^ (-(((d : ℝ) - 1) / p)) :=
      Real.rpow_le_rpow_of_nonpos hhalf hslow (by linarith)
    have hinv : (r / 2) ^ (-(((d : ℝ) - 1) / p)) = (2 / r) ^ (((d : ℝ) - 1) / p) := by
      rw [Real.rpow_neg hhalf.le, show (2 / r : ℝ) = (r / 2)⁻¹ by rw [inv_div],
        Real.inv_rpow hhalf.le]
    rw [norm_eq_of_brsProfileSub hd hp0 f₀ hspos, ← hinv]
    exact mul_le_mul_of_nonneg_right hmono (norm_nonneg _)
  have hint1 : (∫ s in (r - t)..(r + t), ‖f₀ s‖) ≤
      ∫ s in (r - t)..(r + t),
        (2 / r) ^ (((d : ℝ) - 1) / p) * ‖brsProfileSub d p f₀ s‖ :=
    intervalIntegral.integral_mono_on hab (hf₀.norm.intervalIntegrable _ _)
      ((continuous_const.mul hgcont.norm).intervalIntegrable _ _) hpoint
  have hint2 : (∫ s in (r - t)..(r + t),
        (2 / r) ^ (((d : ℝ) - 1) / p) * ‖brsProfileSub d p f₀ s‖) =
      (2 / r) ^ (((d : ℝ) - 1) / p) *
        ∫ s in (r - t)..(r + t), ‖brsProfileSub d p f₀ s‖ :=
    intervalIntegral.integral_const_mul _ _
  have hint3 : (∫ s in (r - t)..(r + t), ‖brsProfileSub d p f₀ s‖) ≤
      ∫ s in (r - 2)..(r + 2), ‖brsProfileSub d p f₀ s‖ :=
    intervalIntegral_mono_subinterval hgcont.norm (fun s => norm_nonneg _)
      (by linarith) hab (by linarith)
  have hinvle : t⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr ht1
  have hcoefnn : (0 : ℝ) ≤ (2 / r) ^ (((d : ℝ) - 1) / p) :=
    Real.rpow_nonneg (by positivity) _
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hRterm]
  calc t⁻¹ * ∫ s in (r - t)..(r + t), ‖f₀ s‖
      ≤ 1 * ∫ s in (r - t)..(r + t), ‖f₀ s‖ := by
        refine mul_le_mul_of_nonneg_right hinvle ?_
        exact intervalIntegral.integral_nonneg hab fun s _ => norm_nonneg _
    _ = ∫ s in (r - t)..(r + t), ‖f₀ s‖ := one_mul _
    _ ≤ (2 / r) ^ (((d : ℝ) - 1) / p) *
          ∫ s in (r - t)..(r + t), ‖brsProfileSub d p f₀ s‖ := by
        rw [← hint2]
        exact hint1
    _ ≤ (2 / r) ^ (((d : ℝ) - 1) / p) *
          ∫ s in (r - 2)..(r + 2), ‖brsProfileSub d p f₀ s‖ :=
        mul_le_mul_of_nonneg_left hint3 hcoefnn

/-- The `L^p(s^{d-1} ds)` quasi-norm of a profile.  The weight
`ENNReal.ofReal s ^ (d-1)` vanishes for `s ≤ 0`, so this is the norm over
`(0, ∞)` used throughout BRS §4. -/
def profileLpNorm (d : ℕ) (p : ℝ) (h : ℝ → ENNReal) : ENNReal :=
  (∫⁻ s, ENNReal.ofReal s ^ (d - 1) * h s ^ p) ^ (1 / p)

/-- The substitution identity in `ℝ≥0∞` form: the `p`-th power of the
substituted profile carries the weight `s^{d-1}`. -/
theorem enorm_brsProfileSub_rpow {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 0 < p)
    (f₀ : ℝ → ℂ) {s : ℝ} (hs : 0 ≤ s) :
    (ENNReal.ofReal ‖brsProfileSub d p f₀ s‖) ^ p =
      ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp : (0 : ℝ) < ((d : ℝ) - 1) / p := by
    apply div_pos <;> linarith
  have hweight : (ENNReal.ofReal (s ^ (((d : ℝ) - 1) / p))) ^ p =
      ENNReal.ofReal s ^ (d - 1) := by
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, Real.zero_rpow hexp.ne', ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hp, zero_pow (by omega : d - 1 ≠ 0)]
    · have hconv : (s : ℝ) ^ ((d : ℝ) - 1) = s ^ (d - 1) := by
        have hc := pow_sub_eq_rpow h (D := d) (k := 1) (by omega)
        simpa using hc.symm
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs _) hp.le,
        ← Real.rpow_mul hs,
        show ((d : ℝ) - 1) / p * p = (d : ℝ) - 1 by field_simp,
        hconv, ENNReal.ofReal_pow hs]
  rw [norm_brsProfileSub hd hp f₀ hs,
    ENNReal.ofReal_mul (Real.rpow_nonneg hs _),
    ENNReal.mul_rpow_of_nonneg _ _ hp.le, hweight]

/-- **The `q = ∞` endpoint of BRS Proposition 4.2.**  The remainder `R₁` is
bounded pointwise by the `L^p(s^{d-1} ds)` norm of the profile. -/
theorem brsRemainderOne_le_profileLpNorm {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 1 ≤ p)
    {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) (r : ℝ) :
    brsRemainderOne (absProfile f₀) r ≤
      ENNReal.ofReal ((4 : ℝ) ^ (1 - 1 / p)) *
        profileLpNorm d p (fun s => ENNReal.ofReal ‖f₀ s‖) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ha : (0 : ℝ) ≤ ((d : ℝ) - 1) / p := by
    apply div_nonneg <;> linarith
  by_cases hr2 : r < 2
  · rw [brsRemainderOne_eq_zero_of_lt hr2]
    simp
  push Not at hr2
  have hrpos : 0 < r := by linarith
  have hab : r - 2 ≤ r + 2 := by linarith
  have hgcont : Continuous (brsProfileSub d p f₀) :=
    continuous_brsProfileSub hd hp0 hf₀
  set Φ : ℝ → ENNReal := fun s => ENNReal.ofReal ‖brsProfileSub d p f₀ s‖ with hΦ
  have hΦmeas : Measurable Φ := by
    rw [hΦ]
    exact hgcont.norm.measurable.ennreal_ofReal
  -- Step A, with the harmless factor `(2/r)^{(d-1)/p} ≤ 1`
  have hcoef : (2 / r) ^ (((d : ℝ) - 1) / p) ≤ 1 := by
    refine Real.rpow_le_one (by positivity) ?_ ha
    rw [div_le_one hrpos]
    exact hr2
  have hstepA : brsRemainderOne (absProfile f₀) r ≤
      ENNReal.ofReal (∫ s in (r - 2)..(r + 2), ‖brsProfileSub d p f₀ s‖) := by
    refine le_trans (brsRemainderOne_le_substituted hd hp hf₀ r)
      (ENNReal.ofReal_le_ofReal ?_)
    have hInn : (0 : ℝ) ≤ ∫ s in (r - 2)..(r + 2), ‖brsProfileSub d p f₀ s‖ :=
      intervalIntegral.integral_nonneg hab fun s _ => norm_nonneg _
    calc (2 / r) ^ (((d : ℝ) - 1) / p) *
          ∫ s in (r - 2)..(r + 2), ‖brsProfileSub d p f₀ s‖
        ≤ 1 * ∫ s in (r - 2)..(r + 2), ‖brsProfileSub d p f₀ s‖ :=
          mul_le_mul_of_nonneg_right hcoef hInn
      _ = ∫ s in (r - 2)..(r + 2), ‖brsProfileSub d p f₀ s‖ := one_mul _
  -- rewrite the window integral as a lintegral
  have hconv : ENNReal.ofReal (∫ s in (r - 2)..(r + 2),
      ‖brsProfileSub d p f₀ s‖) = ∫⁻ s in Icc (r - 2) (r + 2), Φ s := by
    rw [intervalIntegral.integral_of_le hab,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine ofReal_integral_eq_lintegral_ofReal ?_ ?_
    · exact (hgcont.norm.continuousOn).integrableOn_Icc
    · exact ae_of_all _ fun s => norm_nonneg _
  -- Hölder on the window
  have hWvol : volume (Icc (r - 2) (r + 2)) = ENNReal.ofReal 4 := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have hholder : (∫⁻ s in Icc (r - 2) (r + 2), Φ s) ≤
      (∫⁻ s in Icc (r - 2) (r + 2), Φ s ^ p) ^ (1 / p) *
        ENNReal.ofReal ((4 : ℝ) ^ (1 - 1 / p)) := by
    rcases eq_or_lt_of_le hp with hp1 | hp1
    · rw [← hp1]
      simp
    · have hpq := Real.HolderConjugate.conjExponent hp1
      have hkey := ENNReal.lintegral_mul_le_Lp_mul_Lq
        (volume.restrict (Icc (r - 2) (r + 2))) hpq
        hΦmeas.aemeasurable (aemeasurable_const (b := (1 : ENNReal)))
      simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow] at hkey
      refine le_trans hkey ?_
      have hone : (∫⁻ _s in Icc (r - 2) (r + 2), (1 : ENNReal)) =
          ENNReal.ofReal 4 := by
        rw [setLIntegral_one, hWvol]
      rw [hone]
      refine mul_le_mul' le_rfl ?_
      have hconj : 1 / Real.conjExponent p = 1 - 1 / p := by
        rw [Real.conjExponent]
        have hpne : p ≠ 0 := hp0.ne'
        have hp1ne : p - 1 ≠ 0 := by
          intro hcon
          rw [sub_eq_zero] at hcon
          exact absurd hcon.symm hp1.ne
        field_simp
      rw [hconj, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by
        have : 1 / p ≤ 1 := by
          rw [div_le_one hp0]
          exact hp
        linarith)]
  -- pass from the window to the whole line
  have hpow : (∫⁻ s in Icc (r - 2) (r + 2), Φ s ^ p) ≤
      ∫⁻ s, ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p := by
    calc (∫⁻ s in Icc (r - 2) (r + 2), Φ s ^ p)
        = ∫⁻ s in Icc (r - 2) (r + 2),
            ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p := by
          refine setLIntegral_congr_fun measurableSet_Icc ?_
          intro s hs
          have hs0 : 0 ≤ s := by
            have := hs.1
            linarith
          rw [hΦ]
          exact enorm_brsProfileSub_rpow hd hp0 f₀ hs0
      _ ≤ ∫⁻ s, ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p :=
          setLIntegral_le_lintegral _ _
  calc brsRemainderOne (absProfile f₀) r
      ≤ ∫⁻ s in Icc (r - 2) (r + 2), Φ s := by rw [← hconv]; exact hstepA
    _ ≤ (∫⁻ s in Icc (r - 2) (r + 2), Φ s ^ p) ^ (1 / p) *
          ENNReal.ofReal ((4 : ℝ) ^ (1 - 1 / p)) := hholder
    _ ≤ (∫⁻ s, ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p) ^ (1 / p) *
          ENNReal.ofReal ((4 : ℝ) ^ (1 - 1 / p)) := by
        refine mul_le_mul' (ENNReal.rpow_le_rpow hpow (by positivity)) le_rfl
    _ = ENNReal.ofReal ((4 : ℝ) ^ (1 - 1 / p)) *
          profileLpNorm d p (fun s => ENNReal.ofReal ‖f₀ s‖) := by
        rw [profileLpNorm, mul_comm]

/-- Hölder's inequality against the constant function: on a measure space the
integral is bounded by the `L^p` norm times a power of the total mass. -/
theorem lintegral_le_rpow_mul_measure_univ {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Φ : α → ENNReal} (hΦ : Measurable Φ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ s, Φ s ∂μ) ≤ (∫⁻ s, Φ s ^ p ∂μ) ^ (1 / p) * (μ univ) ^ (1 - 1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · rw [← hp1]
    simp
  · have hpq := Real.HolderConjugate.conjExponent hp1
    have hkey := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hΦ.aemeasurable
      (aemeasurable_const (b := (1 : ENNReal)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow] at hkey
    refine le_trans hkey ?_
    rw [lintegral_one]
    refine mul_le_mul' le_rfl ?_
    have hconj : 1 / Real.conjExponent p = 1 - 1 / p := by
      rw [Real.conjExponent]
      have hpne : p ≠ 0 := hp0.ne'
      have hp1ne : p - 1 ≠ 0 := by
        intro hcon
        rw [sub_eq_zero] at hcon
        exact absurd hcon.symm hp1.ne
      field_simp
    rw [hconj]

/-- The weighted `p`-th power of `R₁` at radius `r` is controlled by the
`L^p` mass of the substituted profile on the window `[r-2, r+2]`; the weight
`r^{d-1}` is cancelled exactly by the factor `(2/r)^{d-1}` of the substitution
bound. -/
theorem weighted_brsRemainderOne_pow_le {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 1 ≤ p)
    {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) (r : ℝ) :
    ENNReal.ofReal r ^ (d - 1) * brsRemainderOne (absProfile f₀) r ^ p ≤
      ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ (p - 1)) *
        ∫⁻ s in Icc (r - 2) (r + 2) ∩ Ici (0 : ℝ),
          (ENNReal.ofReal ‖brsProfileSub d p f₀ s‖) ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ha : (0 : ℝ) ≤ ((d : ℝ) - 1) / p := by
    apply div_nonneg <;> linarith
  by_cases hr2 : r < 2
  · rw [brsRemainderOne_eq_zero_of_lt hr2, ENNReal.zero_rpow_of_pos hp0, mul_zero]
    simp
  push Not at hr2
  have hrpos : 0 < r := by linarith
  have hab : r - 2 ≤ r + 2 := by linarith
  have hsubset : Icc (r - 2) (r + 2) ⊆ Ici (0 : ℝ) := by
    intro s hs
    have := hs.1
    simp only [mem_Ici]
    linarith
  have hset : Icc (r - 2) (r + 2) ∩ Ici (0 : ℝ) = Icc (r - 2) (r + 2) :=
    inter_eq_self_of_subset_left hsubset
  rw [hset]
  have hgcont : Continuous (brsProfileSub d p f₀) :=
    continuous_brsProfileSub hd hp0 hf₀
  set Φ : ℝ → ENNReal := fun s => ENNReal.ofReal ‖brsProfileSub d p f₀ s‖ with hΦ
  have hΦmeas : Measurable Φ := by
    rw [hΦ]
    exact hgcont.norm.measurable.ennreal_ofReal
  set W : ℝ := ∫ s in (r - 2)..(r + 2), ‖brsProfileSub d p f₀ s‖ with hW
  have hWnn : 0 ≤ W := by
    rw [hW]
    exact intervalIntegral.integral_nonneg hab fun s _ => norm_nonneg _
  have hconv : ENNReal.ofReal W = ∫⁻ s in Icc (r - 2) (r + 2), Φ s := by
    rw [hW, intervalIntegral.integral_of_le hab,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine ofReal_integral_eq_lintegral_ofReal ?_ ?_
    · exact (hgcont.norm.continuousOn).integrableOn_Icc
    · exact ae_of_all _ fun s => norm_nonneg _
  -- the weight cancellation
  have hpowconv : ((2 : ℝ) / r) ^ (((d : ℝ) - 1) / p * p) = ((2 : ℝ) / r) ^ (d - 1) := by
    rw [show ((d : ℝ) - 1) / p * p = (d : ℝ) - 1 by field_simp]
    have hc := pow_sub_eq_rpow (x := (2 : ℝ) / r) (by positivity) (D := d) (k := 1)
      (by omega)
    simpa using hc.symm
  have hweight : ENNReal.ofReal r ^ (d - 1) *
      ENNReal.ofReal (((2 : ℝ) / r) ^ (d - 1)) =
        ENNReal.ofReal ((2 : ℝ) ^ (d - 1)) := by
    rw [← ENNReal.ofReal_pow hrpos.le, ← ENNReal.ofReal_mul (by positivity),
      ← mul_pow]
    congr 2
    field_simp
  -- the Hölder step
  have hholder : ENNReal.ofReal (W ^ p) ≤
      ENNReal.ofReal ((4 : ℝ) ^ (p - 1)) *
        ∫⁻ s in Icc (r - 2) (r + 2), Φ s ^ p := by
    have hWvol : (volume.restrict (Icc (r - 2) (r + 2))) univ = ENNReal.ofReal 4 := by
      rw [Measure.restrict_apply_univ, Real.volume_Icc]
      congr 1
      ring
    have h1 := lintegral_le_rpow_mul_measure_univ (μ := volume.restrict
      (Icc (r - 2) (r + 2))) hΦmeas hp
    rw [hWvol] at h1
    have h2 : (ENNReal.ofReal W) ^ p ≤
        ((∫⁻ s in Icc (r - 2) (r + 2), Φ s ^ p) ^ (1 / p) *
          ENNReal.ofReal 4 ^ (1 - 1 / p)) ^ p := by
      rw [hconv]
      exact ENNReal.rpow_le_rpow h1 hp0.le
    have hexp1 : (0 : ℝ) ≤ 1 - 1 / p := by
      have h1p : 1 / p ≤ 1 := by
        rw [div_le_one hp0]
        exact hp
      linarith
    have hexp2 : (0 : ℝ) ≤ (1 - p⁻¹) * p := by
      have h1p : p⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        exact Or.inr hp
      have : (0 : ℝ) ≤ 1 - p⁻¹ := by linarith
      positivity
    have h3 : ((∫⁻ s in Icc (r - 2) (r + 2), Φ s ^ p) ^ (1 / p) *
          ENNReal.ofReal 4 ^ (1 - 1 / p)) ^ p =
        ENNReal.ofReal ((4 : ℝ) ^ (p - 1)) *
          ∫⁻ s in Icc (r - 2) (r + 2), Φ s ^ p := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg (by norm_num) hexp2,
        show (1 - p⁻¹) * p = p - 1 by field_simp]
      ring
    rw [← ENNReal.ofReal_rpow_of_nonneg hWnn hp0.le]
    exact le_trans h2 (le_of_eq h3)
  -- assemble
  have hstepA : brsRemainderOne (absProfile f₀) r ≤
      ENNReal.ofReal (((2 : ℝ) / r) ^ (((d : ℝ) - 1) / p) * W) := by
    rw [hW]
    exact brsRemainderOne_le_substituted hd hp hf₀ r
  calc ENNReal.ofReal r ^ (d - 1) * brsRemainderOne (absProfile f₀) r ^ p
      ≤ ENNReal.ofReal r ^ (d - 1) *
          (ENNReal.ofReal (((2 : ℝ) / r) ^ (((d : ℝ) - 1) / p) * W)) ^ p :=
        mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hstepA hp0.le)
    _ = ENNReal.ofReal r ^ (d - 1) *
          (ENNReal.ofReal (((2 : ℝ) / r) ^ (d - 1)) * ENNReal.ofReal (W ^ p)) := by
        congr 1
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
          Real.mul_rpow (Real.rpow_nonneg (by positivity) _) hWnn,
          ← Real.rpow_mul (by positivity), hpowconv,
          ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((2 : ℝ) ^ (d - 1)) * ENNReal.ofReal (W ^ p) := by
        rw [← mul_assoc, hweight]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (d - 1)) *
          (ENNReal.ofReal ((4 : ℝ) ^ (p - 1)) *
            ∫⁻ s in Icc (r - 2) (r + 2), Φ s ^ p) :=
        mul_le_mul' le_rfl hholder
    _ = ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ (p - 1)) *
          ∫⁻ s in Icc (r - 2) (r + 2), Φ s ^ p := by
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]

/-- Translating the window: the integral over `[r-2, r+2]` is the integral of
the translate over `[-2, 2]`. -/
theorem lintegral_window_translate {Ψ : ℝ → ENNReal} (hΨ : Measurable Ψ) (r : ℝ) :
    (∫⁻ s in Icc (r - 2) (r + 2), Ψ s) = ∫⁻ u in Icc (-2 : ℝ) 2, Ψ (u + r) := by
  rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc,
    ← lintegral_add_right_eq_self
      (fun s => (Icc (r - 2) (r + 2)).indicator Ψ s) r]
  refine lintegral_congr fun u => ?_
  by_cases hu : u ∈ Icc (-2 : ℝ) 2
  · have hmem : u + r ∈ Icc (r - 2) (r + 2) := by
      constructor <;> [linarith [hu.1]; linarith [hu.2]]
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hu]
  · have hnmem : u + r ∉ Icc (r - 2) (r + 2) := by
      intro hcon
      exact hu ⟨by linarith [hcon.1], by linarith [hcon.2]⟩
    rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hu]

/-- **Tonelli for the unit window.**  Integrating the window mass over all
radii multiplies the total mass by the window length. -/
theorem lintegral_window_swap {Ψ : ℝ → ENNReal} (hΨ : Measurable Ψ) :
    (∫⁻ r : ℝ, ∫⁻ s in Icc (r - 2) (r + 2), Ψ s) =
      ENNReal.ofReal 4 * ∫⁻ s, Ψ s := by
  have htrans : (∫⁻ r : ℝ, ∫⁻ s in Icc (r - 2) (r + 2), Ψ s) =
      ∫⁻ r : ℝ, ∫⁻ u in Icc (-2 : ℝ) 2, Ψ (u + r) :=
    lintegral_congr fun r => lintegral_window_translate hΨ r
  have hswap : (∫⁻ r : ℝ, ∫⁻ u in Icc (-2 : ℝ) 2, Ψ (u + r)) =
      ∫⁻ u in Icc (-2 : ℝ) 2, ∫⁻ r : ℝ, Ψ (u + r) := by
    refine lintegral_lintegral_swap ?_
    exact (hΨ.comp (measurable_snd.add measurable_fst)).aemeasurable
  have hinner : ∀ u : ℝ, (∫⁻ r : ℝ, Ψ (u + r)) = ∫⁻ r, Ψ r := fun u =>
    lintegral_add_left_eq_self Ψ u
  rw [htrans, hswap, lintegral_congr hinner, setLIntegral_const, Real.volume_Icc]
  rw [show (2 : ℝ) - -2 = 4 by ring]
  rw [mul_comm]

theorem setLIntegral_inter_eq_indicator {A B : Set ℝ} (hB : MeasurableSet B)
    (f : ℝ → ENNReal) :
    (∫⁻ s in A ∩ B, f s) = ∫⁻ s in A, B.indicator f s := by
  rw [lintegral_indicator hB, Measure.restrict_restrict hB, inter_comm]

/-- **The diagonal case `p = q` of BRS Proposition 4.2.** -/
theorem profileLpNorm_brsRemainderOne_le {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 1 ≤ p)
    {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) :
    (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
        brsRemainderOne (absProfile f₀) r ^ p) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p) *
        ∫⁻ s, ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hgcont : Continuous (brsProfileSub d p f₀) :=
    continuous_brsProfileSub hd hp0 hf₀
  set Φ : ℝ → ENNReal := fun s => ENNReal.ofReal ‖brsProfileSub d p f₀ s‖ with hΦ
  have hΦmeas : Measurable Φ := by
    rw [hΦ]
    exact hgcont.norm.measurable.ennreal_ofReal
  set Ψ : ℝ → ENNReal := (Ici (0 : ℝ)).indicator (fun s => Φ s ^ p) with hΨdef
  have hΨmeas : Measurable Ψ := by
    rw [hΨdef]
    exact (hΦmeas.pow_const p).indicator measurableSet_Ici
  -- the pointwise bound, rewritten with the indicator
  have hpoint : ∀ r : ℝ, ENNReal.ofReal r ^ (d - 1) *
      brsRemainderOne (absProfile f₀) r ^ p ≤
        ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ (p - 1)) *
          ∫⁻ s in Icc (r - 2) (r + 2), Ψ s := by
    intro r
    refine le_trans (weighted_brsRemainderOne_pow_le hd hp hf₀ r) ?_
    rw [hΨdef, ← setLIntegral_inter_eq_indicator measurableSet_Ici]
  -- integrate and swap
  have hswap := lintegral_window_swap hΨmeas
  have hΨint : (∫⁻ s, Ψ s) =
      ∫⁻ s in Ici (0 : ℝ), ENNReal.ofReal s ^ (d - 1) *
        (ENNReal.ofReal ‖f₀ s‖) ^ p := by
    rw [hΨdef, lintegral_indicator measurableSet_Ici]
    refine setLIntegral_congr_fun measurableSet_Ici ?_
    intro s hs
    rw [hΦ]
    exact enorm_brsProfileSub_rpow hd hp0 f₀ hs
  calc (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
        brsRemainderOne (absProfile f₀) r ^ p)
      ≤ ∫⁻ r, ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ (p - 1)) *
          ∫⁻ s in Icc (r - 2) (r + 2), Ψ s := lintegral_mono hpoint
    _ = ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ (p - 1)) *
          ∫⁻ r, ∫⁻ s in Icc (r - 2) (r + 2), Ψ s := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ (p - 1)) *
          (ENNReal.ofReal 4 * ∫⁻ s, Ψ s) := by rw [hswap]
    _ = ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p) * ∫⁻ s, Ψ s := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [show (2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ (p - 1) * 4 =
          (2 : ℝ) ^ (d - 1) * ((4 : ℝ) ^ (p - 1) * 4) by ring]
        congr 1
        rw [show (4 : ℝ) ^ p = (4 : ℝ) ^ (p - 1 + 1) by ring_nf,
          Real.rpow_add (by norm_num), Real.rpow_one]
    _ = ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p) *
          ∫⁻ s in Ici (0 : ℝ), ENNReal.ofReal s ^ (d - 1) *
            (ENNReal.ofReal ‖f₀ s‖) ^ p := by rw [hΨint]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p) *
          ∫⁻ s, ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p := by
        exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- **BRS Proposition 4.2.**  For `1 ≤ p ≤ q < ∞` the remainder `R₁` maps
`L^p(s^{d-1} ds)` to `L^q(r^{d-1} dr)`.  The proof interpolates between the
diagonal bound and the `q = ∞` endpoint. -/
theorem prop42_brsRemainderOne {d : ℕ} (hd : 2 ≤ d) {p q : ℝ} (hp : 1 ≤ p)
    (hpq : p ≤ q) {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) :
    (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
        brsRemainderOne (absProfile f₀) r ^ q) ^ (1 / q) ≤
      ENNReal.ofReal (((4 : ℝ) ^ ((1 - 1 / p) * (q - p)) *
          ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p)) ^ (1 / q)) *
        (∫⁻ s, ENNReal.ofReal s ^ (d - 1) *
          (ENNReal.ofReal ‖f₀ s‖) ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le hp0 hpq
  have hqp : (0 : ℝ) ≤ q - p := by linarith
  have hexp1 : (0 : ℝ) ≤ 1 - 1 / p := by
    have h1p : 1 / p ≤ 1 := by
      rw [div_le_one hp0]
      exact hp
    linarith
  have hCpos : (0 : ℝ) < ((4 : ℝ) ^ ((1 - 1 / p) * (q - p)) *
      ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p)) ^ (1 / q) := by
    have h1 : (0 : ℝ) < (4 : ℝ) ^ ((1 - 1 / p) * (q - p)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < (4 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (d - 1) := by positivity
    exact Real.rpow_pos_of_pos (by positivity) _
  set X : ENNReal := ∫⁻ s, ENNReal.ofReal s ^ (d - 1) *
    (ENNReal.ofReal ‖f₀ s‖) ^ p with hX
  by_cases hXtop : X = ⊤
  · rw [hXtop, ENNReal.top_rpow_of_pos (by positivity : (0:ℝ) < 1 / p),
      ENNReal.mul_top (by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact hCpos)]
    exact le_top
  set N : ENNReal := ENNReal.ofReal ((4 : ℝ) ^ (1 - 1 / p)) * X ^ (1 / p) with hN
  have hNtop : N ≠ ⊤ := by
    rw [hN]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hXtop
  have hNpow : N ^ (q - p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hqp hNtop
  -- the `q = ∞` endpoint gives a uniform pointwise bound
  have hsup : ∀ r : ℝ, brsRemainderOne (absProfile f₀) r ≤ N := by
    intro r
    have h := brsRemainderOne_le_profileLpNorm hd hp hf₀ r
    rw [profileLpNorm, ← hX, ← hN] at h
    exact h
  -- interpolation, pointwise
  have hstep : ∀ r : ℝ, ENNReal.ofReal r ^ (d - 1) *
      brsRemainderOne (absProfile f₀) r ^ q ≤
        N ^ (q - p) *
          (ENNReal.ofReal r ^ (d - 1) * brsRemainderOne (absProfile f₀) r ^ p) := by
    intro r
    have hsplit : brsRemainderOne (absProfile f₀) r ^ q =
        brsRemainderOne (absProfile f₀) r ^ (q - p) *
          brsRemainderOne (absProfile f₀) r ^ p := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hqp hp0.le]
      congr 1
      ring
    rw [hsplit]
    calc ENNReal.ofReal r ^ (d - 1) *
          (brsRemainderOne (absProfile f₀) r ^ (q - p) *
            brsRemainderOne (absProfile f₀) r ^ p)
        ≤ ENNReal.ofReal r ^ (d - 1) *
            (N ^ (q - p) * brsRemainderOne (absProfile f₀) r ^ p) := by
          refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
          exact ENNReal.rpow_le_rpow (hsup r) hqp
      _ = N ^ (q - p) *
            (ENNReal.ofReal r ^ (d - 1) * brsRemainderOne (absProfile f₀) r ^ p) := by
          ring
  -- integrate
  have hint : (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
      brsRemainderOne (absProfile f₀) r ^ q) ≤
        N ^ (q - p) * (ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p) * X) := by
    calc (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
          brsRemainderOne (absProfile f₀) r ^ q)
        ≤ ∫⁻ r, N ^ (q - p) *
            (ENNReal.ofReal r ^ (d - 1) *
              brsRemainderOne (absProfile f₀) r ^ p) := lintegral_mono hstep
      _ = N ^ (q - p) * ∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
            brsRemainderOne (absProfile f₀) r ^ p :=
          lintegral_const_mul' _ _ hNpow
      _ ≤ N ^ (q - p) * (ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p) * X) := by
          refine mul_le_mul' le_rfl ?_
          rw [hX]
          exact profileLpNorm_brsRemainderOne_le hd hp hf₀
  -- take the `q`-th root and collect the powers of `X`
  have hpowN : N ^ (q - p) = ENNReal.ofReal ((4 : ℝ) ^ ((1 - 1 / p) * (q - p))) *
      X ^ ((q - p) / p) := by
    rw [hN, ENNReal.mul_rpow_of_nonneg _ _ hqp]
    congr 1
    · rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (by norm_num) _) hqp,
        ← Real.rpow_mul (by norm_num)]
    · rw [← ENNReal.rpow_mul]
      congr 1
      field_simp
  have hXcomb : X ^ ((q - p) / p) * X = X ^ (q / p) := by
    have h1 : X ^ ((q - p) / p + 1) = X ^ ((q - p) / p) * X ^ (1 : ℝ) :=
      ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by norm_num)
    rw [ENNReal.rpow_one] at h1
    rw [← h1]
    congr 1
    field_simp
    ring
  calc (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
        brsRemainderOne (absProfile f₀) r ^ q) ^ (1 / q)
      ≤ (N ^ (q - p) *
          (ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p) * X)) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = (ENNReal.ofReal ((4 : ℝ) ^ ((1 - 1 / p) * (q - p))) * X ^ ((q - p) / p) *
          (ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p) * X)) ^ (1 / q) := by
        rw [hpowN]
    _ = ENNReal.ofReal (((4 : ℝ) ^ ((1 - 1 / p) * (q - p)) *
          ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p)) ^ (1 / q)) *
          (X ^ ((q - p) / p) * X) ^ (1 / q) := by
        rw [show ENNReal.ofReal ((4 : ℝ) ^ ((1 - 1 / p) * (q - p))) *
            X ^ ((q - p) / p) *
            (ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p) * X) =
            (ENNReal.ofReal ((4 : ℝ) ^ ((1 - 1 / p) * (q - p))) *
              ENNReal.ofReal ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p)) *
              (X ^ ((q - p) / p) * X) by ring,
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / q),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    _ = ENNReal.ofReal (((4 : ℝ) ^ ((1 - 1 / p) * (q - p)) *
          ((2 : ℝ) ^ (d - 1) * (4 : ℝ) ^ p)) ^ (1 / q)) * X ^ (1 / p) := by
        congr 1
        rw [hXcomb, ← ENNReal.rpow_mul]
        congr 1
        field_simp

/-- **BRS (4.5).**  Hölder's inequality turns `R₂` into a local `L^p` average:
the admissible dilations force the integration window into `[1/4, 4]`, where
the weight `s^{d-1}` is comparable to one. -/
theorem brsRemainderTwo_le_local {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 1 ≤ p)
    {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) (r : ℝ) :
    brsRemainderTwo (absProfile f₀) r ≤
      ENNReal.ofReal ((3 : ℝ) ^ (((d : ℝ) - 1) / p) * (2 : ℝ) ^ (1 - 1 / p)) *
        (ENNReal.ofReal r⁻¹ *
          ∫⁻ s in Icc (1 / 4 : ℝ) 4,
            ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp1 : (0 : ℝ) ≤ 1 - 1 / p := by
    have h1p : 1 / p ≤ 1 := by
      rw [div_le_one hp0]
      exact hp
    linarith
  set Y : ENNReal := ∫⁻ s in Icc (1 / 4 : ℝ) 4,
    ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p with hY
  refine iSup₂_le fun t ht => ?_
  obtain ⟨htIcc, htr⟩ := ht
  have ht1 : (1 : ℝ) ≤ t := htIcc.1
  have ht2 : t ≤ 2 := htIcc.2
  have htr' : 3 * r / 2 ≤ t := htr
  by_cases hr : r ≤ 0
  · have hzero : r⁻¹ * ‖∫ s in (t - r)..(t + r), absProfile f₀ s‖ ≤ 0 := by
      have hinv : r⁻¹ ≤ 0 := inv_nonpos.mpr hr
      exact mul_nonpos_of_nonpos_of_nonneg hinv (norm_nonneg _)
    rw [ENNReal.ofReal_eq_zero.mpr hzero]
    simp
  push Not at hr
  have hrle : r ≤ 4 / 3 := by linarith
  have hab : t - r ≤ t + r := by linarith
  have hthird : t / 3 ≤ t - r := by linarith
  have hslow : ∀ s ∈ Icc (t - r) (t + r), (1 : ℝ) / 3 ≤ s := by
    intro s hs
    have h1 : t - r ≤ s := hs.1
    have h2 : (1 : ℝ) / 3 ≤ t / 3 := by linarith
    linarith
  have hsub : Icc (t - r) (t + r) ⊆ Icc (1 / 4 : ℝ) 4 := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have := hslow s hs
      linarith
    · have := hs.2
      linarith
  -- the window integral as a lintegral
  have hRterm : ‖∫ s in (t - r)..(t + r), absProfile f₀ s‖ =
      ∫ s in (t - r)..(t + r), ‖f₀ s‖ := by
    have h : (fun s : ℝ => absProfile f₀ s) = fun s : ℝ => ((‖f₀ s‖ : ℝ) : ℂ) := rfl
    rw [h]
    exact norm_intervalIntegral_ofReal_nonneg hab _ fun s _ => norm_nonneg _
  have hconv : ENNReal.ofReal (∫ s in (t - r)..(t + r), ‖f₀ s‖) =
      ∫⁻ s in Icc (t - r) (t + r), ENNReal.ofReal ‖f₀ s‖ := by
    rw [intervalIntegral.integral_of_le hab,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine ofReal_integral_eq_lintegral_ofReal ?_ ?_
    · exact (hf₀.norm.continuousOn).integrableOn_Icc
    · exact ae_of_all _ fun s => norm_nonneg _
  -- Hölder on the window
  have hWvol : (volume.restrict (Icc (t - r) (t + r))) univ =
      ENNReal.ofReal (2 * r) := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    congr 1
    ring
  have hholder := lintegral_le_rpow_mul_measure_univ
    (μ := volume.restrict (Icc (t - r) (t + r)))
    (Φ := fun s => ENNReal.ofReal ‖f₀ s‖)
    hf₀.norm.measurable.ennreal_ofReal hp
  rw [hWvol] at hholder
  -- the weight is comparable to one on the window
  have hweight : (∫⁻ s in Icc (t - r) (t + r), (ENNReal.ofReal ‖f₀ s‖) ^ p) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (d - 1)) * Y := by
    calc (∫⁻ s in Icc (t - r) (t + r), (ENNReal.ofReal ‖f₀ s‖) ^ p)
        ≤ ∫⁻ s in Icc (t - r) (t + r), ENNReal.ofReal ((3 : ℝ) ^ (d - 1)) *
            (ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p) := by
          refine setLIntegral_mono' measurableSet_Icc ?_
          intro s hs
          have hs3 : (1 : ℝ) / 3 ≤ s := hslow s hs
          have hspos : 0 < s := by linarith
          have hone : (1 : ENNReal) ≤ ENNReal.ofReal ((3 : ℝ) ^ (d - 1)) *
              ENNReal.ofReal s ^ (d - 1) := by
            rw [← ENNReal.ofReal_pow hspos.le, ← ENNReal.ofReal_mul (by positivity),
              ← mul_pow, ENNReal.one_le_ofReal]
            refine one_le_pow₀ ?_
            nlinarith [hs3]
          calc (ENNReal.ofReal ‖f₀ s‖) ^ p
              = 1 * (ENNReal.ofReal ‖f₀ s‖) ^ p := (one_mul _).symm
            _ ≤ (ENNReal.ofReal ((3 : ℝ) ^ (d - 1)) * ENNReal.ofReal s ^ (d - 1)) *
                  (ENNReal.ofReal ‖f₀ s‖) ^ p := mul_le_mul' hone le_rfl
            _ = ENNReal.ofReal ((3 : ℝ) ^ (d - 1)) *
                  (ENNReal.ofReal s ^ (d - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p) := by
                ring
      _ = ENNReal.ofReal ((3 : ℝ) ^ (d - 1)) *
            ∫⁻ s in Icc (t - r) (t + r), ENNReal.ofReal s ^ (d - 1) *
              (ENNReal.ofReal ‖f₀ s‖) ^ p :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (d - 1)) * Y := by
          refine mul_le_mul' le_rfl ?_
          rw [hY]
          exact lintegral_mono_set hsub
  -- assemble
  have hfinal : ENNReal.ofReal r⁻¹ *
      ((ENNReal.ofReal ((3 : ℝ) ^ (d - 1)) * Y) ^ (1 / p) *
        ENNReal.ofReal (2 * r) ^ (1 - 1 / p)) =
      ENNReal.ofReal ((3 : ℝ) ^ (((d : ℝ) - 1) / p) * (2 : ℝ) ^ (1 - 1 / p)) *
        (ENNReal.ofReal r⁻¹ * Y) ^ (1 / p) := by
    have h3 : (ENNReal.ofReal ((3 : ℝ) ^ (d - 1))) ^ (1 / p) =
        ENNReal.ofReal ((3 : ℝ) ^ (((d : ℝ) - 1) / p)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      congr 1
      have hc : ((3 : ℝ) ^ (d - 1) : ℝ) = (3 : ℝ) ^ ((d : ℝ) - 1) := by
        have hc0 := pow_sub_eq_rpow (x := (3 : ℝ)) (by norm_num) (D := d) (k := 1)
          (by omega)
        simpa using hc0
      rw [hc, ← Real.rpow_mul (by norm_num)]
      congr 1
      field_simp
    have h2r : ENNReal.ofReal (2 * r) ^ (1 - 1 / p) =
        ENNReal.ofReal ((2 : ℝ) ^ (1 - 1 / p)) *
          ENNReal.ofReal (r ^ (1 - 1 / p)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hexp1,
        Real.mul_rpow (by norm_num) hr.le, ENNReal.ofReal_mul (by positivity)]
    have hrinv : ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r ^ (1 - 1 / p)) =
        (ENNReal.ofReal r⁻¹) ^ (1 / p) := by
      rw [← ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      congr 1
      have hL : r⁻¹ * r ^ (1 - 1 / p) = r ^ (-(1 / p)) := by
        rw [← Real.rpow_neg_one r, ← Real.rpow_add hr]
        congr 1
        ring
      have hR : (r⁻¹) ^ (1 / p) = r ^ (-(1 / p)) := by
        rw [← Real.rpow_neg_one r, ← Real.rpow_mul hr.le]
        congr 1
        ring
      rw [hL, hR]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p), h3, h2r]
    calc ENNReal.ofReal r⁻¹ *
          (ENNReal.ofReal ((3 : ℝ) ^ (((d : ℝ) - 1) / p)) * Y ^ (1 / p) *
            (ENNReal.ofReal ((2 : ℝ) ^ (1 - 1 / p)) *
              ENNReal.ofReal (r ^ (1 - 1 / p))))
        = (ENNReal.ofReal ((3 : ℝ) ^ (((d : ℝ) - 1) / p)) *
            ENNReal.ofReal ((2 : ℝ) ^ (1 - 1 / p))) *
            ((ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r ^ (1 - 1 / p))) *
              Y ^ (1 / p)) := by ring
      _ = ENNReal.ofReal ((3 : ℝ) ^ (((d : ℝ) - 1) / p) * (2 : ℝ) ^ (1 - 1 / p)) *
            ((ENNReal.ofReal r⁻¹) ^ (1 / p) * Y ^ (1 / p)) := by
          rw [← ENNReal.ofReal_mul (by positivity), hrinv]
      _ = ENNReal.ofReal ((3 : ℝ) ^ (((d : ℝ) - 1) / p) * (2 : ℝ) ^ (1 - 1 / p)) *
            (ENNReal.ofReal r⁻¹ * Y) ^ (1 / p) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p)]
  calc ENNReal.ofReal (r⁻¹ * ‖∫ s in (t - r)..(t + r), absProfile f₀ s‖)
      = ENNReal.ofReal r⁻¹ *
          ∫⁻ s in Icc (t - r) (t + r), ENNReal.ofReal ‖f₀ s‖ := by
        rw [hRterm, ENNReal.ofReal_mul (by positivity), hconv]
    _ ≤ ENNReal.ofReal r⁻¹ *
          ((∫⁻ s in Icc (t - r) (t + r), (ENNReal.ofReal ‖f₀ s‖) ^ p) ^ (1 / p) *
            ENNReal.ofReal (2 * r) ^ (1 - 1 / p)) := mul_le_mul' le_rfl hholder
    _ ≤ ENNReal.ofReal r⁻¹ *
          ((ENNReal.ofReal ((3 : ℝ) ^ (d - 1)) * Y) ^ (1 / p) *
            ENNReal.ofReal (2 * r) ^ (1 - 1 / p)) := by
        refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
        exact ENNReal.rpow_le_rpow hweight (by positivity)
    _ = ENNReal.ofReal ((3 : ℝ) ^ (((d : ℝ) - 1) / p) * (2 : ℝ) ^ (1 - 1 / p)) *
          (ENNReal.ofReal r⁻¹ * Y) ^ (1 / p) := hfinal

/-- `R₂` vanishes for `r > 4/3`: no dilation `t ≤ 2` satisfies `t ≥ 3r/2`. -/
theorem brsRemainderTwo_eq_zero_of_gt {f₀ : ℝ → ℂ} {r : ℝ} (hr : 4 / 3 < r) :
    brsRemainderTwo (absProfile f₀) r = 0 := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) (by simp)
  exfalso
  have ht2 : t ≤ 2 := ht.1.2
  have htr : 3 * r / 2 ≤ t := ht.2
  linarith

/-- The weight of the `r`-integration in BRS Proposition 4.3. -/
theorem lintegral_rpow_Ioc_lt_top {a b : ℝ} (hb : 0 < b) (ha : -1 < a) :
    (∫⁻ r in Ioc (0 : ℝ) b, ENNReal.ofReal (r ^ a)) < ⊤ := by
  have hint : IntegrableOn (fun r : ℝ => r ^ a) (Ioc 0 b) volume := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) ha
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le] at h
    exact h
  have hval : ENNReal.ofReal (∫ r in Ioc (0 : ℝ) b, r ^ a) =
      ∫⁻ r in Ioc (0 : ℝ) b, ENNReal.ofReal (r ^ a) := by
    refine ofReal_integral_eq_lintegral_ofReal hint ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    exact Real.rpow_nonneg (le_of_lt hr.1) _
  rw [← hval]
  exact ENNReal.ofReal_lt_top

/-- **BRS Proposition 4.3** for the non-endpoint range `q < pd`. -/
theorem prop43_brsRemainderTwo {d : ℕ} (hd : 2 ≤ d) {p q : ℝ} (hp : 1 ≤ p)
    (hq : 0 < q) (hqpd : q < p * d) :
    ∃ C : ℝ, 0 < C ∧ ∀ f₀ : ℝ → ℂ, Continuous f₀ →
      (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
          brsRemainderTwo (absProfile f₀) r ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C *
          (∫⁻ s, ENNReal.ofReal s ^ (d - 1) *
            (ENNReal.ofReal ‖f₀ s‖) ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set C₁ : ℝ := (3 : ℝ) ^ (((d : ℝ) - 1) / p) * (2 : ℝ) ^ (1 - 1 / p) with hC₁
  have hC₁pos : 0 < C₁ := by
    rw [hC₁]
    have h1 : (0 : ℝ) < (3 : ℝ) ^ (((d : ℝ) - 1) / p) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 - 1 / p) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  -- the radial weight integral is finite
  set a : ℝ := ((d : ℝ) - 1) - q / p with ha
  have hagt : -1 < a := by
    rw [ha]
    have hqp : q / p < (d : ℝ) := by
      rw [div_lt_iff₀ hp0]
      calc q < p * (d : ℝ) := hqpd
        _ = (d : ℝ) * p := by ring
    linarith
  set K : ENNReal := ∫⁻ r in Ioc (0 : ℝ) (4 / 3), ENNReal.ofReal (r ^ a) with hK
  have hKtop : K ≠ ⊤ := by
    rw [hK]
    exact (lintegral_rpow_Ioc_lt_top (by norm_num) hagt).ne
  refine ⟨C₁ * (K.toReal + 1) ^ (1 / q), by positivity, ?_⟩
  intro f₀ hf₀
  set X : ENNReal := ∫⁻ s, ENNReal.ofReal s ^ (d - 1) *
    (ENNReal.ofReal ‖f₀ s‖) ^ p with hX
  by_cases hXtop : X = ⊤
  · rw [hXtop, ENNReal.top_rpow_of_pos (by positivity : (0 : ℝ) < 1 / p),
      ENNReal.mul_top (by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity)]
    exact le_top
  -- the pointwise bound, supported in `(0, 4/3]`
  have hpoint : ∀ r : ℝ, ENNReal.ofReal r ^ (d - 1) *
      brsRemainderTwo (absProfile f₀) r ^ q ≤
        (Ioc (0 : ℝ) (4 / 3)).indicator
          (fun r => ENNReal.ofReal (r ^ a) *
            ((ENNReal.ofReal C₁) ^ q * X ^ (q / p))) r := by
    intro r
    by_cases hr0 : r ≤ 0
    · have hzero : ENNReal.ofReal r ^ (d - 1) = 0 := by
        rw [ENNReal.ofReal_eq_zero.mpr hr0, zero_pow (by omega : d - 1 ≠ 0)]
      rw [hzero, zero_mul]
      simp
    push Not at hr0
    by_cases hrle : r ≤ 4 / 3
    · have hmem : r ∈ Ioc (0 : ℝ) (4 / 3) := ⟨hr0, hrle⟩
      rw [Set.indicator_of_mem hmem]
      -- (4.5) and monotonicity in the domain of integration
      have h45 := brsRemainderTwo_le_local hd hp hf₀ r
      have hY : (∫⁻ s in Icc (1 / 4 : ℝ) 4, ENNReal.ofReal s ^ (d - 1) *
          (ENNReal.ofReal ‖f₀ s‖) ^ p) ≤ X := by
        rw [hX]
        exact setLIntegral_le_lintegral _ _
      have h45' : brsRemainderTwo (absProfile f₀) r ≤
          ENNReal.ofReal C₁ * (ENNReal.ofReal r⁻¹ * X) ^ (1 / p) := by
        refine le_trans h45 ?_
        rw [hC₁]
        refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by positivity))
        exact mul_le_mul' le_rfl hY
      have hpow : brsRemainderTwo (absProfile f₀) r ^ q ≤
          (ENNReal.ofReal C₁) ^ q * ((ENNReal.ofReal r⁻¹) ^ (q / p) * X ^ (q / p)) := by
        calc brsRemainderTwo (absProfile f₀) r ^ q
            ≤ (ENNReal.ofReal C₁ * (ENNReal.ofReal r⁻¹ * X) ^ (1 / p)) ^ q :=
              ENNReal.rpow_le_rpow h45' hq.le
          _ = (ENNReal.ofReal C₁) ^ q *
                ((ENNReal.ofReal r⁻¹) ^ (q / p) * X ^ (q / p)) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul,
                ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p * q),
                show 1 / p * q = q / p by ring]
      have hweight : ENNReal.ofReal r ^ (d - 1) * (ENNReal.ofReal r⁻¹) ^ (q / p) =
          ENNReal.ofReal (r ^ a) := by
        have h1 : ENNReal.ofReal r ^ (d - 1) = ENNReal.ofReal (r ^ ((d : ℝ) - 1)) := by
          rw [← ENNReal.ofReal_pow hr0.le]
          congr 1
          have hc := pow_sub_eq_rpow hr0 (D := d) (k := 1) (by omega)
          simpa using hc
        have h2 : (ENNReal.ofReal r⁻¹) ^ (q / p) =
            ENNReal.ofReal (r ^ (-(q / p))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
          congr 1
          rw [← Real.rpow_neg_one r, ← Real.rpow_mul hr0.le]
          congr 1
          ring
        rw [h1, h2, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr0.le _),
          ← Real.rpow_add hr0, ha]
        congr 1
      calc ENNReal.ofReal r ^ (d - 1) * brsRemainderTwo (absProfile f₀) r ^ q
          ≤ ENNReal.ofReal r ^ (d - 1) *
              ((ENNReal.ofReal C₁) ^ q *
                ((ENNReal.ofReal r⁻¹) ^ (q / p) * X ^ (q / p))) :=
            mul_le_mul' le_rfl hpow
        _ = (ENNReal.ofReal r ^ (d - 1) * (ENNReal.ofReal r⁻¹) ^ (q / p)) *
              ((ENNReal.ofReal C₁) ^ q * X ^ (q / p)) := by ring
        _ = ENNReal.ofReal (r ^ a) * ((ENNReal.ofReal C₁) ^ q * X ^ (q / p)) := by
            rw [hweight]
    · push Not at hrle
      rw [brsRemainderTwo_eq_zero_of_gt hrle, ENNReal.zero_rpow_of_pos hq, mul_zero]
      simp
  -- integrate the pointwise bound
  have hXpow : X ^ (q / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hXtop
  have hconst : (ENNReal.ofReal C₁) ^ q * X ^ (q / p) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top) hXpow
  have hint : (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
      brsRemainderTwo (absProfile f₀) r ^ q) ≤
        K * ((ENNReal.ofReal C₁) ^ q * X ^ (q / p)) := by
    calc (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
          brsRemainderTwo (absProfile f₀) r ^ q)
        ≤ ∫⁻ r, (Ioc (0 : ℝ) (4 / 3)).indicator
            (fun r => ENNReal.ofReal (r ^ a) *
              ((ENNReal.ofReal C₁) ^ q * X ^ (q / p))) r := lintegral_mono hpoint
      _ = ∫⁻ r in Ioc (0 : ℝ) (4 / 3), ENNReal.ofReal (r ^ a) *
            ((ENNReal.ofReal C₁) ^ q * X ^ (q / p)) :=
          lintegral_indicator measurableSet_Ioc _
      _ = K * ((ENNReal.ofReal C₁) ^ q * X ^ (q / p)) := by
          rw [hK, ← lintegral_mul_const' _ _ hconst]
  -- take the `q`-th root
  have hKle : K ≤ ENNReal.ofReal (K.toReal + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_toReal hKtop,
      ENNReal.ofReal_one]
    exact le_self_add
  calc (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
        brsRemainderTwo (absProfile f₀) r ^ q) ^ (1 / q)
      ≤ (ENNReal.ofReal (K.toReal + 1) *
          ((ENNReal.ofReal C₁) ^ q * X ^ (q / p))) ^ (1 / q) := by
        refine ENNReal.rpow_le_rpow (le_trans hint ?_) (by positivity)
        exact mul_le_mul' hKle le_rfl
    _ = ENNReal.ofReal (C₁ * (K.toReal + 1) ^ (1 / q)) * X ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / q),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / q),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          mul_one_div_cancel hq.ne', ENNReal.rpow_one,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ENNReal.ofReal_mul hC₁pos.le]
        rw [show q / p * (1 / q) = 1 / p by field_simp]
        ring

/-- An interval integral is dominated by any `ℝ≥0∞` majorant of its integrand,
with no integrability hypothesis: if the integrand fails to be integrable the
Bochner integral vanishes by convention. -/
theorem ofReal_norm_intervalIntegral_le_lintegral {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → ℂ) (H : ℝ → ENNReal)
    (hH : ∀ s ∈ Icc a b, ENNReal.ofReal ‖F s‖ ≤ H s) :
    ENNReal.ofReal ‖∫ s in a..b, F s‖ ≤ ∫⁻ s in Icc a b, H s := by
  by_cases hint : IntervalIntegrable F volume a b
  · have hnormint : IntegrableOn (fun s => ‖F s‖) (Icc a b) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      exact hint.norm
    calc ENNReal.ofReal ‖∫ s in a..b, F s‖
        ≤ ENNReal.ofReal (∫ s in a..b, ‖F s‖) :=
          ENNReal.ofReal_le_ofReal
            (intervalIntegral.norm_integral_le_integral_norm hab)
      _ = ∫⁻ s in Icc a b, ENNReal.ofReal ‖F s‖ := by
          rw [intervalIntegral.integral_of_le hab,
            ← MeasureTheory.integral_Icc_eq_integral_Ioc]
          exact ofReal_integral_eq_lintegral_ofReal hnormint
            (ae_of_all _ fun s => norm_nonneg _)
      _ ≤ ∫⁻ s in Icc a b, H s := setLIntegral_mono' measurableSet_Icc hH
  · rw [intervalIntegral.integral_undef hint]
    simp

/-! ### The support of the main term `𝔐_p`

The constraints `t ∈ E ⊆ [1,2]` and `r/2 < t < 3r/2` confine the radius to
`(2/3, 4)`. -/

theorem brsMainMaximal_eq_zero_of_le {d : ℕ} {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    {p : ℝ} (g : ℝ → ℂ) {r : ℝ} (hr : r ≤ 2 / 3) :
    brsMainMaximal d E p g r = 0 := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) (by simp)
  exfalso
  have ht1 : (1 : ℝ) ≤ t := (hE ht.1).1
  have ht2 : t < 3 * r / 2 := ht.2.2
  linarith

theorem brsMainMaximal_eq_zero_of_ge {d : ℕ} {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    {p : ℝ} (g : ℝ → ℂ) {r : ℝ} (hr : 4 ≤ r) :
    brsMainMaximal d E p g r = 0 := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) (by simp)
  exfalso
  have ht2 : t ≤ 2 := (hE ht.1).2
  have htr : r / 2 < t := ht.2.1
  linarith

/-- For `p > p_d = d/(d-1)` the conjugate exponent satisfies `p' < d`. -/
theorem conjExponent_lt_of_lt {d : ℕ} (hd : 2 ≤ d) {p : ℝ}
    (hpd : (d : ℝ) / ((d : ℝ) - 1) < p) : Real.conjExponent p < (d : ℝ) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hp1 : 1 < p := by
    have h1 : (1 : ℝ) < (d : ℝ) / ((d : ℝ) - 1) := by
      rw [lt_div_iff₀ hd1]
      linarith
    linarith
  rw [Real.conjExponent, div_lt_iff₀ (by linarith : (0 : ℝ) < p - 1)]
  rw [div_lt_iff₀ hd1] at hpd
  nlinarith [hpd]

/-- The `p'`-th power of the kernel weight is integrable on `[0,6]` exactly when
`p > p_d = d/(d-1)`. -/
theorem lintegral_kernel_weight_lt_top {d : ℕ} (hd : 2 ≤ d) {p : ℝ}
    (hpd : (d : ℝ) / ((d : ℝ) - 1) < p) :
    (∫⁻ s in Icc (0 : ℝ) 6,
        ENNReal.ofReal (s ^ (((d : ℝ) - 1) - Real.conjExponent p))) < ⊤ := by
  have hexp : -1 < ((d : ℝ) - 1) - Real.conjExponent p := by
    have := conjExponent_lt_of_lt hd hpd
    linarith
  have hint : IntegrableOn
      (fun s : ℝ => s ^ (((d : ℝ) - 1) - Real.conjExponent p)) (Icc 0 6) volume := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 6) hexp
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at h
    exact h
  have hval : ENNReal.ofReal
      (∫ s in Icc (0 : ℝ) 6, s ^ (((d : ℝ) - 1) - Real.conjExponent p)) =
      ∫⁻ s in Icc (0 : ℝ) 6,
        ENNReal.ofReal (s ^ (((d : ℝ) - 1) - Real.conjExponent p)) := by
    refine ofReal_integral_eq_lintegral_ofReal hint ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
    exact Real.rpow_nonneg hs.1 _
  rw [← hval]
  exact ENNReal.ofReal_lt_top

/-- The kernel weight raised to `p'` is the power appearing above. -/
theorem kernel_weight_rpow {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp1 : 1 < p) {s : ℝ}
    (hs : 0 ≤ s) :
    (ENNReal.ofReal (s ^ (((d : ℝ) - 1) * (1 - 1 / p) - 1))) ^
        Real.conjExponent p =
      ENNReal.ofReal (s ^ (((d : ℝ) - 1) - Real.conjExponent p)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hp1ne : p - 1 ≠ 0 := by
    intro hcon
    rw [sub_eq_zero] at hcon
    exact absurd hcon.symm hp1.ne
  have hp'pos : 0 < Real.conjExponent p := by
    rw [Real.conjExponent]
    exact div_pos hp0 (by linarith)
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs _) hp'pos.le,
    ← Real.rpow_mul hs]
  congr 2
  rw [Real.conjExponent]
  field_simp

theorem setLIntegral_Icc_zero_le_Ioi {b : ℝ} (H : ℝ → ENNReal) :
    (∫⁻ s in Icc (0 : ℝ) b, H s) ≤ ∫⁻ s in Ioi (0 : ℝ), H s := by
  calc (∫⁻ s in Icc (0 : ℝ) b, H s) = ∫⁻ s in Ioc (0 : ℝ) b, H s :=
        (setLIntegral_congr Ioc_ae_eq_Icc).symm
    _ ≤ ∫⁻ s in Ioi (0 : ℝ), H s := lintegral_mono_set Ioc_subset_Ioi_self

/-- **The pointwise bound of BRS Proposition 4.4.**  For `p > p_d` the kernel
weight lies in `L^{p'}` of the relevant window, so `𝔐_p g` is bounded by a
constant multiple of the `L^p` norm of `g`. -/
theorem brsMainMaximal_le_of_lt {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p : ℝ} (hpd : (d : ℝ) / ((d : ℝ) - 1) < p)
    {g : ℝ → ℂ} (hg : Measurable g) (r : ℝ) :
    brsMainMaximal d E p g r ≤
      ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
        ((∫⁻ s in Icc (0 : ℝ) 6,
            ENNReal.ofReal (s ^ (((d : ℝ) - 1) - Real.conjExponent p))) ^
              (1 / Real.conjExponent p) *
          (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hp1 : 1 < p := by
    have h1 : (1 : ℝ) < (d : ℝ) / ((d : ℝ) - 1) := by
      rw [lt_div_iff₀ hd1]
      linarith
    linarith
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hp'pos : 0 < Real.conjExponent p := by
    rw [Real.conjExponent]
    exact div_pos hp0 (by linarith)
  have hpq : (Real.conjExponent p).HolderConjugate p :=
    (Real.HolderConjugate.conjExponent hp1).symm
  set e : ℝ := ((d : ℝ) - 1) * (1 - 1 / p) - 1 with hedef
  set W : ENNReal := ∫⁻ s in Icc (0 : ℝ) 6,
    ENNReal.ofReal (s ^ (((d : ℝ) - 1) - Real.conjExponent p)) with hW
  set G : ENNReal := ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ p with hG
  refine iSup₂_le fun t ht => ?_
  obtain ⟨htE, htlow, hthigh⟩ := ht
  have htIcc : t ∈ Icc (1 : ℝ) 2 := hE htE
  have ht1 : (1 : ℝ) ≤ t := htIcc.1
  have ht2 : t ≤ 2 := htIcc.2
  have hrlow : 2 / 3 < r := by linarith
  have hrpos : 0 < r := by linarith
  have hab : |r - t| ≤ r + t := by
    rw [abs_le]
    constructor <;> linarith
  have hsub : Icc |r - t| (r + t) ⊆ Icc (0 : ℝ) 6 := by
    intro s hs
    refine ⟨le_trans (abs_nonneg _) hs.1, ?_⟩
    have := hs.2
    linarith
  -- the radial factor
  have hradial : r ^ (1 - (d : ℝ)) ≤ (2 / 3 : ℝ) ^ (1 - (d : ℝ)) := by
    refine Real.rpow_le_rpow_of_nonpos (by norm_num) hrlow.le (by linarith)
  -- the inner integral, dominated by a lintegral
  have hinner : ENNReal.ofReal
      ‖∫ s in |r - t|..(r + t), ((s ^ e : ℝ) : ℂ) * g s‖ ≤
      ∫⁻ s in Icc (0 : ℝ) 6,
        ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖ := by
    refine le_trans (ofReal_norm_intervalIntegral_le_lintegral hab _
      (fun s => ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖) ?_) ?_
    · intro s hs
      have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hs.1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hs0 _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hs0 _)]
    · exact lintegral_mono_set hsub
  -- Hölder
  have hholder : (∫⁻ s in Icc (0 : ℝ) 6,
      ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖) ≤
      W ^ (1 / Real.conjExponent p) * G ^ (1 / p) := by
    have hmeas1 : Measurable fun s : ℝ => ENNReal.ofReal (s ^ e) := by fun_prop
    have hmeas2 : Measurable fun s : ℝ => ENNReal.ofReal ‖g s‖ :=
      hg.norm.ennreal_ofReal
    have hkey := ENNReal.lintegral_mul_le_Lp_mul_Lq
      (volume.restrict (Icc (0 : ℝ) 6)) hpq hmeas1.aemeasurable hmeas2.aemeasurable
    simp only [Pi.mul_apply] at hkey
    refine le_trans hkey ?_
    have hWeq : (∫⁻ s in Icc (0 : ℝ) 6,
        (ENNReal.ofReal (s ^ e)) ^ Real.conjExponent p) = W := by
      rw [hW]
      refine setLIntegral_congr_fun measurableSet_Icc ?_
      intro s hs
      rw [hedef]
      exact kernel_weight_rpow hd hp1 hs.1
    have hGle : (∫⁻ s in Icc (0 : ℝ) 6, (ENNReal.ofReal ‖g s‖) ^ p) ≤ G := by
      rw [hG]
      exact setLIntegral_Icc_zero_le_Ioi _
    rw [hWeq]
    exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hGle (by positivity))
  -- combine
  calc ENNReal.ofReal (r ^ (1 - (d : ℝ)) *
        ‖∫ s in |r - t|..(r + t), ((s ^ e : ℝ) : ℂ) * g s‖)
      = ENNReal.ofReal (r ^ (1 - (d : ℝ))) *
          ENNReal.ofReal ‖∫ s in |r - t|..(r + t), ((s ^ e : ℝ) : ℂ) * g s‖ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hrpos.le _)]
    _ ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
          (W ^ (1 / Real.conjExponent p) * G ^ (1 / p)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hradial) (le_trans hinner hholder)

/-- The radial weight over the support of `𝔐_p` is finite. -/
theorem lintegral_radial_weight_Ioo_lt_top {d : ℕ} :
    (∫⁻ r in Ioo (2 / 3 : ℝ) 4, ENNReal.ofReal r ^ (d - 1)) < ⊤ := by
  have hbound : ∀ r ∈ Ioo (2 / 3 : ℝ) 4,
      ENNReal.ofReal r ^ (d - 1) ≤ ENNReal.ofReal ((4 : ℝ) ^ (d - 1)) := by
    intro r hr
    rw [← ENNReal.ofReal_pow (by linarith [hr.1] : (0 : ℝ) ≤ r)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine pow_le_pow_left₀ (by linarith [hr.1]) ?_ _
    exact le_of_lt hr.2
  calc (∫⁻ r in Ioo (2 / 3 : ℝ) 4, ENNReal.ofReal r ^ (d - 1))
      ≤ ∫⁻ _r in Ioo (2 / 3 : ℝ) 4, ENNReal.ofReal ((4 : ℝ) ^ (d - 1)) :=
        setLIntegral_mono' measurableSet_Ioo hbound
    _ = ENNReal.ofReal ((4 : ℝ) ^ (d - 1)) * volume (Ioo (2 / 3 : ℝ) 4) :=
        setLIntegral_const _ _
    _ < ⊤ := by
        rw [Real.volume_Ioo]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **BRS Proposition 4.4.**  For `p > p_d = d/(d-1)` and every `0 < q < ∞` the
main term `𝔐_p` maps `L^p(ds)` to `L^q(r^{d-1} dr)`. -/
theorem prop44_brsMainMaximal {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p q : ℝ} (hpd : (d : ℝ) / ((d : ℝ) - 1) < p)
    (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℂ, Measurable g →
      (∫⁻ r, ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C *
          (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hp1 : 1 < p := by
    have h1 : (1 : ℝ) < (d : ℝ) / ((d : ℝ) - 1) := by
      rw [lt_div_iff₀ hd1]
      linarith
    linarith
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hp'pos : 0 < Real.conjExponent p := by
    rw [Real.conjExponent]
    exact div_pos hp0 (by linarith)
  set W : ENNReal := ∫⁻ s in Icc (0 : ℝ) 6,
    ENNReal.ofReal (s ^ (((d : ℝ) - 1) - Real.conjExponent p)) with hW
  have hWtop : W ≠ ⊤ := by
    rw [hW]
    exact (lintegral_kernel_weight_lt_top hd hpd).ne
  set M : ENNReal := ∫⁻ r in Ioo (2 / 3 : ℝ) 4, ENNReal.ofReal r ^ (d - 1) with hM
  have hMtop : M ≠ ⊤ := by
    rw [hM]
    exact (lintegral_radial_weight_Ioo_lt_top (d := d)).ne
  set A : ℝ := (2 / 3 : ℝ) ^ (1 - (d : ℝ)) with hA
  have hApos : 0 < A := by
    rw [hA]
    exact Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨A * (W.toReal + 1) ^ (1 / Real.conjExponent p) *
    (M.toReal + 1) ^ (1 / q), by positivity, ?_⟩
  intro g hg
  set G : ENNReal := ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ p with hG
  by_cases hGtop : G = ⊤
  · rw [hGtop, ENNReal.top_rpow_of_pos (by positivity : (0 : ℝ) < 1 / p),
      ENNReal.mul_top (by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity)]
    exact le_top
  set B : ENNReal := ENNReal.ofReal A *
    (W ^ (1 / Real.conjExponent p) * G ^ (1 / p)) with hB
  have hBtop : B ≠ ⊤ := by
    rw [hB]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ ?_)
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hWtop
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hGtop
  have hBpow : B ^ q ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq.le hBtop
  -- the pointwise bound, supported in `(2/3, 4)`
  have hpoint : ∀ r : ℝ, ENNReal.ofReal r ^ (d - 1) *
      brsMainMaximal d E p g r ^ q ≤
        (Ioo (2 / 3 : ℝ) 4).indicator
          (fun r => ENNReal.ofReal r ^ (d - 1) * B ^ q) r := by
    intro r
    by_cases hr1 : r ≤ 2 / 3
    · rw [brsMainMaximal_eq_zero_of_le hE g hr1, ENNReal.zero_rpow_of_pos hq,
        mul_zero]
      simp
    push Not at hr1
    by_cases hr2 : 4 ≤ r
    · rw [brsMainMaximal_eq_zero_of_ge hE g hr2, ENNReal.zero_rpow_of_pos hq,
        mul_zero]
      simp
    push Not at hr2
    have hmem : r ∈ Ioo (2 / 3 : ℝ) 4 := ⟨hr1, hr2⟩
    rw [Set.indicator_of_mem hmem]
    refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ hq.le)
    rw [hB, hA, hW, hG]
    exact brsMainMaximal_le_of_lt hd hE hpd hg r
  -- integrate
  have hint : (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
      brsMainMaximal d E p g r ^ q) ≤ M * B ^ q := by
    calc (∫⁻ r, ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q)
        ≤ ∫⁻ r, (Ioo (2 / 3 : ℝ) 4).indicator
            (fun r => ENNReal.ofReal r ^ (d - 1) * B ^ q) r := lintegral_mono hpoint
      _ = ∫⁻ r in Ioo (2 / 3 : ℝ) 4, ENNReal.ofReal r ^ (d - 1) * B ^ q :=
          lintegral_indicator measurableSet_Ioo _
      _ = M * B ^ q := by
          rw [hM, ← lintegral_mul_const' _ _ hBpow]
  -- take the `q`-th root and bound the constants
  have hWle : W ^ (1 / Real.conjExponent p) ≤
      ENNReal.ofReal ((W.toReal + 1) ^ (1 / Real.conjExponent p)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_toReal hWtop,
      ENNReal.ofReal_one]
    exact le_self_add
  have hMle : M ^ (1 / q) ≤ ENNReal.ofReal ((M.toReal + 1) ^ (1 / q)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_toReal hMtop,
      ENNReal.ofReal_one]
    exact le_self_add
  calc (∫⁻ r, ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q) ^ (1 / q)
      ≤ (M * B ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow hint (by positivity)
    _ = M ^ (1 / q) * B := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / q),
          ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]
    _ = M ^ (1 / q) * (ENNReal.ofReal A * W ^ (1 / Real.conjExponent p)) *
          G ^ (1 / p) := by
        rw [hB]
        ring
    _ ≤ ENNReal.ofReal ((M.toReal + 1) ^ (1 / q)) *
          (ENNReal.ofReal A *
            ENNReal.ofReal ((W.toReal + 1) ^ (1 / Real.conjExponent p))) *
          G ^ (1 / p) := by
        refine mul_le_mul' (mul_le_mul' hMle (mul_le_mul' le_rfl hWle)) le_rfl
    _ = ENNReal.ofReal (A * (W.toReal + 1) ^ (1 / Real.conjExponent p) *
          (M.toReal + 1) ^ (1 / q)) * G ^ (1 / p) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-! ## The dyadic neighbourhoods (4.6) -/

section DyadicShells

open Auto.FractalDimensions

/-! ## BRS (4.6): the dyadic neighbourhoods of the dilation set

`U_n` is the `2^{-n+1}`-neighbourhood of `E` and `D_n = U_n \ U_{n+1}` is the
dyadic shell where the distance to `E` is of size `2^{-n}`.  On `D_n` the
integration window of `𝔐_p` is cut off at `2^{-n}`, which is what makes the
`p < p_d` estimate possible. -/

/-- The `2^{-n+1}`-neighbourhood of the dilation set, BRS (4.6). -/
def brsU (E : Set ℝ) (n : ℕ) : Set ℝ :=
  {r | Metric.infDist r E ≤ 2 * (2 : ℝ) ^ (-(n : ℤ))}

/-- The dyadic shell `D_n = U_n \ U_{n+1}` of BRS (4.6). -/
def brsD (E : Set ℝ) (n : ℕ) : Set ℝ := brsU E n \ brsU E (n + 1)

theorem measurableSet_brsU (E : Set ℝ) (n : ℕ) : MeasurableSet (brsU E n) := by
  have hcont : Continuous fun r : ℝ => Metric.infDist r E :=
    Metric.continuous_infDist_pt E
  exact measurableSet_le hcont.measurable measurable_const

theorem measurableSet_brsD (E : Set ℝ) (n : ℕ) : MeasurableSet (brsD E n) :=
  (measurableSet_brsU E n).diff (measurableSet_brsU E (n + 1))

/-- The neighbourhoods decrease. -/
theorem brsU_subset_of_le (E : Set ℝ) {m n : ℕ} (hmn : m ≤ n) :
    brsU E n ⊆ brsU E m := by
  intro r hr
  have hpow : (2 : ℝ) ^ (-(n : ℤ)) ≤ (2 : ℝ) ^ (-(m : ℤ)) := by
    refine zpow_le_zpow_right₀ (by norm_num) ?_
    omega
  have h : Metric.infDist r E ≤ 2 * (2 : ℝ) ^ (-(n : ℤ)) := hr
  show Metric.infDist r E ≤ 2 * (2 : ℝ) ^ (-(m : ℤ))
  linarith

/-- The shells `D_n` are pairwise disjoint. -/
theorem brsD_disjoint (E : Set ℝ) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (brsD E m) (brsD E n) := by
  rcases lt_or_gt_of_ne hmn with h | h
  · refine Set.disjoint_left.mpr fun r hrm hrn => ?_
    exact hrm.2 (brsU_subset_of_le E (by omega) hrn.1)
  · refine Set.disjoint_left.mpr fun r hrm hrn => ?_
    exact hrn.2 (brsU_subset_of_le E (by omega) hrm.1)

/-- Points of `U_0` outside every shell are at distance zero from `E`. -/
theorem infDist_eq_zero_of_notMem_iUnion_brsD {E : Set ℝ} {r : ℝ}
    (hr : r ∈ brsU E 0) (hnot : r ∉ ⋃ n, brsD E n) : Metric.infDist r E = 0 := by
  have hall : ∀ n : ℕ, r ∈ brsU E n := by
    intro n
    induction n with
    | zero => exact hr
    | succ k ih =>
        by_contra hcon
        exact hnot (Set.mem_iUnion.mpr ⟨k, ⟨ih, hcon⟩⟩)
  by_contra hne
  have hpos : 0 < Metric.infDist r E :=
    lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / Metric.infDist r E)
    (by norm_num : (1 : ℝ) < 2)
  have hpown : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h2 : 2 * (2 : ℝ) ^ (-(n : ℤ)) < Metric.infDist r E := by
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_lt_iff₀ hpown]
    rw [div_lt_iff₀ hpos] at hn
    nlinarith [hn]
  exact absurd (hall n) (not_le.mpr h2)

/-- **The measure of the dyadic neighbourhood**, in terms of the covering
number at the same scale. -/
theorem volume_brsU_le {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    (n : ℕ) :
    volume (brsU E n) ≤
      ENNReal.ofReal (7 * (2 : ℝ) ^ (-(n : ℤ))) *
        (intervalCoveringNumber E ((2 : ℝ) ^ (-(n : ℤ))) : ℝ≥0∞) := by
  set δ : ℝ := (2 : ℝ) ^ (-(n : ℤ)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    positivity
  obtain ⟨ι, hι, hcard⟩ := exists_intervalCover_card_eq_intervalCoveringNumber hE hδpos
  have hsub : brsU E n ⊆ ⋃ a ∈ ι, Icc (a - δ / 2 - 3 * δ) (a + δ / 2 + 3 * δ) := by
    intro r hr
    have hdist : Metric.infDist r E ≤ 2 * δ := hr
    obtain ⟨t, htE, hrt⟩ : ∃ t ∈ E, dist r t < 3 * δ := by
      have hlt : Metric.infDist r E < 3 * δ := by linarith
      exact (Metric.infDist_lt_iff hEne).mp hlt
    obtain ⟨a, haι, hat⟩ : ∃ a ∈ ι, t ∈ Icc (a - δ / 2) (a + δ / 2) := by
      have hcov := hι htE
      simpa only [Set.mem_iUnion, exists_prop] using hcov
    refine Set.mem_biUnion haι ?_
    rw [Real.dist_eq, abs_lt] at hrt
    exact ⟨by linarith [hat.1, hrt.1], by linarith [hat.2, hrt.2]⟩
  calc volume (brsU E n)
      ≤ volume (⋃ a ∈ ι, Icc (a - δ / 2 - 3 * δ) (a + δ / 2 + 3 * δ)) :=
        measure_mono hsub
    _ ≤ ∑ a ∈ ι, volume (Icc (a - δ / 2 - 3 * δ) (a + δ / 2 + 3 * δ)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _a ∈ ι, ENNReal.ofReal (7 * δ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Real.volume_Icc]
        congr 1
        ring
    _ = (ι.card : ℝ≥0∞) * ENNReal.ofReal (7 * δ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (7 * δ) * (intervalCoveringNumber E δ : ℝ≥0∞) := by
        rw [hcard, mul_comm]

end DyadicShells

/-- On the shell `D_n` the distance to `E` exceeds `2^{-n}`. -/
theorem lt_infDist_of_mem_brsD {E : Set ℝ} {n : ℕ} {r : ℝ} (hr : r ∈ brsD E n) :
    (2 : ℝ) ^ (-(n : ℤ)) < Metric.infDist r E := by
  have hnot : ¬ (Metric.infDist r E ≤ 2 * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))) := hr.2
  push Not at hnot
  have hid : 2 * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(n : ℤ)) := by
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hcast, neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    field_simp
  rwa [hid] at hnot

/-- **The window cutoff of BRS Proposition 4.5.**  On the shell `D_n` the
integration window of `𝔐_p` starts at `2^{-n}`, since every admissible
dilation `t` satisfies `|r - t| ≥ dist(r, E) > 2^{-n}`. -/
theorem brsMainMaximal_le_on_brsD {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p : ℝ} (g : ℝ → ℂ) {n : ℕ} {r : ℝ}
    (hrD : r ∈ brsD E n) :
    brsMainMaximal d E p g r ≤
      ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
        ∫⁻ s in Icc ((2 : ℝ) ^ (-(n : ℤ))) 6,
          ENNReal.ofReal (s ^ (((d : ℝ) - 1) * (1 - 1 / p) - 1)) *
            ENNReal.ofReal ‖g s‖ := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set e : ℝ := ((d : ℝ) - 1) * (1 - 1 / p) - 1 with hedef
  have hdist := lt_infDist_of_mem_brsD hrD
  refine iSup₂_le fun t ht => ?_
  obtain ⟨htE, htlow, hthigh⟩ := ht
  have htIcc : t ∈ Icc (1 : ℝ) 2 := hE htE
  have ht1 : (1 : ℝ) ≤ t := htIcc.1
  have ht2 : t ≤ 2 := htIcc.2
  have hrlow : 2 / 3 < r := by linarith
  have hrpos : 0 < r := by linarith
  have hab : |r - t| ≤ r + t := by
    rw [abs_le]
    constructor <;> linarith
  -- the lower cutoff
  have hcut : (2 : ℝ) ^ (-(n : ℤ)) ≤ |r - t| := by
    have hle : Metric.infDist r E ≤ dist r t := Metric.infDist_le_dist_of_mem htE
    rw [Real.dist_eq] at hle
    linarith
  have hsub : Icc |r - t| (r + t) ⊆ Icc ((2 : ℝ) ^ (-(n : ℤ))) 6 := by
    intro s hs
    refine ⟨le_trans hcut hs.1, ?_⟩
    have := hs.2
    linarith
  -- the radial factor
  have hradial : r ^ (1 - (d : ℝ)) ≤ (2 / 3 : ℝ) ^ (1 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hrlow.le (by linarith)
  -- the inner integral
  have hinner : ENNReal.ofReal
      ‖∫ s in |r - t|..(r + t), ((s ^ e : ℝ) : ℂ) * g s‖ ≤
      ∫⁻ s in Icc ((2 : ℝ) ^ (-(n : ℤ))) 6,
        ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖ := by
    refine le_trans (ofReal_norm_intervalIntegral_le_lintegral hab _
      (fun s => ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖) ?_) ?_
    · intro s hs
      have hs0 : 0 ≤ s := le_trans (abs_nonneg _) hs.1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hs0 _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hs0 _)]
    · exact lintegral_mono_set hsub
  calc ENNReal.ofReal (r ^ (1 - (d : ℝ)) *
        ‖∫ s in |r - t|..(r + t), ((s ^ e : ℝ) : ℂ) * g s‖)
      = ENNReal.ofReal (r ^ (1 - (d : ℝ))) *
          ENNReal.ofReal ‖∫ s in |r - t|..(r + t), ((s ^ e : ℝ) : ℂ) * g s‖ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hrpos.le _)]
    _ ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
          ∫⁻ s in Icc ((2 : ℝ) ^ (-(n : ℤ))) 6,
            ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖ :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hradial) hinner

/-! ## Discrete summation tools

Proposition 4.5 needs two summation inequalities.  Both are obtained by
running the `ℝ≥0∞` integral machinery against the counting measure on `ℕ`,
which turns `lintegral` into `tsum`. -/

/-- The embedding `ℓ^p ⊆ ℓ^q` for `0 < p ≤ q`. -/
theorem tsum_rpow_le_tsum_rpow (G : ℕ → ENNReal) {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) :
    (∑' k, G k ^ q) ^ (1 / q) ≤ (∑' k, G k ^ p) ^ (1 / p) := by
  have hq0 : 0 < q := lt_of_lt_of_le hp hpq
  set S : ENNReal := (∑' k, G k ^ p) ^ (1 / p) with hS
  have hSpow : S ^ p = ∑' k, G k ^ p := by
    rw [hS, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  have hle : ∀ k, G k ≤ S := by
    intro k
    have h1 : G k ^ p ≤ ∑' k, G k ^ p := ENNReal.le_tsum k
    calc G k = (G k ^ p) ^ (1 / p) := by
          rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]
      _ ≤ S := by
          rw [hS]
          exact ENNReal.rpow_le_rpow h1 (by positivity)
  have hstep : ∀ k, G k ^ q ≤ S ^ (q - p) * G k ^ p := by
    intro k
    have hsplit : G k ^ q = G k ^ (q - p) * G k ^ p := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) hp.le]
      congr 1
      ring
    rw [hsplit]
    exact mul_le_mul' (ENNReal.rpow_le_rpow (hle k) (by linarith)) le_rfl
  calc (∑' k, G k ^ q) ^ (1 / q)
      ≤ (∑' k, S ^ (q - p) * G k ^ p) ^ (1 / q) := by
        refine ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum hstep) (by positivity)
    _ = (S ^ (q - p) * ∑' k, G k ^ p) ^ (1 / q) := by rw [ENNReal.tsum_mul_left]
    _ = (S ^ q) ^ (1 / q) := by
        rw [← hSpow, ← ENNReal.rpow_add_of_nonneg _ _ (by linarith) hp.le]
        congr 2
        ring
    _ = S := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

/-- The counting-measure representation of a weighted sum. -/
theorem lintegral_withDensity_count (c G : ℕ → ENNReal) :
    (∫⁻ x, G x ∂((Measure.count : Measure ℕ).withDensity c)) = ∑' x, c x * G x := by
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_from_top) (measurable_from_top)]
  simp only [Pi.mul_apply]
  exact lintegral_count _

/-- **Weighted Hölder for sums.**  For `q ≥ 1` a weighted sum is bounded by the
weighted `ℓ^q` norm times a power of the total weight. -/
theorem tsum_weighted_le (c G : ℕ → ENNReal) {q : ℝ} (hq : 1 ≤ q) :
    (∑' j, c j * G j) ≤
      (∑' j, c j * G j ^ q) ^ (1 / q) * (∑' j, c j) ^ (1 - 1 / q) := by
  set μ : Measure ℕ := (Measure.count : Measure ℕ).withDensity c with hμ
  have huniv : μ univ = ∑' j, c j := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact lintegral_count _
  have hkey := lintegral_le_rpow_mul_measure_univ (μ := μ) (Φ := G)
    measurable_from_top hq
  rw [lintegral_withDensity_count c G, huniv] at hkey
  refine le_trans hkey ?_
  refine mul_le_mul' (ENNReal.rpow_le_rpow (le_of_eq ?_) (by positivity)) le_rfl
  rw [hμ]
  have hG : (∫⁻ x, G x ^ q ∂((Measure.count : Measure ℕ).withDensity c)) =
      ∑' x, c x * G x ^ q :=
    lintegral_withDensity_count c (fun x => G x ^ q)
  exact hG

/-! ## The dyadic blocks of the profile variable

The window `[2^{-n}, 6]` of `𝔐_p` on the shell `D_n` is covered by the dyadic
blocks `[3·2^{-k}, 6·2^{-k}]`, `k ≤ n + 2`. -/

/-- The dyadic block `[3·2^{-k}, 6·2^{-k}]` of the profile variable. -/
def brsBlock (k : ℕ) : Set ℝ :=
  Icc (3 * (2 : ℝ) ^ (-(k : ℤ))) (6 * (2 : ℝ) ^ (-(k : ℤ)))

theorem brsBlock_pos {k : ℕ} {s : ℝ} (hs : s ∈ brsBlock k) : 0 < s := by
  have h := hs.1
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(k : ℤ)) := by positivity
  nlinarith [hpow]

theorem volume_brsBlock (k : ℕ) :
    volume (brsBlock k) = ENNReal.ofReal (3 * (2 : ℝ) ^ (-(k : ℤ))) := by
  rw [brsBlock, Real.volume_Icc]
  congr 1
  ring

/-- The window on the shell `D_n` is covered by the first `n + 3` blocks. -/
theorem window_subset_iUnion_brsBlock (n : ℕ) :
    Icc ((2 : ℝ) ^ (-(n : ℤ))) 6 ⊆ ⋃ k ∈ Finset.range (n + 3), brsBlock k := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs1
  -- choose the block containing `s`
  have hexists : ∃ k : ℕ, k < n + 3 ∧ s ∈ brsBlock k := by
    -- the blocks `[3·2^{-k}, 6·2^{-k}]` for `k ≤ n+2` cover `[2^{-n}, 6]`
    by_contra hcon
    push Not at hcon
    have hmono : ∀ k : ℕ, k < n + 3 → s ∉ brsBlock k := by
      intro k hk
      exact hcon k hk
    -- descend from the top block to a contradiction
    have hstep : ∀ k : ℕ, k < n + 3 → s ≤ 6 * (2 : ℝ) ^ (-(k : ℤ)) →
        s < 3 * (2 : ℝ) ^ (-(k : ℤ)) := by
      intro k hk hle
      by_contra hgt
      push Not at hgt
      exact hmono k hk ⟨hgt, hle⟩
    have hall : ∀ k : ℕ, k < n + 3 → s < 3 * (2 : ℝ) ^ (-(k : ℤ)) := by
      intro k hk
      induction k with
      | zero =>
          refine hstep 0 hk ?_
          simpa using hs2
      | succ j ih =>
          refine hstep (j + 1) hk ?_
          have hj : j < n + 3 := by omega
          have hprev := ih hj
          have hid : 3 * (2 : ℝ) ^ (-(j : ℤ)) = 6 * (2 : ℝ) ^ (-((j : ℤ) + 1)) := by
            rw [neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            norm_num
            ring
          have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
          rw [hcast, ← hid]
          exact hprev.le
    have hlast := hall (n + 2) (by omega)
    have hid2 : 3 * (2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
      have hcast : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
      have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℤ)) := by positivity
      have hsplit : (2 : ℝ) ^ (-((n : ℤ) + 2)) =
          (2 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ (-2 : ℤ) := by
        rw [neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have h4 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
      rw [hcast, hsplit, h4]
      linarith
    linarith [hs1, hlast, hid2]
  obtain ⟨k, hk, hmem⟩ := hexists
  exact Set.mem_biUnion (Finset.mem_range.mpr hk) hmem

/-- The weight `s^e` is comparable to `(2^{-k})^e` on the block. -/
theorem rpow_le_on_brsBlock {e : ℝ} {k : ℕ} {s : ℝ} (hs : s ∈ brsBlock k) :
    s ^ e ≤ max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) * ((2 : ℝ) ^ (-(k : ℤ))) ^ e := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(k : ℤ)) := by positivity
  have hspos : 0 < s := brsBlock_pos hs
  set u : ℝ := s / (2 : ℝ) ^ (-(k : ℤ)) with hu
  have hu3 : 3 ≤ u := by
    rw [hu, le_div_iff₀ hpow]
    exact hs.1
  have hu6 : u ≤ 6 := by
    rw [hu, div_le_iff₀ hpow]
    exact hs.2
  have hupos : 0 < u := by linarith
  have hsu : s = u * (2 : ℝ) ^ (-(k : ℤ)) := by
    rw [hu]
    field_simp
  have hue : u ^ e ≤ max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) := by
    by_cases he : 0 ≤ e
    · refine le_trans (Real.rpow_le_rpow (by linarith) hu6 he) (le_max_right _ _)
    · push Not at he
      refine le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num) hu3 he.le)
        (le_max_left _ _)
  rw [hsu, Real.mul_rpow hupos.le hpow.le]
  exact mul_le_mul_of_nonneg_right hue (Real.rpow_nonneg hpow.le _)

/-- **The per-block Hölder bound.**  On the block `[3·2^{-k}, 6·2^{-k}]` the
weighted integral is controlled by the local `L^p` norm of `g`. -/
theorem lintegral_brsBlock_le {e p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℂ}
    (hg : Measurable g) (k : ℕ) :
    (∫⁻ s in brsBlock k, ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖) ≤
      ENNReal.ofReal (max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) *
          ((2 : ℝ) ^ (-(k : ℤ))) ^ e *
          (3 * (2 : ℝ) ^ (-(k : ℤ))) ^ (1 - 1 / p)) *
        (∫⁻ s in brsBlock k, (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(k : ℤ)) := by positivity
  set A : ℝ := max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) * ((2 : ℝ) ^ (-(k : ℤ))) ^ e with hA
  have hApos : 0 < A := by
    rw [hA]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) _
    have h6 : (0 : ℝ) < (6 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) _
    have hmax : 0 < max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) := lt_max_of_lt_left h3
    positivity
  -- replace the weight by its maximum on the block
  have hstep1 : (∫⁻ s in brsBlock k,
      ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖) ≤
      ENNReal.ofReal A * ∫⁻ s in brsBlock k, ENNReal.ofReal ‖g s‖ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (by
      rw [brsBlock]
      exact measurableSet_Icc) ?_
    intro s hs
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [hA]
    exact rpow_le_on_brsBlock hs
  -- Hölder against the constant function on the block
  have hstep2 : (∫⁻ s in brsBlock k, ENNReal.ofReal ‖g s‖) ≤
      (∫⁻ s in brsBlock k, (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p) *
        ENNReal.ofReal ((3 * (2 : ℝ) ^ (-(k : ℤ))) ^ (1 - 1 / p)) := by
    have hvol : (volume.restrict (brsBlock k)) univ =
        ENNReal.ofReal (3 * (2 : ℝ) ^ (-(k : ℤ))) := by
      rw [Measure.restrict_apply_univ, volume_brsBlock]
    have h := lintegral_le_rpow_mul_measure_univ
      (μ := volume.restrict (brsBlock k))
      (Φ := fun s => ENNReal.ofReal ‖g s‖) hg.norm.ennreal_ofReal hp
    rw [hvol] at h
    refine le_trans h ?_
    refine mul_le_mul' le_rfl (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by
      have h1p : 1 / p ≤ 1 := by
        rw [div_le_one hp0]
        exact hp
      linarith)]
  calc (∫⁻ s in brsBlock k, ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖)
      ≤ ENNReal.ofReal A * ∫⁻ s in brsBlock k, ENNReal.ofReal ‖g s‖ := hstep1
    _ ≤ ENNReal.ofReal A *
          ((∫⁻ s in brsBlock k, (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p) *
            ENNReal.ofReal ((3 * (2 : ℝ) ^ (-(k : ℤ))) ^ (1 - 1 / p))) :=
        mul_le_mul' le_rfl hstep2
    _ = ENNReal.ofReal (A * (3 * (2 : ℝ) ^ (-(k : ℤ))) ^ (1 - 1 / p)) *
          (∫⁻ s in brsBlock k, (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p) := by
        rw [ENNReal.ofReal_mul hApos.le]
        ring

/-- The local `L^p` norm of the profile on the dyadic block `k`. -/
def brsBlockNorm (p : ℝ) (g : ℝ → ℂ) (k : ℕ) : ENNReal :=
  (∫⁻ s in brsBlock k, (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p)

/-- The constant produced by the per-block Hölder bound. -/
def blockConst (e p : ℝ) (k : ℕ) : ℝ :=
  max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) * ((2 : ℝ) ^ (-(k : ℤ))) ^ e *
    (3 * (2 : ℝ) ^ (-(k : ℤ))) ^ (1 - 1 / p)

theorem blockConst_pos {e p : ℝ} (hp : 1 ≤ p) (k : ℕ) : 0 < blockConst e p k := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) _
  have hmax : 0 < max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) := lt_max_of_lt_left h3
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(k : ℤ)) := by positivity
  rw [blockConst]
  positivity

/-- The weight attached to the block `k` in the window on the shell `D_n`:
blocks beyond `n + 2` do not meet the window. -/
def brsWindowWeight (e p : ℝ) (n k : ℕ) : ENNReal :=
  if k < n + 3 then ENNReal.ofReal (blockConst e p k) else 0

/-- Blocks beyond `n + 2` lie strictly below the window on `D_n`. -/
theorem brsBlock_disjoint_window {n k : ℕ} (hk : n + 3 ≤ k) :
    brsBlock k ∩ Icc ((2 : ℝ) ^ (-(n : ℤ))) 6 = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun s hs => ?_
  obtain ⟨hsblock, hswindow⟩ := hs
  have hup : s ≤ 6 * (2 : ℝ) ^ (-(k : ℤ)) := hsblock.2
  have hlow : (2 : ℝ) ^ (-(n : ℤ)) ≤ s := hswindow.1
  have hkpow : (2 : ℝ) ^ (-(k : ℤ)) ≤ (2 : ℝ) ^ (-((n + 3 : ℕ) : ℤ)) := by
    refine zpow_le_zpow_right₀ (by norm_num) ?_
    omega
  have hid : 6 * (2 : ℝ) ^ (-((n + 3 : ℕ) : ℤ)) < (2 : ℝ) ^ (-(n : ℤ)) := by
    have hcast : ((n + 3 : ℕ) : ℤ) = (n : ℤ) + 3 := by push_cast; ring
    have hsplit : (2 : ℝ) ^ (-((n : ℤ) + 3)) =
        (2 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ (-3 : ℤ) := by
      rw [neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have h8 : (2 : ℝ) ^ (-3 : ℤ) = 1 / 8 := by norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℤ)) := by positivity
    rw [hcast, hsplit, h8]
    linarith
  have hchain : s ≤ 6 * (2 : ℝ) ^ (-((n + 3 : ℕ) : ℤ)) := by
    refine le_trans hup ?_
    nlinarith [hkpow]
  linarith

/-- **Window to blocks.**  The window integral on the shell `D_n` is dominated
by the weighted sum of the local `L^p` norms over the blocks meeting it. -/
theorem lintegral_window_le_tsum_blocks {e p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℂ}
    (hg : Measurable g) (n : ℕ) :
    (∫⁻ s in Icc ((2 : ℝ) ^ (-(n : ℤ))) 6,
        ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖) ≤
      ∑' k : ℕ, brsWindowWeight e p n k * brsBlockNorm p g k := by
  set F : ℝ → ENNReal := fun s => ENNReal.ofReal (s ^ e) * ENNReal.ofReal ‖g s‖
    with hF
  set A : ℕ → Set ℝ := fun k => if k < n + 3 then brsBlock k else ∅ with hA
  have hcover : Icc ((2 : ℝ) ^ (-(n : ℤ))) 6 ⊆ ⋃ k : ℕ, A k := by
    intro s hs
    obtain ⟨k, hk, hmem⟩ : ∃ k : ℕ, k < n + 3 ∧ s ∈ brsBlock k := by
      have hcov := window_subset_iUnion_brsBlock n hs
      simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hcov
      exact hcov
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    rw [hA]
    simp only [if_pos hk]
    exact hmem
  have hterm : ∀ k : ℕ, (∫⁻ s in A k, F s) ≤
      brsWindowWeight e p n k * brsBlockNorm p g k := by
    intro k
    by_cases hk : k < n + 3
    · have hAk : A k = brsBlock k := by
        rw [hA]
        simp only [if_pos hk]
      rw [hAk, brsWindowWeight, if_pos hk, brsBlockNorm, blockConst, hF]
      exact lintegral_brsBlock_le hp hg k
    · have hAk : A k = ∅ := by
        rw [hA]
        simp only [if_neg hk]
      rw [hAk]
      simp
  calc (∫⁻ s in Icc ((2 : ℝ) ^ (-(n : ℤ))) 6, F s)
      ≤ ∫⁻ s in ⋃ k : ℕ, A k, F s := lintegral_mono_set hcover
    _ ≤ ∑' k : ℕ, ∫⁻ s in A k, F s := lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, brsWindowWeight e p n k * brsBlockNorm p g k :=
        ENNReal.tsum_le_tsum hterm

/-- A truncated geometric sum with ratio greater than one. -/
theorem sum_geom_le {x : ℝ} (hx : 1 < x) (m : ℕ) :
    ∑ k ∈ Finset.range m, x ^ k ≤ x ^ m / (x - 1) := by
  have hx1 : x ≠ 1 := ne_of_gt hx
  have hxpos : (0 : ℝ) < x - 1 := by linarith
  rw [geom_sum_eq hx1]
  gcongr
  linarith

/-- The constant of the per-block Hölder bound, with the `k`-dependence
factored out. -/
def blockConstBase (e p : ℝ) : ℝ :=
  max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) * (3 : ℝ) ^ (1 - 1 / p)

theorem blockConstBase_pos (e p : ℝ) : 0 < blockConstBase e p := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) _
  have hmax : 0 < max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) := lt_max_of_lt_left h3
  have h31 : (0 : ℝ) < (3 : ℝ) ^ (1 - 1 / p) := Real.rpow_pos_of_pos (by norm_num) _
  rw [blockConstBase]
  positivity

/-- The block constant is a geometric sequence with ratio `2^{-a}`, where
`a = e + 1 - 1/p` is the exponent that the shell estimate produces. -/
theorem blockConst_eq {e p a : ℝ} (hae : e + 1 - 1 / p = a) (k : ℕ) :
    blockConst e p k = blockConstBase e p * ((2 : ℝ) ^ (-a)) ^ k := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(k : ℤ)) := by positivity
  have hsplit : (3 * (2 : ℝ) ^ (-(k : ℤ))) ^ (1 - 1 / p) =
      (3 : ℝ) ^ (1 - 1 / p) * ((2 : ℝ) ^ (-(k : ℤ))) ^ (1 - 1 / p) :=
    Real.mul_rpow (by norm_num) hpow.le
  have hcombine : ((2 : ℝ) ^ (-(k : ℤ))) ^ e * ((2 : ℝ) ^ (-(k : ℤ))) ^ (1 - 1 / p) =
      ((2 : ℝ) ^ (-(k : ℤ))) ^ a := by
    rw [← Real.rpow_add hpow]
    congr 1
    linarith [hae]
  have hzpow : ((2 : ℝ) ^ (-(k : ℤ))) ^ a = ((2 : ℝ) ^ (-a)) ^ k := by
    have h1 : (2 : ℝ) ^ (-(k : ℤ)) = (2 : ℝ) ^ (-(k : ℝ)) := by
      rw [← Real.rpow_intCast]
      push_cast
      ring_nf
    rw [h1, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-a)) k,
      ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [blockConst, blockConstBase, hsplit]
  calc max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) * ((2 : ℝ) ^ (-(k : ℤ))) ^ e *
        ((3 : ℝ) ^ (1 - 1 / p) * ((2 : ℝ) ^ (-(k : ℤ))) ^ (1 - 1 / p))
      = (max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) * (3 : ℝ) ^ (1 - 1 / p)) *
          (((2 : ℝ) ^ (-(k : ℤ))) ^ e * ((2 : ℝ) ^ (-(k : ℤ))) ^ (1 - 1 / p)) := by
        ring
    _ = (max ((3 : ℝ) ^ e) ((6 : ℝ) ^ e) * (3 : ℝ) ^ (1 - 1 / p)) *
          ((2 : ℝ) ^ (-a)) ^ k := by
        rw [hcombine, hzpow]

/-- **The total weight of the blocks meeting the window on `D_n`.**  Since
`a < 0` the geometric sum is dominated by its largest term. -/
theorem tsum_brsWindowWeight_le {e p a : ℝ} (hp : 1 ≤ p)
    (hae : e + 1 - 1 / p = a) (ha : a < 0) (n : ℕ) :
    (∑' k : ℕ, brsWindowWeight e p n k) ≤
      ENNReal.ofReal (blockConstBase e p *
        (((2 : ℝ) ^ (-a)) ^ (n + 3) / ((2 : ℝ) ^ (-a) - 1))) := by
  set x : ℝ := (2 : ℝ) ^ (-a) with hx
  have hx1 : 1 < x := by
    rw [hx]
    exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, by linarith⟩)
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  have hC0 : 0 < blockConstBase e p := blockConstBase_pos e p
  -- the sum is finite and equals a `Finset` sum
  have hvanish : ∀ k : ℕ, k ∉ Finset.range (n + 3) → brsWindowWeight e p n k = 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [brsWindowWeight, if_neg hk]
  have hsum : (∑' k : ℕ, brsWindowWeight e p n k) =
      ∑ k ∈ Finset.range (n + 3), brsWindowWeight e p n k :=
    tsum_eq_sum hvanish
  rw [hsum]
  have hterm : ∀ k ∈ Finset.range (n + 3), brsWindowWeight e p n k =
      ENNReal.ofReal (blockConstBase e p * x ^ k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [brsWindowWeight, if_pos hk, blockConst_eq hae k, hx]
  rw [Finset.sum_congr rfl hterm]
  have hreal : ∑ k ∈ Finset.range (n + 3), ENNReal.ofReal (blockConstBase e p * x ^ k) =
      ENNReal.ofReal (∑ k ∈ Finset.range (n + 3), blockConstBase e p * x ^ k) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro k _
    positivity
  rw [hreal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (sum_geom_le hx1 (n + 3)) hC0.le

/-- **Step 1 of Proposition 4.5.**  Composing the shell cutoff with the
window-to-blocks bound. -/
theorem brsMainMaximal_le_tsum_blocks {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℂ}
    (hg : Measurable g) {n : ℕ} {r : ℝ} (hrD : r ∈ brsD E n) :
    brsMainMaximal d E p g r ≤
      ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
        ∑' k : ℕ, brsWindowWeight (((d : ℝ) - 1) * (1 - 1 / p) - 1) p n k *
          brsBlockNorm p g k := by
  refine le_trans (brsMainMaximal_le_on_brsD hd hE g hrD) ?_
  exact mul_le_mul' le_rfl (lintegral_window_le_tsum_blocks hp hg n)

/-- **Step 2 of Proposition 4.5.**  The `q`-th power of the shell bound, after
weighted Hölder in the block index. -/
theorem brsMainMaximal_rpow_le_on_brsD {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p q a : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hae : (((d : ℝ) - 1) * (1 - 1 / p) - 1) + 1 - 1 / p = a) (ha : a < 0)
    {g : ℝ → ℂ} (hg : Measurable g) {n : ℕ} {r : ℝ} (hrD : r ∈ brsD E n) :
    brsMainMaximal d E p g r ^ q ≤
      ENNReal.ofReal (((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q) *
          (ENNReal.ofReal (blockConstBase (((d : ℝ) - 1) * (1 - 1 / p) - 1) p *
            (((2 : ℝ) ^ (-a)) ^ (n + 3) / ((2 : ℝ) ^ (-a) - 1)))) ^ (q - 1) *
        ∑' k : ℕ, brsWindowWeight (((d : ℝ) - 1) * (1 - 1 / p) - 1) p n k *
          brsBlockNorm p g k ^ q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set e : ℝ := ((d : ℝ) - 1) * (1 - 1 / p) - 1 with he
  set c : ℕ → ENNReal := brsWindowWeight e p n with hc
  set G : ℕ → ENNReal := brsBlockNorm p g with hG
  set A : ℝ := (2 / 3 : ℝ) ^ (1 - (d : ℝ)) with hA
  have hApos : 0 < A := by
    rw [hA]
    exact Real.rpow_pos_of_pos (by norm_num) _
  -- the weighted Hölder inequality in the block index
  have hholder : (∑' k, c k * G k) ≤
      (∑' k, c k * G k ^ q) ^ (1 / q) * (∑' k, c k) ^ (1 - 1 / q) :=
    tsum_weighted_le c G hq
  -- the total weight
  have hweight : (∑' k, c k) ≤
      ENNReal.ofReal (blockConstBase e p *
        (((2 : ℝ) ^ (-a)) ^ (n + 3) / ((2 : ℝ) ^ (-a) - 1))) := by
    rw [hc, he]
    exact tsum_brsWindowWeight_le hp hae ha n
  set B : ENNReal := ENNReal.ofReal (blockConstBase e p *
    (((2 : ℝ) ^ (-a)) ^ (n + 3) / ((2 : ℝ) ^ (-a) - 1))) with hB
  -- raise the shell bound to the `q`-th power
  have hstep := brsMainMaximal_le_tsum_blocks hd hE hp hg hrD
  rw [← he, ← hc, ← hG, ← hA] at hstep
  calc brsMainMaximal d E p g r ^ q
      ≤ (ENNReal.ofReal A * ∑' k, c k * G k) ^ q :=
        ENNReal.rpow_le_rpow hstep hq0.le
    _ = (ENNReal.ofReal A) ^ q * (∑' k, c k * G k) ^ q := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
    _ ≤ (ENNReal.ofReal A) ^ q *
          ((∑' k, c k * G k ^ q) ^ (1 / q) * (∑' k, c k) ^ (1 - 1 / q)) ^ q := by
        refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hholder hq0.le)
    _ = (ENNReal.ofReal A) ^ q * ((∑' k, c k * G k ^ q) * (∑' k, c k) ^ (q - 1)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
        congr 2
        field_simp
    _ ≤ (ENNReal.ofReal A) ^ q * ((∑' k, c k * G k ^ q) * B ^ (q - 1)) := by
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
        exact ENNReal.rpow_le_rpow hweight (by linarith)
    _ = ENNReal.ofReal (A ^ q) * B ^ (q - 1) * ∑' k, c k * G k ^ q := by
        rw [ENNReal.ofReal_rpow_of_nonneg hApos.le hq0.le]
        ring

/-- Every point of the first neighbourhood is at most `5`. -/
theorem le_five_of_mem_brsU_zero {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hEne : E.Nonempty) {r : ℝ} (hr : r ∈ brsU E 0) : r ≤ 5 := by
  have hdist : Metric.infDist r E ≤ 2 * (2 : ℝ) ^ (-(0 : ℕ) : ℤ) := hr
  have hdist' : Metric.infDist r E ≤ 2 := by
    simpa using hdist
  obtain ⟨t, htE, hrt⟩ := (Metric.infDist_lt_iff hEne).mp
    (lt_of_le_of_lt hdist' (by norm_num : (2 : ℝ) < 3))
  have ht2 : t ≤ 2 := (hE htE).2
  rw [Real.dist_eq, abs_lt] at hrt
  linarith [hrt.2]

/-- The radial weight is bounded on the neighbourhood of `E`. -/
theorem weight_le_of_mem_brsU_zero {d : ℕ} {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hEne : E.Nonempty) {r : ℝ} (hr : r ∈ brsU E 0) :
    ENNReal.ofReal r ^ (d - 1) ≤ ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) := by
  have hr5 : r ≤ 5 := le_five_of_mem_brsU_zero hE hEne hr
  by_cases hr0 : 0 ≤ r
  · rw [← ENNReal.ofReal_pow hr0]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr0 hr5 _)
  · push Not at hr0
    rw [ENNReal.ofReal_eq_zero.mpr hr0.le]
    by_cases hd1 : d - 1 = 0
    · rw [hd1, pow_zero, pow_zero]
      simp
    · rw [zero_pow hd1]
      simp

/-- **Step 3 of Proposition 4.5.**  Integrating the shell bound over `D_n`. -/
theorem lintegral_brsD_le {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p q a : ℝ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) (hae : (((d : ℝ) - 1) * (1 - 1 / p) - 1) + 1 - 1 / p = a)
    (ha : a < 0) {g : ℝ → ℂ} (hg : Measurable g) (n : ℕ) :
    (∫⁻ r in brsD E n,
        ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q) ≤
      ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
          (ENNReal.ofReal (((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q) *
            (ENNReal.ofReal (blockConstBase (((d : ℝ) - 1) * (1 - 1 / p) - 1) p *
              (((2 : ℝ) ^ (-a)) ^ (n + 3) / ((2 : ℝ) ^ (-a) - 1)))) ^ (q - 1) *
            ∑' k : ℕ, brsWindowWeight (((d : ℝ) - 1) * (1 - 1 / p) - 1) p n k *
              brsBlockNorm p g k ^ q) *
        volume (brsU E n) := by
  set e : ℝ := ((d : ℝ) - 1) * (1 - 1 / p) - 1 with he
  set B : ENNReal := ENNReal.ofReal (blockConstBase e p *
    (((2 : ℝ) ^ (-a)) ^ (n + 3) / ((2 : ℝ) ^ (-a) - 1))) with hB
  set T : ENNReal := ∑' k : ℕ, brsWindowWeight e p n k * brsBlockNorm p g k ^ q
    with hT
  set K : ENNReal := ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
    (ENNReal.ofReal (((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q) * B ^ (q - 1) * T) with hK
  have hpoint : ∀ r ∈ brsD E n,
      ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q ≤ K := by
    intro r hr
    have hrU0 : r ∈ brsU E 0 := brsU_subset_of_le E (Nat.zero_le n) hr.1
    have hweight := weight_le_of_mem_brsU_zero (d := d) hE hEne hrU0
    have hmax : brsMainMaximal d E p g r ^ q ≤
        ENNReal.ofReal (((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q) * B ^ (q - 1) * T := by
      rw [hB, hT, he]
      exact brsMainMaximal_rpow_le_on_brsD hd hE hp hq hae ha hg hr
    rw [hK]
    exact mul_le_mul' hweight hmax
  calc (∫⁻ r in brsD E n,
        ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q)
      ≤ ∫⁻ _r in brsD E n, K :=
        setLIntegral_mono' (measurableSet_brsD E n) hpoint
    _ = K * volume (brsD E n) := setLIntegral_const _ _
    _ ≤ K * volume (brsU E n) := by
        refine mul_le_mul' le_rfl (measure_mono ?_)
        exact fun r hr => hr.1
    _ = ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
          (ENNReal.ofReal (((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q) * B ^ (q - 1) * T) *
          volume (brsU E n) := by rw [hK]

/-- The main term vanishes off the first neighbourhood of `E`: an admissible
dilation `t` for the radius `r` is always within distance `2` of `r`. -/
theorem brsMainMaximal_eq_zero_of_notMem_brsU_zero {d : ℕ} {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p : ℝ} (g : ℝ → ℂ) {r : ℝ}
    (hr : r ∉ brsU E 0) : brsMainMaximal d E p g r = 0 := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) (by simp)
  exfalso
  obtain ⟨htE, htlow, hthigh⟩ := ht
  have htIcc : t ∈ Icc (1 : ℝ) 2 := hE htE
  have ht1 : (1 : ℝ) ≤ t := htIcc.1
  have ht2 : t ≤ 2 := htIcc.2
  have hclose : |r - t| < 2 := by
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · have hh : t < 3 * r / 2 := hthigh
      linarith
    · have hl : r / 2 < t := htlow
      linarith
  have hdist : Metric.infDist r E ≤ |r - t| := by
    have h : Metric.infDist r E ≤ dist r t :=
      Metric.infDist_le_dist_of_mem (x := r) htE
    rwa [Real.dist_eq] at h
  have hmem : r ∈ brsU E 0 := by
    show Metric.infDist r E ≤ 2 * (2 : ℝ) ^ (-(0 : ℕ) : ℤ)
    have hcalc : (2 : ℝ) * (2 : ℝ) ^ (-(0 : ℕ) : ℤ) = 2 := by norm_num
    rw [hcalc]
    linarith
  exact hr hmem

/-- **Step 4 of Proposition 4.5.**  The full radial integral is bounded by the
sum of the integrals over the shells; the leftover set lies in the closure of
`E`, which is null when `dim_M E < 1`. -/
theorem lintegral_le_tsum_brsD {d : ℕ} {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hEne : E.Nonempty) (hEnull : volume (closure E) = 0) {p q : ℝ} (hq : 0 < q)
    (g : ℝ → ℂ) :
    (∫⁻ r, ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q) ≤
      ∑' n : ℕ, ∫⁻ r in brsD E n,
        ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q := by
  set F : ℝ → ENNReal := fun r =>
    ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q with hF
  have hzero : ∀ r, r ∉ brsU E 0 → F r = 0 := by
    intro r hr
    rw [hF]
    simp only []
    rw [brsMainMaximal_eq_zero_of_notMem_brsU_zero hE g hr,
      ENNReal.zero_rpow_of_pos hq, mul_zero]
  have hcover : brsU E 0 ⊆ (⋃ n : ℕ, brsD E n) ∪ closure E := by
    intro r hr
    by_cases hmem : r ∈ ⋃ n : ℕ, brsD E n
    · exact Or.inl hmem
    · refine Or.inr ?_
      have hd0 := infDist_eq_zero_of_notMem_iUnion_brsD hr hmem
      rwa [← Metric.mem_closure_iff_infDist_zero hEne] at hd0
  calc (∫⁻ r, F r) = ∫⁻ r in brsU E 0, F r := by
        rw [← lintegral_indicator (measurableSet_brsU E 0)]
        refine lintegral_congr fun r => ?_
        by_cases hr : r ∈ brsU E 0
        · rw [Set.indicator_of_mem hr]
        · rw [Set.indicator_of_notMem hr, hzero r hr]
    _ ≤ ∫⁻ r in (⋃ n : ℕ, brsD E n) ∪ closure E, F r := lintegral_mono_set hcover
    _ ≤ (∫⁻ r in ⋃ n : ℕ, brsD E n, F r) + ∫⁻ r in closure E, F r :=
        lintegral_union_le _ _ _
    _ = ∫⁻ r in ⋃ n : ℕ, brsD E n, F r := by
        rw [setLIntegral_measure_zero _ _ hEnull, add_zero]
    _ ≤ ∑' n : ℕ, ∫⁻ r in brsD E n, F r := lintegral_iUnion_le _ _

/-- The half-open version of a dyadic block; these tile `(0, 6]`. -/
def brsBlockIoc (k : ℕ) : Set ℝ :=
  Ioc (3 * (2 : ℝ) ^ (-(k : ℤ))) (6 * (2 : ℝ) ^ (-(k : ℤ)))

theorem measurableSet_brsBlockIoc (k : ℕ) : MeasurableSet (brsBlockIoc k) := by
  rw [brsBlockIoc]
  exact measurableSet_Ioc

theorem brsBlockIoc_disjoint : Pairwise (Function.onFun Disjoint brsBlockIoc) := by
  intro m n hmn
  have hkey : ∀ i j : ℕ, i < j → Disjoint (brsBlockIoc i) (brsBlockIoc j) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun s hsi hsj => ?_
    have hlow : 3 * (2 : ℝ) ^ (-(i : ℤ)) < s := hsi.1
    have hup : s ≤ 6 * (2 : ℝ) ^ (-(j : ℤ)) := hsj.2
    have hstep : (2 : ℝ) ^ (-(j : ℤ)) ≤ (2 : ℝ) ^ (-((i : ℤ) + 1)) := by
      refine zpow_le_zpow_right₀ (by norm_num) ?_
      omega
    have hid : 6 * (2 : ℝ) ^ (-((i : ℤ) + 1)) = 3 * (2 : ℝ) ^ (-(i : ℤ)) := by
      rw [neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
      ring
    have hchain : s ≤ 3 * (2 : ℝ) ^ (-(i : ℤ)) := by
      refine le_trans hup ?_
      rw [← hid]
      nlinarith [hstep]
    linarith
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hkey m n h
  · exact (hkey n m h).symm

theorem brsBlockIoc_subset_Ioi (k : ℕ) : brsBlockIoc k ⊆ Ioi (0 : ℝ) := by
  intro s hs
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(k : ℤ)) := by positivity
  have h := hs.1
  simp only [mem_Ioi]
  nlinarith [hpow]

/-- **The blocks recover the global `L^p` norm.**  The blocks overlap only in
endpoints, so the sum of the local `p`-th powers is at most the global one. -/
theorem tsum_brsBlockNorm_rpow_le {p : ℝ} (hp : 0 < p) (g : ℝ → ℂ) :
    (∑' k : ℕ, brsBlockNorm p g k ^ p) ≤
      ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ p := by
  have hterm : ∀ k : ℕ, brsBlockNorm p g k ^ p =
      ∫⁻ s in brsBlockIoc k, (ENNReal.ofReal ‖g s‖) ^ p := by
    intro k
    rw [brsBlockNorm, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne',
      ENNReal.rpow_one, brsBlock, brsBlockIoc]
    exact (setLIntegral_congr Ioc_ae_eq_Icc).symm
  rw [tsum_congr hterm,
    ← lintegral_iUnion (s := brsBlockIoc) measurableSet_brsBlockIoc
      brsBlockIoc_disjoint]
  refine lintegral_mono_set ?_
  exact Set.iUnion_subset brsBlockIoc_subset_Ioi

/-- Reindexing the tail `{n : m ≤ n}` of `ℕ`. -/
def tailEquiv (m : ℕ) : ({n : ℕ | m ≤ n} : Set ℕ) ≃ ℕ where
  toFun n := n.1 - m
  invFun j := ⟨j + m, by simp only [Set.mem_setOf_eq]; omega⟩
  left_inv := fun n => by
    obtain ⟨n, hn⟩ := n
    simp only [Set.mem_setOf_eq] at hn
    simp only [Subtype.mk.injEq]
    omega
  right_inv := fun j => by simp

/-- **The geometric tail sum.** -/
theorem tsum_geometric_tail (y : ENNReal) (m : ℕ) :
    (∑' n : ℕ, (if m ≤ n then y ^ n else 0)) = y ^ m * (1 - y)⁻¹ := by
  have hind : ∀ n : ℕ, (if m ≤ n then y ^ n else 0) =
      {n : ℕ | m ≤ n}.indicator (fun n => y ^ n) n := by
    intro n
    by_cases h : m ≤ n <;> simp [Set.indicator_apply, h]
  have hterm : ∀ j : ℕ, y ^ (j + m) = y ^ m * y ^ j := by
    intro j
    rw [pow_add]
    ring
  rw [tsum_congr hind, ← tsum_subtype]
  calc (∑' x : ({n : ℕ | m ≤ n} : Set ℕ), y ^ (x : ℕ))
      = ∑' x : ({n : ℕ | m ≤ n} : Set ℕ), y ^ ((tailEquiv m x) + m) := by
        refine tsum_congr fun x => ?_
        congr 1
        have hx : m ≤ (x : ℕ) := x.2
        simp only [tailEquiv, Equiv.coe_fn_mk]
        omega
    _ = ∑' j : ℕ, y ^ (j + m) :=
        (tailEquiv m).tsum_eq (fun j : ℕ => y ^ (j + m))
    _ = y ^ m * (1 - y)⁻¹ := by
        rw [tsum_congr hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- The shell weights, summed against the geometric factor `x^{-n}`, are
uniformly bounded in the block index. -/
theorem tsum_shell_weight_le {x : ℝ} (hx : 1 < x) (k : ℕ) :
    (∑' n : ℕ, (if k < n + 3 then (ENNReal.ofReal x⁻¹) ^ n else 0)) ≤
      ENNReal.ofReal (x ^ (2 : ℕ)) * (ENNReal.ofReal x⁻¹) ^ k *
        (1 - ENNReal.ofReal x⁻¹)⁻¹ := by
  set y : ENNReal := ENNReal.ofReal x⁻¹ with hy
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hcond : ∀ n : ℕ, (if k < n + 3 then y ^ n else 0) =
      (if k - 2 ≤ n then y ^ n else 0) := by
    intro n
    by_cases h : k < n + 3
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  rw [tsum_congr hcond, tsum_geometric_tail]
  refine mul_le_mul' ?_ le_rfl
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk0 : k - 2 = 0 := by omega
    rw [hk0, pow_zero]
    have hcalc : ENNReal.ofReal (x ^ (2 : ℕ)) * y ^ k =
        ENNReal.ofReal (x ^ (2 : ℕ) * (x⁻¹) ^ k) := by
      rw [hy, ← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
    rw [hcalc, ENNReal.one_le_ofReal, inv_pow, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity : (0 : ℝ) < x ^ k), one_mul]
    exact pow_le_pow_right₀ hx.le (by omega)
  · have hsplit : y ^ k = y ^ (k - 2) * y ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    have hyx : ENNReal.ofReal (x ^ (2 : ℕ)) * y ^ 2 = 1 := by
      rw [hy, ← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      rw [show x ^ (2 : ℕ) * (x⁻¹) ^ (2 : ℕ) = 1 by field_simp]
      exact ENNReal.ofReal_one
    rw [hsplit]
    calc y ^ (k - 2) = y ^ (k - 2) * 1 := (mul_one _).symm
      _ = y ^ (k - 2) * (ENNReal.ofReal (x ^ (2 : ℕ)) * y ^ 2) := by rw [hyx]
      _ = ENNReal.ofReal (x ^ (2 : ℕ)) * (y ^ (k - 2) * y ^ 2) := by ring
      _ ≤ _ := le_rfl

theorem one_lt_two_rpow_neg {a : ℝ} (ha : a < 0) : 1 < (2 : ℝ) ^ (-a) := by
  refine Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, ?_⟩)
  linarith

/-- The weight of a single block, summed over the shells that see it, is
bounded uniformly in the block index. -/
theorem tsum_shell_single_block_le {e p a : ℝ} (hae : e + 1 - 1 / p = a)
    (ha : a < 0) (k : ℕ) :
    (∑' n : ℕ, (ENNReal.ofReal ((2 : ℝ) ^ (-a))⁻¹) ^ n * brsWindowWeight e p n k) ≤
      ENNReal.ofReal (blockConstBase e p * ((2 : ℝ) ^ (-a)) ^ (2 : ℕ)) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (-a))⁻¹)⁻¹ := by
  set x : ℝ := (2 : ℝ) ^ (-a) with hxdef
  have hx : 1 < x := by
    rw [hxdef]
    exact one_lt_two_rpow_neg ha
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hC0 : 0 < blockConstBase e p := blockConstBase_pos e p
  have hterm : ∀ n : ℕ, (ENNReal.ofReal x⁻¹) ^ n * brsWindowWeight e p n k =
      ENNReal.ofReal (blockConstBase e p * x ^ k) *
        (if k < n + 3 then (ENNReal.ofReal x⁻¹) ^ n else 0) := by
    intro n
    by_cases hn : k < n + 3
    · rw [brsWindowWeight, if_pos hn, if_pos hn, blockConst_eq hae, hxdef, mul_comm]
    · rw [brsWindowWeight, if_neg hn, if_neg hn, mul_zero, mul_zero]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  refine le_trans (mul_le_mul' le_rfl (tsum_shell_weight_le hx k)) ?_
  have hpow : (ENNReal.ofReal x⁻¹) ^ k = ENNReal.ofReal ((x⁻¹) ^ k) :=
    (ENNReal.ofReal_pow (by positivity) k).symm
  have hprod : ENNReal.ofReal (blockConstBase e p * x ^ k) *
      (ENNReal.ofReal (x ^ (2 : ℕ)) * ENNReal.ofReal ((x⁻¹) ^ k)) =
      ENNReal.ofReal (blockConstBase e p * x ^ (2 : ℕ)) := by
    rw [← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (mul_nonneg hC0.le (by positivity))]
    congr 1
    rw [show blockConstBase e p * x ^ k * (x ^ (2 : ℕ) * (x⁻¹) ^ k) =
        blockConstBase e p * x ^ (2 : ℕ) * (x ^ k * (x⁻¹) ^ k) by ring,
      show x ^ k * (x⁻¹) ^ k = 1 by
        rw [← mul_pow, mul_inv_cancel₀ hxpos.ne', one_pow],
      mul_one]
  have hcollect : ENNReal.ofReal (blockConstBase e p * x ^ k) *
      (ENNReal.ofReal (x ^ (2 : ℕ)) * (ENNReal.ofReal x⁻¹) ^ k *
        (1 - ENNReal.ofReal x⁻¹)⁻¹) =
      ENNReal.ofReal (blockConstBase e p * x ^ (2 : ℕ)) *
        (1 - ENNReal.ofReal x⁻¹)⁻¹ := by
    calc ENNReal.ofReal (blockConstBase e p * x ^ k) *
          (ENNReal.ofReal (x ^ (2 : ℕ)) * (ENNReal.ofReal x⁻¹) ^ k *
            (1 - ENNReal.ofReal x⁻¹)⁻¹)
        = (ENNReal.ofReal (blockConstBase e p * x ^ k) *
            (ENNReal.ofReal (x ^ (2 : ℕ)) * ENNReal.ofReal ((x⁻¹) ^ k))) *
            (1 - ENNReal.ofReal x⁻¹)⁻¹ := by
          rw [hpow]
          ring
      _ = ENNReal.ofReal (blockConstBase e p * x ^ (2 : ℕ)) *
            (1 - ENNReal.ofReal x⁻¹)⁻¹ := by rw [hprod]
  calc ENNReal.ofReal (blockConstBase e p * x ^ k) *
        (ENNReal.ofReal (x ^ (2 : ℕ)) * (ENNReal.ofReal x⁻¹) ^ k *
          (1 - ENNReal.ofReal x⁻¹)⁻¹)
      = ENNReal.ofReal (blockConstBase e p * x ^ (2 : ℕ)) *
          (1 - ENNReal.ofReal x⁻¹)⁻¹ := hcollect
    _ ≤ _ := le_rfl

/-- **The double sum over shells and blocks.** -/
theorem tsum_shell_block_le {e p a q : ℝ} (hae : e + 1 - 1 / p = a) (ha : a < 0)
    (g : ℝ → ℂ) :
    (∑' n : ℕ, (ENNReal.ofReal ((2 : ℝ) ^ (-a))⁻¹) ^ n *
        ∑' k : ℕ, brsWindowWeight e p n k * brsBlockNorm p g k ^ q) ≤
      ENNReal.ofReal (blockConstBase e p * ((2 : ℝ) ^ (-a)) ^ (2 : ℕ)) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (-a))⁻¹)⁻¹ *
        ∑' k : ℕ, brsBlockNorm p g k ^ q := by
  set y : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (-a))⁻¹ with hy
  set M : ENNReal := ENNReal.ofReal (blockConstBase e p * ((2 : ℝ) ^ (-a)) ^ (2 : ℕ)) *
    (1 - ENNReal.ofReal ((2 : ℝ) ^ (-a))⁻¹)⁻¹ with hM
  calc (∑' n : ℕ, y ^ n * ∑' k : ℕ, brsWindowWeight e p n k * brsBlockNorm p g k ^ q)
      = ∑' n : ℕ, ∑' k : ℕ,
          y ^ n * (brsWindowWeight e p n k * brsBlockNorm p g k ^ q) := by
        refine tsum_congr fun n => ?_
        rw [ENNReal.tsum_mul_left]
    _ = ∑' k : ℕ, ∑' n : ℕ,
          y ^ n * (brsWindowWeight e p n k * brsBlockNorm p g k ^ q) :=
        ENNReal.tsum_comm
    _ = ∑' k : ℕ, (∑' n : ℕ, y ^ n * brsWindowWeight e p n k) *
          brsBlockNorm p g k ^ q := by
        refine tsum_congr fun k => ?_
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun n => ?_
        ring
    _ ≤ ∑' k : ℕ, M * brsBlockNorm p g k ^ q := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        refine mul_le_mul' ?_ le_rfl
        rw [hM, hy]
        exact tsum_shell_single_block_le hae ha k
    _ = M * ∑' k : ℕ, brsBlockNorm p g k ^ q := ENNReal.tsum_mul_left

theorem two_zpow_eq_rpow (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [← Real.rpow_intCast]
  push_cast
  ring_nf

theorem two_rpow_pow (c : ℝ) (m : ℕ) : ((2 : ℝ) ^ c) ^ m = (2 : ℝ) ^ (c * m) := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ c) m, ← Real.rpow_mul (by norm_num)]

theorem two_rpow_rpow (c t : ℝ) : ((2 : ℝ) ^ c) ^ t = (2 : ℝ) ^ (c * t) :=
  (Real.rpow_mul (by norm_num) c t).symm

theorem two_rpow_inv_pow (c : ℝ) (n : ℕ) :
    (((2 : ℝ) ^ c)⁻¹) ^ n = (2 : ℝ) ^ (-c * n) := by
  rw [← Real.rpow_neg_one ((2 : ℝ) ^ c), two_rpow_rpow, two_rpow_pow]
  congr 1
  ring

/-- **The shell factor collapses.**  The `n`-dependence of the shell constant,
the radial volume and the covering bound cancel down to `x^{-n}`. -/
theorem shell_factor_identity {a q : ℝ} (n : ℕ) :
    (((2 : ℝ) ^ (-a)) ^ (n + 3)) ^ (q - 1) *
        ((2 : ℝ) ^ (-(n : ℤ)) * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1))) =
      ((2 : ℝ) ^ (-a)) ^ (3 * (q - 1)) * (((2 : ℝ) ^ (-a))⁻¹) ^ n := by
  rw [two_rpow_pow (-a) (n + 3), two_rpow_rpow, two_zpow_eq_rpow, two_rpow_rpow,
    two_rpow_rpow, two_rpow_inv_pow]
  simp only [← Real.rpow_add (show (0 : ℝ) < 2 by norm_num)]
  congr 1
  push_cast
  ring

/-! ## The per-shell estimate -/

section PerShell

open Auto.FractalDimensions

/-- The constant of the per-shell estimate in BRS Proposition 4.5. -/
def shellConst (d : ℕ) (p q a S : ℝ) : ℝ :=
  (5 : ℝ) ^ (d - 1) * ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q *
    (blockConstBase (((d : ℝ) - 1) * (1 - 1 / p) - 1) p /
      ((2 : ℝ) ^ (-a) - 1)) ^ (q - 1) * 7 * S ^ q *
    ((2 : ℝ) ^ (-a)) ^ (3 * (q - 1))

theorem shellConst_pos {d : ℕ} {p q a S : ℝ} (ha : a < 0) (hS : 0 < S) :
    0 < shellConst d p q a S := by
  have hx : 1 < (2 : ℝ) ^ (-a) := one_lt_two_rpow_neg ha
  have hC0 : 0 < blockConstBase (((d : ℝ) - 1) * (1 - 1 / p) - 1) p :=
    blockConstBase_pos _ _
  have h1 : (0 : ℝ) < ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _
  have h2 : (0 : ℝ) < (blockConstBase (((d : ℝ) - 1) * (1 - 1 / p) - 1) p /
      ((2 : ℝ) ^ (-a) - 1)) ^ (q - 1) := by
    refine Real.rpow_pos_of_pos (div_pos hC0 ?_) _
    linarith
  have h3 : (0 : ℝ) < S ^ q := Real.rpow_pos_of_pos hS _
  have h4 : (0 : ℝ) < ((2 : ℝ) ^ (-a)) ^ (3 * (q - 1)) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _
  rw [shellConst]
  positivity

/-- **The per-shell estimate of BRS Proposition 4.5.** -/
theorem lintegral_brsD_le_shell {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p q a S : ℝ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) (hae : (((d : ℝ) - 1) * (1 - 1 / p) - 1) + 1 - 1 / p = a)
    (ha : a < 0) (hS : 0 < S)
    (hcov : ∀ n : ℕ, ((intervalCoveringNumber E ((2 : ℝ) ^ (-(n : ℤ))) : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (S ^ q * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1))))
    {g : ℝ → ℂ} (hg : Measurable g) (n : ℕ) :
    (∫⁻ r in brsD E n,
        ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q) ≤
      ENNReal.ofReal (shellConst d p q a S) *
          (ENNReal.ofReal ((2 : ℝ) ^ (-a))⁻¹) ^ n *
        ∑' k : ℕ, brsWindowWeight (((d : ℝ) - 1) * (1 - 1 / p) - 1) p n k *
          brsBlockNorm p g k ^ q := by
  set e : ℝ := ((d : ℝ) - 1) * (1 - 1 / p) - 1 with he
  set x : ℝ := (2 : ℝ) ^ (-a) with hxdef
  have hx : 1 < x := by
    rw [hxdef]
    exact one_lt_two_rpow_neg ha
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hC0 : 0 < blockConstBase e p := blockConstBase_pos e p
  have hA : (0 : ℝ) < (2 / 3 : ℝ) ^ (1 - (d : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  set T : ENNReal := ∑' k : ℕ, brsWindowWeight e p n k * brsBlockNorm p g k ^ q
    with hT
  -- the volume of the shell neighbourhood
  have hvol : volume (brsU E n) ≤
      ENNReal.ofReal (7 * (2 : ℝ) ^ (-(n : ℤ)) *
        (S ^ q * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1)))) := by
    refine le_trans (volume_brsU_le hE hEne n) ?_
    calc ENNReal.ofReal (7 * (2 : ℝ) ^ (-(n : ℤ))) *
          ((intervalCoveringNumber E ((2 : ℝ) ^ (-(n : ℤ))) : ℕ) : ℝ≥0∞)
        ≤ ENNReal.ofReal (7 * (2 : ℝ) ^ (-(n : ℤ))) *
            ENNReal.ofReal (S ^ q * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1))) :=
          mul_le_mul' le_rfl (hcov n)
      _ = ENNReal.ofReal (7 * (2 : ℝ) ^ (-(n : ℤ)) *
            (S ^ q * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  -- the shell constant, with its `n`-dependence
  have hB : (ENNReal.ofReal (blockConstBase e p * (x ^ (n + 3) / (x - 1)))) ^ (q - 1) =
      ENNReal.ofReal ((blockConstBase e p / (x - 1)) ^ (q - 1) *
        (x ^ (n + 3)) ^ (q - 1)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith)]
    congr 1
    rw [show blockConstBase e p * (x ^ (n + 3) / (x - 1)) =
        (blockConstBase e p / (x - 1)) * x ^ (n + 3) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
  -- assemble
  have hstep := lintegral_brsD_le hd hE hEne hp hq hae ha hg n
  rw [← he, ← hT] at hstep
  refine le_trans hstep ?_
  rw [← hxdef, hB]
  refine le_trans (mul_le_mul' le_rfl hvol) (le_of_eq ?_)
  set A1 : ℝ := (5 : ℝ) ^ (d - 1) with hA1
  set A2 : ℝ := ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q with hA2
  set A3 : ℝ := (blockConstBase e p / (x - 1)) ^ (q - 1) * (x ^ (n + 3)) ^ (q - 1)
    with hA3
  set A4 : ℝ := 7 * (2 : ℝ) ^ (-(n : ℤ)) *
    (S ^ q * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1))) with hA4
  have h1 : 0 ≤ A1 := by rw [hA1]; positivity
  have h2 : 0 ≤ A2 := by
    rw [hA2]
    exact (Real.rpow_pos_of_pos hA _).le
  have h3 : 0 ≤ A3 := by
    rw [hA3]
    have hb1 : (0 : ℝ) < (blockConstBase e p / (x - 1)) ^ (q - 1) :=
      Real.rpow_pos_of_pos (div_pos hC0 (by linarith)) _
    have hb2 : (0 : ℝ) < (x ^ (n + 3)) ^ (q - 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  have h4 : 0 ≤ A4 := by
    rw [hA4]
    have hb1 : (0 : ℝ) < S ^ q := Real.rpow_pos_of_pos hS _
    have hb2 : (0 : ℝ) < ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1)) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hfactor := shell_factor_identity (a := a) (q := q) n
  rw [← hxdef] at hfactor
  have hconst : A1 * A2 * A3 * A4 = shellConst d p q a S * (x⁻¹) ^ n := by
    rw [hA1, hA2, hA3, hA4, shellConst, ← he, ← hxdef]
    calc (5 : ℝ) ^ (d - 1) * ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q *
          ((blockConstBase e p / (x - 1)) ^ (q - 1) * (x ^ (n + 3)) ^ (q - 1)) *
          (7 * (2 : ℝ) ^ (-(n : ℤ)) *
            (S ^ q * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1))))
        = ((5 : ℝ) ^ (d - 1) * ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q *
            (blockConstBase e p / (x - 1)) ^ (q - 1) * 7 * S ^ q) *
            ((x ^ (n + 3)) ^ (q - 1) *
              ((2 : ℝ) ^ (-(n : ℤ)) *
                ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1)))) := by ring
      _ = ((5 : ℝ) ^ (d - 1) * ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q *
            (blockConstBase e p / (x - 1)) ^ (q - 1) * 7 * S ^ q) *
            (x ^ (3 * (q - 1)) * (x⁻¹) ^ n) := by rw [hfactor]
      _ = (5 : ℝ) ^ (d - 1) * ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q *
            (blockConstBase e p / (x - 1)) ^ (q - 1) * 7 * S ^ q *
            x ^ (3 * (q - 1)) * (x⁻¹) ^ n := by ring
  calc ENNReal.ofReal A1 * (ENNReal.ofReal A2 * ENNReal.ofReal A3 * T) *
        ENNReal.ofReal A4
      = (ENNReal.ofReal A1 * ENNReal.ofReal A2 * ENNReal.ofReal A3 *
          ENNReal.ofReal A4) * T := by ring
    _ = ENNReal.ofReal (A1 * A2 * A3 * A4) * T := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h1 h2) h3),
          ENNReal.ofReal_mul (mul_nonneg h1 h2), ENNReal.ofReal_mul h1]
    _ = ENNReal.ofReal (shellConst d p q a S * (x⁻¹) ^ n) * T := by rw [hconst]
    _ = ENNReal.ofReal (shellConst d p q a S) * (ENNReal.ofReal x⁻¹) ^ n * T := by
        rw [ENNReal.ofReal_mul (shellConst_pos (d := d) (p := p) (q := q) ha hS).le,
          ENNReal.ofReal_pow (by positivity)]

end PerShell

/-! ## Proposition 4.5 -/

section Prop45

open Auto.FractalDimensions

/-- The block-sum constant `M` of Proposition 4.5, as a real number. -/
theorem blockSumConst_eq {e p a : ℝ} (ha : a < 0) :
    ENNReal.ofReal (blockConstBase e p * ((2 : ℝ) ^ (-a)) ^ (2 : ℕ)) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (-a))⁻¹)⁻¹ =
      ENNReal.ofReal (blockConstBase e p * ((2 : ℝ) ^ (-a)) ^ (2 : ℕ) *
        (1 - ((2 : ℝ) ^ (-a))⁻¹)⁻¹) := by
  have hx : 1 < (2 : ℝ) ^ (-a) := one_lt_two_rpow_neg ha
  have hxpos : (0 : ℝ) < (2 : ℝ) ^ (-a) := lt_trans zero_lt_one hx
  have hinv : ((2 : ℝ) ^ (-a))⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hx
  have hsub : (0 : ℝ) < 1 - ((2 : ℝ) ^ (-a))⁻¹ := by linarith
  have hone : (1 : ENNReal) - ENNReal.ofReal ((2 : ℝ) ^ (-a))⁻¹ =
      ENNReal.ofReal (1 - ((2 : ℝ) ^ (-a))⁻¹) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  rw [hone, ← ENNReal.ofReal_inv_of_pos hsub, ← ENNReal.ofReal_mul (by
    have hC0 : 0 < blockConstBase e p := blockConstBase_pos e p
    positivity)]

/-- **BRS Proposition 4.5.**  For `1 ≤ p < p_d`, `p ≤ q < ∞` and a dilation set
whose dyadic covering numbers obey `N(E, 2^{-n}) ≤ S^q (2^{-n})^{-(qa+1)}`
with `a = d - 1 - d/p < 0`, the main term `𝔐_p` maps `L^p(ds)` into
`L^q(r^{d-1} dr)`. -/
theorem prop45_brsMainMaximal {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    (hEnull : volume (closure E) = 0) {p q a S : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : p ≤ q) (hae : (((d : ℝ) - 1) * (1 - 1 / p) - 1) + 1 - 1 / p = a)
    (ha : a < 0) (hS : 0 < S)
    (hcov : ∀ n : ℕ, ((intervalCoveringNumber E ((2 : ℝ) ^ (-(n : ℤ))) : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (S ^ q * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℂ, Measurable g →
      (∫⁻ r, ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C *
          (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set e : ℝ := ((d : ℝ) - 1) * (1 - 1 / p) - 1 with he
  set x : ℝ := (2 : ℝ) ^ (-a) with hxdef
  have hx : 1 < x := by
    rw [hxdef]
    exact one_lt_two_rpow_neg ha
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hinv : x⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hx
  have hC0 : 0 < blockConstBase e p := blockConstBase_pos e p
  set Mreal : ℝ := blockConstBase e p * x ^ (2 : ℕ) * (1 - x⁻¹)⁻¹ with hMreal
  have hMpos : 0 < Mreal := by
    rw [hMreal]
    have hsub : (0 : ℝ) < 1 - x⁻¹ := by linarith
    positivity
  have hSC : 0 < shellConst d p q a S := shellConst_pos (d := d) (p := p) (q := q) ha hS
  refine ⟨(shellConst d p q a S * Mreal) ^ (1 / q), by positivity, ?_⟩
  intro g hg
  set G : ENNReal := (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p) with hG
  -- the shells
  have hshell : ∀ n : ℕ, (∫⁻ r in brsD E n,
      ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q) ≤
        ENNReal.ofReal (shellConst d p q a S) * (ENNReal.ofReal x⁻¹) ^ n *
          ∑' k : ℕ, brsWindowWeight e p n k * brsBlockNorm p g k ^ q := by
    intro n
    rw [he, hxdef]
    exact lintegral_brsD_le_shell hd hE hEne hp hq hae ha hS hcov hg n
  -- the block sums
  have hblocks : (∑' k : ℕ, brsBlockNorm p g k ^ q) ≤ G ^ q := by
    have h1 : (∑' k : ℕ, brsBlockNorm p g k ^ q) ^ (1 / q) ≤
        (∑' k : ℕ, brsBlockNorm p g k ^ p) ^ (1 / p) :=
      tsum_rpow_le_tsum_rpow _ hp0 hpq
    have h2 : (∑' k : ℕ, brsBlockNorm p g k ^ p) ^ (1 / p) ≤ G := by
      rw [hG]
      exact ENNReal.rpow_le_rpow (tsum_brsBlockNorm_rpow_le hp0 g) (by positivity)
    have h3 : (∑' k : ℕ, brsBlockNorm p g k ^ q) ^ (1 / q) ≤ G := le_trans h1 h2
    have h4 := ENNReal.rpow_le_rpow h3 hq0.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one] at h4
  -- chain everything
  have hmain : (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
      brsMainMaximal d E p g r ^ q) ≤
        ENNReal.ofReal (shellConst d p q a S * Mreal) * G ^ q := by
    calc (∫⁻ r, ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q)
        ≤ ∑' n : ℕ, ∫⁻ r in brsD E n,
            ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q :=
          lintegral_le_tsum_brsD hE hEne hEnull hq0 g
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (shellConst d p q a S) *
            (ENNReal.ofReal x⁻¹) ^ n *
            ∑' k : ℕ, brsWindowWeight e p n k * brsBlockNorm p g k ^ q :=
          ENNReal.tsum_le_tsum hshell
      _ = ENNReal.ofReal (shellConst d p q a S) *
            ∑' n : ℕ, (ENNReal.ofReal x⁻¹) ^ n *
              ∑' k : ℕ, brsWindowWeight e p n k * brsBlockNorm p g k ^ q := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun n => ?_
          ring
      _ ≤ ENNReal.ofReal (shellConst d p q a S) *
            (ENNReal.ofReal (blockConstBase e p * x ^ (2 : ℕ)) *
              (1 - ENNReal.ofReal x⁻¹)⁻¹ *
              ∑' k : ℕ, brsBlockNorm p g k ^ q) := by
          refine mul_le_mul' le_rfl ?_
          rw [hxdef]
          exact tsum_shell_block_le hae ha g
      _ = ENNReal.ofReal (shellConst d p q a S) * ENNReal.ofReal Mreal *
            ∑' k : ℕ, brsBlockNorm p g k ^ q := by
          rw [hMreal, hxdef, ← blockSumConst_eq (e := e) (p := p) ha]
          ring
      _ ≤ ENNReal.ofReal (shellConst d p q a S) * ENNReal.ofReal Mreal * G ^ q :=
          mul_le_mul' le_rfl hblocks
      _ = ENNReal.ofReal (shellConst d p q a S * Mreal) * G ^ q := by
          rw [ENNReal.ofReal_mul hSC.le]
  calc (∫⁻ r, ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q) ^ (1 / q)
      ≤ (ENNReal.ofReal (shellConst d p q a S * Mreal) * G ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = ENNReal.ofReal ((shellConst d p q a S * Mreal) ^ (1 / q)) * G := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / q),
          ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]

end Prop45

/-! ## Logarithmic shells and blocks -/

section LogShells

open Auto.FractalDimensions

/-! ## The logarithmic shells and blocks of BRS Proposition 4.6

At the endpoint `p = p_d` the geometric gain of Proposition 4.5 disappears and
is replaced by a logarithm.  The shells are grouped dyadically in `n`, and the
profile variable is decomposed into doubly exponential blocks. -/

/-- The grouped shell `Ω_ℓ = ⋃_{2^{ℓ-1} ≤ n < 2^ℓ} D_n` of BRS §4. -/
def brsOmega (E : Set ℝ) (l : ℕ) : Set ℝ :=
  ⋃ n ∈ Finset.Ico (2 ^ (l - 1)) (2 ^ l), brsD E n

theorem measurableSet_brsOmega (E : Set ℝ) (l : ℕ) :
    MeasurableSet (brsOmega E l) := by
  rw [brsOmega]
  exact Finset.measurableSet_biUnion _ fun n _ => measurableSet_brsD E n

/-- The grouped shell sits inside the neighbourhood at its coarsest scale. -/
theorem brsOmega_subset_brsU {E : Set ℝ} {l : ℕ} (hl : 1 ≤ l) :
    brsOmega E l ⊆ brsU E (2 ^ (l - 1)) := by
  intro r hr
  rw [brsOmega] at hr
  obtain ⟨n, hn, hrn⟩ : ∃ n ∈ Finset.Ico (2 ^ (l - 1)) (2 ^ l), r ∈ brsD E n := by
    simpa only [Set.mem_iUnion, exists_prop] using hr
  rw [Finset.mem_Ico] at hn
  exact brsU_subset_of_le E hn.1 hrn.1

/-- **The measure of a grouped shell.** -/
theorem volume_brsOmega_le {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    {l : ℕ} (hl : 1 ≤ l) :
    volume (brsOmega E l) ≤
      ENNReal.ofReal (7 * (2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) *
        ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ≥0∞) := by
  refine le_trans (measure_mono (brsOmega_subset_brsU hl)) ?_
  have h := volume_brsU_le hE hEne (2 ^ (l - 1))
  have hcast : ((2 ^ (l - 1) : ℕ) : ℤ) = (2 ^ (l - 1) : ℤ) := by push_cast; ring
  rwa [hcast] at h

/-- The grouped shells are pairwise disjoint. -/
theorem brsOmega_disjoint (E : Set ℝ) {l l' : ℕ} (hl : 1 ≤ l) (hl' : 1 ≤ l')
    (hll : l ≠ l') : Disjoint (brsOmega E l) (brsOmega E l') := by
  refine Set.disjoint_left.mpr fun r hr hr' => ?_
  rw [brsOmega] at hr hr'
  obtain ⟨n, hn, hrn⟩ : ∃ n ∈ Finset.Ico (2 ^ (l - 1)) (2 ^ l), r ∈ brsD E n := by
    simpa only [Set.mem_iUnion, exists_prop] using hr
  obtain ⟨m, hm, hrm⟩ : ∃ m ∈ Finset.Ico (2 ^ (l' - 1)) (2 ^ l'), r ∈ brsD E m := by
    simpa only [Set.mem_iUnion, exists_prop] using hr'
  rw [Finset.mem_Ico] at hn hm
  have hnm : n ≠ m := by
    rcases lt_or_gt_of_ne hll with h | h
    · have h1 : l ≤ l' - 1 := by omega
      have h2 : (2 : ℕ) ^ l ≤ 2 ^ (l' - 1) :=
        Nat.pow_le_pow_right (by norm_num) h1
      omega
    · have h1 : l' ≤ l - 1 := by omega
      have h2 : (2 : ℕ) ^ l' ≤ 2 ^ (l - 1) :=
        Nat.pow_le_pow_right (by norm_num) h1
      omega
  exact (Set.disjoint_left.mp (brsD_disjoint E hnm)) hrn hrm

/-- The doubly exponential block `J_m = [2^{-2^{m+1}}, 2^{-2^m}]` of the
profile variable. -/
def brsLogBlock (m : ℕ) : Set ℝ :=
  Icc ((2 : ℝ) ^ (-(2 ^ (m + 1) : ℤ))) ((2 : ℝ) ^ (-(2 ^ m : ℤ)))

theorem brsLogBlock_pos {m : ℕ} {s : ℝ} (hs : s ∈ brsLogBlock m) : 0 < s := by
  have h := hs.1
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(2 ^ (m + 1) : ℤ)) := by positivity
  linarith

/-- **The logarithmic length of a block.**  The measure `s^{-1} ds` gives every
block the same order of magnitude `2^m`. -/
theorem integral_inv_brsLogBlock (m : ℕ) :
    (∫ s in ((2 : ℝ) ^ (-(2 ^ (m + 1) : ℤ)))..((2 : ℝ) ^ (-(2 ^ m : ℤ))), s⁻¹) =
      (2 : ℝ) ^ m * Real.log 2 := by
  have hlow : (0 : ℝ) < (2 : ℝ) ^ (-(2 ^ (m + 1) : ℤ)) := by positivity
  have hup : (0 : ℝ) < (2 : ℝ) ^ (-(2 ^ m : ℤ)) := by positivity
  rw [integral_inv_of_pos hlow hup]
  have hdiv : (2 : ℝ) ^ (-(2 ^ m : ℤ)) / (2 : ℝ) ^ (-(2 ^ (m + 1) : ℤ)) =
      (2 : ℝ) ^ ((2 ^ (m + 1) : ℤ) - (2 ^ m : ℤ)) := by
    rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [hdiv, Real.log_zpow]
  have hexp : ((2 ^ (m + 1) : ℤ) - (2 ^ m : ℤ)) = (2 ^ m : ℤ) := by
    have : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [this]
    ring
  rw [hexp]
  push_cast
  ring

end LogShells

/-! ## BRS (4.8) -/

section Eq48

open Auto.FractalDimensions

/-- **BRS (4.8).**  With `B` the supremum of
`δ^{1/q} N(E,δ)^{1/q} (log 1/δ)^{1/d}`, the grouped shell `Ω_ℓ` has measure
`≲ B^q 2^{-ℓ q/d}`: the doubly exponential scale `δ_ℓ = 2^{-2^{ℓ-1}}` turns the
logarithmic factor into a power of `2^ℓ`. -/
theorem volume_brsOmega_le_of_cov {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hEne : E.Nonempty) {q B : ℝ} {d : ℕ} (hq : 0 < q) (hd : 2 ≤ d) (hB : 0 < B)
    (hcov : ∀ l : ℕ, 1 ≤ l →
      ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (B ^ q * (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) *
          (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (d : ℝ)))))
    {l : ℕ} (hl : 1 ≤ l) :
    volume (brsOmega E l) ≤
      ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
        ((2 : ℝ) ^ (l - 1)) ^ (-(q / (d : ℝ)))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow2 : (0 : ℝ) < ((2 : ℝ) ^ (l - 1)) := by positivity
  have hBq : (0 : ℝ) < B ^ q := Real.rpow_pos_of_pos hB _
  refine le_trans (volume_brsOmega_le hE hEne hl) ?_
  refine le_trans (mul_le_mul' le_rfl (hcov l hl)) (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  -- the two doubly exponential powers cancel
  have hcancel : (2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ)) * (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  have hsplit : (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (d : ℝ))) =
      ((2 : ℝ) ^ (l - 1)) ^ (-(q / (d : ℝ))) * (Real.log 2) ^ (-(q / (d : ℝ))) :=
    Real.mul_rpow hpow2.le hlog2.le
  calc 7 * (2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ)) *
        (B ^ q * (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) *
          (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (d : ℝ))))
      = 7 * B ^ q * ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ)) * (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ))) *
          (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (d : ℝ))) := by ring
    _ = 7 * B ^ q * (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (d : ℝ))) := by
        rw [hcancel, mul_one]
    _ = 7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
          ((2 : ℝ) ^ (l - 1)) ^ (-(q / (d : ℝ))) := by
        rw [hsplit]
        ring

end Eq48

theorem measurableSet_brsLogBlock (m : ℕ) : MeasurableSet (brsLogBlock m) := by
  rw [brsLogBlock]
  exact measurableSet_Icc

/-- The `s^{-1}`-mass of a logarithmic block, as a `lintegral`. -/
theorem lintegral_inv_brsLogBlock (m : ℕ) :
    (∫⁻ s in brsLogBlock m, ENNReal.ofReal s⁻¹) =
      ENNReal.ofReal ((2 : ℝ) ^ m * Real.log 2) := by
  have hlow : (0 : ℝ) < (2 : ℝ) ^ (-(2 ^ (m + 1) : ℤ)) := by positivity
  have hup : (0 : ℝ) < (2 : ℝ) ^ (-(2 ^ m : ℤ)) := by positivity
  have hle : (2 : ℝ) ^ (-(2 ^ (m + 1) : ℤ)) ≤ (2 : ℝ) ^ (-(2 ^ m : ℤ)) := by
    refine zpow_le_zpow_right₀ (by norm_num) ?_
    have hpos : (0 : ℤ) < 2 ^ m := by positivity
    have h : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
    omega
  have hint : IntegrableOn (fun s : ℝ => s⁻¹) (brsLogBlock m) volume := by
    rw [brsLogBlock]
    refine (ContinuousOn.integrableOn_Icc ?_)
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro s hs
    exact (lt_of_lt_of_le hlow hs.1).ne'
  have hval : ENNReal.ofReal (∫ s in brsLogBlock m, s⁻¹) =
      ∫⁻ s in brsLogBlock m, ENNReal.ofReal s⁻¹ := by
    refine ofReal_integral_eq_lintegral_ofReal hint ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_brsLogBlock m)] with s hs
    have hspos : 0 < s := brsLogBlock_pos hs
    positivity
  rw [← hval]
  congr 1
  rw [brsLogBlock, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  exact integral_inv_brsLogBlock m

/-- **The per-block Hölder bound at the endpoint `p = p_d`.**  Hölder with the
conjugate pair `(d, p_d)` turns the weight `s^{-1/d}` into the logarithmic
length of the block. -/
theorem lintegral_logBlock_le {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℂ}
    (hg : Measurable g) (m : ℕ) :
    (∫⁻ s in brsLogBlock m,
        ENNReal.ofReal (s ^ (-(1 / (d : ℝ)))) * ENNReal.ofReal ‖g s‖) ≤
      ENNReal.ofReal (((2 : ℝ) ^ m * Real.log 2) ^ (1 / (d : ℝ))) *
        (∫⁻ s in brsLogBlock m,
          (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
            (((d : ℝ) - 1) / (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hd1lt : 1 < (d : ℝ) := by linarith
  -- the conjugate pair `(d, d/(d-1))`
  have hpq : (d : ℝ).HolderConjugate ((d : ℝ) / ((d : ℝ) - 1)) := by
    have h := Real.HolderConjugate.conjExponent hd1lt
    rwa [Real.conjExponent] at h
  have hmeas1 : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (-(1 / (d : ℝ)))) := by
    fun_prop
  have hmeas2 : Measurable fun s : ℝ => ENNReal.ofReal ‖g s‖ :=
    hg.norm.ennreal_ofReal
  have hkey := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (brsLogBlock m)) hpq hmeas1.aemeasurable hmeas2.aemeasurable
  simp only [Pi.mul_apply] at hkey
  refine le_trans hkey ?_
  -- identify the first factor with the logarithmic length
  have hweight : (∫⁻ s in brsLogBlock m,
      (ENNReal.ofReal (s ^ (-(1 / (d : ℝ))))) ^ (d : ℝ)) =
      ENNReal.ofReal ((2 : ℝ) ^ m * Real.log 2) := by
    rw [← lintegral_inv_brsLogBlock m]
    refine setLIntegral_congr_fun (measurableSet_brsLogBlock m) ?_
    intro s hs
    have hspos : 0 < s := brsLogBlock_pos hs
    simp only []
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hspos.le _) hdpos.le]
    congr 1
    rw [← Real.rpow_mul hspos.le,
      show -(1 / (d : ℝ)) * (d : ℝ) = -1 by field_simp, Real.rpow_neg_one]
  rw [hweight]
  refine mul_le_mul' (le_of_eq ?_) (le_of_eq ?_)
  · rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  · congr 1
    field_simp

theorem two_zpow_pow_le {i j : ℕ} (hij : i ≤ j) :
    (2 : ℝ) ^ (-(2 ^ j : ℤ)) ≤ (2 : ℝ) ^ (-(2 ^ i : ℤ)) := by
  refine zpow_le_zpow_right₀ (by norm_num) ?_
  have h : (2 : ℤ) ^ i ≤ (2 : ℤ) ^ j := pow_le_pow_right₀ (by norm_num) hij
  omega

/-- **The logarithmic blocks tile `[2^{-2^ℓ}, 1/2]`.** -/
theorem logBlock_cover {l : ℕ} (hl : 1 ≤ l) :
    Icc ((2 : ℝ) ^ (-(2 ^ l : ℤ))) (1 / 2 : ℝ) ⊆
      ⋃ m ∈ Finset.range l, brsLogBlock m := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  by_contra hcon
  have hnot : ∀ m : ℕ, m < l → s ∉ brsLogBlock m := by
    intro m hm hmem
    exact hcon (Set.mem_biUnion (Finset.mem_range.mpr hm) hmem)
  -- descend through the blocks
  have hdesc : ∀ m : ℕ, m ≤ l → s ≤ (2 : ℝ) ^ (-(2 ^ m : ℤ)) := by
    intro m hm
    induction m with
    | zero =>
        have h1 : (2 : ℝ) ^ (-(2 ^ 0 : ℤ)) = 1 / 2 := by norm_num
        rw [h1]
        exact hs2
    | succ j ih =>
        have hjl : j < l := by omega
        have hprev := ih (by omega)
        by_contra hge
        push Not at hge
        exact hnot j hjl ⟨hge.le, hprev⟩
  have hfinal := hdesc l le_rfl
  have hseq : s = (2 : ℝ) ^ (-(2 ^ l : ℤ)) := le_antisymm hfinal hs1
  -- then `s` is the lower endpoint of the block `l - 1`
  refine hnot (l - 1) (by omega) ?_
  rw [brsLogBlock]
  have hl1 : l - 1 + 1 = l := by omega
  rw [hl1]
  exact ⟨le_of_eq hseq.symm, by
    rw [hseq]
    exact two_zpow_pow_le (by omega)⟩

/-- **The top piece.**  On `[1/2, 6]` the weight `s^{-1/d}` is bounded, so
Hölder against the constant function applies. -/
theorem lintegral_top_piece_le {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℂ}
    (hg : Measurable g) :
    (∫⁻ s in Icc (1 / 2 : ℝ) 6,
        ENNReal.ofReal (s ^ (-(1 / (d : ℝ)))) * ENNReal.ofReal ‖g s‖) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
          ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) *
        (∫⁻ s in Icc (1 / 2 : ℝ) 6,
          (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
            (((d : ℝ) - 1) / (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hpd : (1 : ℝ) ≤ (d : ℝ) / ((d : ℝ) - 1) := by
    rw [le_div_iff₀ hd1]
    linarith
  -- the weight is bounded on the top piece
  have hweight : ∀ s ∈ Icc (1 / 2 : ℝ) 6,
      ENNReal.ofReal (s ^ (-(1 / (d : ℝ)))) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ))) := by
    intro s hs
    refine ENNReal.ofReal_le_ofReal ?_
    have hspos : (0 : ℝ) < s := by
      have := hs.1
      linarith
    have hnonpos : -(1 / (d : ℝ)) ≤ 0 := by
      simp only [neg_nonpos]
      positivity
    have hmono : s ^ (-(1 / (d : ℝ))) ≤ (1 / 2 : ℝ) ^ (-(1 / (d : ℝ))) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hs.1 hnonpos
    refine le_trans hmono (le_of_eq ?_)
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, ← Real.rpow_neg_one (2 : ℝ),
      ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  -- Hölder against the constant
  have hvol : (volume.restrict (Icc (1 / 2 : ℝ) 6)) univ =
      ENNReal.ofReal ((11 : ℝ) / 2) := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    congr 1
    norm_num
  have hholder := lintegral_le_rpow_mul_measure_univ
    (μ := volume.restrict (Icc (1 / 2 : ℝ) 6))
    (Φ := fun s => ENNReal.ofReal ‖g s‖) hg.norm.ennreal_ofReal hpd
  rw [hvol] at hholder
  set X : ENNReal := ∫⁻ s in Icc (1 / 2 : ℝ) 6,
    (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1)) with hX
  have hlast : ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ))) *
      (X ^ (1 / ((d : ℝ) / ((d : ℝ) - 1))) *
        ENNReal.ofReal ((11 : ℝ) / 2) ^ (1 - 1 / ((d : ℝ) / ((d : ℝ) - 1)))) =
      ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) * ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) *
        X ^ (((d : ℝ) - 1) / (d : ℝ)) := by
    have h1 : (1 : ℝ) / ((d : ℝ) / ((d : ℝ) - 1)) = ((d : ℝ) - 1) / (d : ℝ) :=
      one_div_div _ _
    have h2 : (1 : ℝ) - ((d : ℝ) - 1) / (d : ℝ) = 1 / (d : ℝ) := by
      field_simp
      ring
    rw [h1, h2,
      ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 2) (by positivity),
      ENNReal.ofReal_mul
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / (d : ℝ)))]
    ring
  calc (∫⁻ s in Icc (1 / 2 : ℝ) 6,
        ENNReal.ofReal (s ^ (-(1 / (d : ℝ)))) * ENNReal.ofReal ‖g s‖)
      ≤ ∫⁻ s in Icc (1 / 2 : ℝ) 6,
          ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ))) * ENNReal.ofReal ‖g s‖ := by
        refine setLIntegral_mono' measurableSet_Icc ?_
        intro s hs
        exact mul_le_mul' (hweight s hs) le_rfl
    _ = ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ))) *
          ∫⁻ s in Icc (1 / 2 : ℝ) 6, ENNReal.ofReal ‖g s‖ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ))) *
          (X ^ (1 / ((d : ℝ) / ((d : ℝ) - 1))) *
            ENNReal.ofReal ((11 : ℝ) / 2) ^ (1 - 1 / ((d : ℝ) / ((d : ℝ) - 1)))) := by
        refine mul_le_mul' le_rfl ?_
        rw [hX]
        exact hholder
    _ = ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) * ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) *
          X ^ (((d : ℝ) - 1) / (d : ℝ)) := hlast

/-- The local `L^{p_d}` norm of the profile on a logarithmic block. -/
def brsLogBlockNorm (d : ℕ) (g : ℝ → ℂ) (m : ℕ) : ENNReal :=
  (∫⁻ s in brsLogBlock m,
    (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^ (((d : ℝ) - 1) / (d : ℝ))

/-- The local `L^{p_d}` norm on the top piece `[1/2, 6]`. -/
def brsTopNorm (d : ℕ) (g : ℝ → ℂ) : ENNReal :=
  (∫⁻ s in Icc (1 / 2 : ℝ) 6,
    (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^ (((d : ℝ) - 1) / (d : ℝ))

/-- The weight attached to the logarithmic block `m` in the window of the
grouped shell `Ω_ℓ`. -/
def brsLogWeight (d : ℕ) (l m : ℕ) : ENNReal :=
  if m < l then ENNReal.ofReal (((2 : ℝ) ^ m * Real.log 2) ^ (1 / (d : ℝ))) else 0

/-- The endpoint exponent of the kernel weight: at `p = p_d` it is `-1/d`. -/
theorem brs_endpoint_exponent {d : ℕ} (hd : 2 ≤ d) :
    ((d : ℝ) - 1) * (1 - 1 / ((d : ℝ) / ((d : ℝ) - 1))) - 1 = -(1 / (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  rw [one_div_div]
  field_simp
  ring

/-- **Window to blocks at the endpoint.**  The window of `𝔐_{p_d}` on the
grouped shell `Ω_ℓ` is covered by the logarithmic blocks `m < ℓ` together with
the top piece. -/
theorem lintegral_window_le_logBlocks {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℂ}
    (hg : Measurable g) {l : ℕ} (hl : 1 ≤ l) :
    (∫⁻ s in Icc ((2 : ℝ) ^ (-(2 ^ l : ℤ))) 6,
        ENNReal.ofReal (s ^ (-(1 / (d : ℝ)))) * ENNReal.ofReal ‖g s‖) ≤
      (∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m) +
        ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) * ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) *
          brsTopNorm d g := by
  set F : ℝ → ENNReal := fun s =>
    ENNReal.ofReal (s ^ (-(1 / (d : ℝ)))) * ENNReal.ofReal ‖g s‖ with hF
  set A : ℕ → Set ℝ := fun m => if m < l then brsLogBlock m else ∅ with hA
  -- the window splits into the blocks and the top piece
  have hcover : Icc ((2 : ℝ) ^ (-(2 ^ l : ℤ))) 6 ⊆
      (⋃ m : ℕ, A m) ∪ Icc (1 / 2 : ℝ) 6 := by
    intro s hs
    by_cases htop : s ≤ 1 / 2
    · refine Or.inl ?_
      obtain ⟨m, hm, hmem⟩ : ∃ m : ℕ, m < l ∧ s ∈ brsLogBlock m := by
        have hcov := logBlock_cover hl ⟨hs.1, htop⟩
        simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hcov
        exact hcov
      refine Set.mem_iUnion.mpr ⟨m, ?_⟩
      rw [hA]
      simp only [if_pos hm]
      exact hmem
    · push Not at htop
      exact Or.inr ⟨htop.le, hs.2⟩
  have hterm : ∀ m : ℕ, (∫⁻ s in A m, F s) ≤
      brsLogWeight d l m * brsLogBlockNorm d g m := by
    intro m
    by_cases hm : m < l
    · have hAm : A m = brsLogBlock m := by
        rw [hA]
        simp only [if_pos hm]
      rw [hAm, brsLogWeight, if_pos hm, brsLogBlockNorm, hF]
      exact lintegral_logBlock_le hd hg m
    · have hAm : A m = ∅ := by
        rw [hA]
        simp only [if_neg hm]
      rw [hAm]
      simp
  calc (∫⁻ s in Icc ((2 : ℝ) ^ (-(2 ^ l : ℤ))) 6, F s)
      ≤ ∫⁻ s in (⋃ m : ℕ, A m) ∪ Icc (1 / 2 : ℝ) 6, F s := lintegral_mono_set hcover
    _ ≤ (∫⁻ s in ⋃ m : ℕ, A m, F s) + ∫⁻ s in Icc (1 / 2 : ℝ) 6, F s :=
        lintegral_union_le _ _ _
    _ ≤ (∑' m : ℕ, ∫⁻ s in A m, F s) + ∫⁻ s in Icc (1 / 2 : ℝ) 6, F s := by
        refine add_le_add ?_ le_rfl
        exact lintegral_iUnion_le _ _
    _ ≤ (∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m) +
          ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
            ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) * brsTopNorm d g := by
        refine add_le_add (ENNReal.tsum_le_tsum hterm) ?_
        rw [brsTopNorm, hF]
        exact lintegral_top_piece_le hd hg

/-- **The shell bound at the endpoint.**  On the grouped shell `Ω_ℓ` the main
term at `p = p_d` is bounded by the weighted sum over the logarithmic blocks
`m < ℓ` plus the top piece. -/
theorem brsMainMaximal_le_on_brsOmega {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {g : ℝ → ℂ} (hg : Measurable g) {l : ℕ} (hl : 1 ≤ l)
    {r : ℝ} (hr : r ∈ brsOmega E l) :
    brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ≤
      ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
        ((∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m) +
          ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) * ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) *
            brsTopNorm d g) := by
  -- locate the shell containing `r`
  obtain ⟨n, hn, hrn⟩ : ∃ n ∈ Finset.Ico (2 ^ (l - 1)) (2 ^ l), r ∈ brsD E n := by
    rw [brsOmega] at hr
    simpa only [Set.mem_iUnion, exists_prop] using hr
  rw [Finset.mem_Ico] at hn
  -- the cutoff on the shell, with the endpoint exponent
  have hcut := brsMainMaximal_le_on_brsD (p := (d : ℝ) / ((d : ℝ) - 1)) hd hE g hrn
  rw [brs_endpoint_exponent hd] at hcut
  refine le_trans hcut ?_
  refine mul_le_mul' le_rfl ?_
  -- enlarge the window to the coarsest scale of the grouped shell
  have hwin : Icc ((2 : ℝ) ^ (-(n : ℤ))) 6 ⊆ Icc ((2 : ℝ) ^ (-(2 ^ l : ℤ))) 6 := by
    refine Icc_subset_Icc ?_ le_rfl
    refine zpow_le_zpow_right₀ (by norm_num) ?_
    have hcast : ((n : ℤ)) ≤ ((2 ^ l : ℕ) : ℤ) := by
      exact_mod_cast le_of_lt hn.2
    push_cast at hcast
    omega
  refine le_trans (lintegral_mono_set hwin) ?_
  exact lintegral_window_le_logBlocks hd hg hl

/-- **Integration of the endpoint shell bound over `Ω_ℓ`.** -/
theorem lintegral_brsOmega_le {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {q : ℝ} (hq : 0 < q)
    {g : ℝ → ℂ} (hg : Measurable g) {l : ℕ} (hl : 1 ≤ l) :
    (∫⁻ r in brsOmega E l, ENNReal.ofReal r ^ (d - 1) *
        brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q) ≤
      ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
          (ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
            ((∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m) +
              ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
                ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) * brsTopNorm d g)) ^ q *
        volume (brsOmega E l) := by
  set W : ENNReal := ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
    ((∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m) +
      ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) * ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) *
        brsTopNorm d g) with hW
  set K : ENNReal := ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) * W ^ q with hK
  have hpoint : ∀ r ∈ brsOmega E l,
      ENNReal.ofReal r ^ (d - 1) *
        brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q ≤ K := by
    intro r hr
    have hrU0 : r ∈ brsU E 0 :=
      brsU_subset_of_le E (Nat.zero_le (2 ^ (l - 1))) (brsOmega_subset_brsU hl hr)
    have hweight := weight_le_of_mem_brsU_zero (d := d) hE hEne hrU0
    have hmax : brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q ≤ W ^ q := by
      refine ENNReal.rpow_le_rpow ?_ hq.le
      rw [hW]
      exact brsMainMaximal_le_on_brsOmega hd hE hg hl hr
    rw [hK]
    exact mul_le_mul' hweight hmax
  calc (∫⁻ r in brsOmega E l, ENNReal.ofReal r ^ (d - 1) *
        brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q)
      ≤ ∫⁻ _r in brsOmega E l, K :=
        setLIntegral_mono' (measurableSet_brsOmega E l) hpoint
    _ = K * volume (brsOmega E l) := setLIntegral_const _ _
    _ = ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) * W ^ q * volume (brsOmega E l) := by
        rw [hK]

theorem one_lt_two_rpow_inv_d {d : ℕ} (hd : 2 ≤ d) : 1 < (2 : ℝ) ^ (1 / (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  refine Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, ?_⟩)
  positivity

/-- The block weight is a geometric sequence in `m` with ratio `2^{1/d}`. -/
theorem brsLogWeight_eq {d : ℕ} (hd : 2 ≤ d) {l m : ℕ} (hm : m < l) :
    brsLogWeight d l m =
      ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) *
        ((2 : ℝ) ^ (1 / (d : ℝ))) ^ m) := by
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [brsLogWeight, if_pos hm]
  congr 1
  rw [Real.mul_rpow (by positivity) hlog2, mul_comm]
  congr 1
  rw [← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((2 : ℝ) ^ (1 / (d : ℝ))) m, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- **The total block weight of a grouped shell.** -/
theorem tsum_brsLogWeight_le {d : ℕ} (hd : 2 ≤ d) (l : ℕ) :
    (∑' m : ℕ, brsLogWeight d l m) ≤
      ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) *
        (((2 : ℝ) ^ (1 / (d : ℝ))) ^ l / ((2 : ℝ) ^ (1 / (d : ℝ)) - 1))) := by
  set y : ℝ := (2 : ℝ) ^ (1 / (d : ℝ)) with hy
  have hy1 : 1 < y := by
    rw [hy]
    exact one_lt_two_rpow_inv_d hd
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogd : (0 : ℝ) < (Real.log 2) ^ (1 / (d : ℝ)) :=
    Real.rpow_pos_of_pos hlog2 _
  have hvanish : ∀ m : ℕ, m ∉ Finset.range l → brsLogWeight d l m = 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [brsLogWeight, if_neg hm]
  rw [tsum_eq_sum hvanish]
  have hterm : ∀ m ∈ Finset.range l, brsLogWeight d l m =
      ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) * y ^ m) := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [brsLogWeight_eq hd hm, hy]
  rw [Finset.sum_congr rfl hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (sum_geom_le hy1 l) hlogd.le

/-- **The shell weights of a single block, summed over the shells that see
it.**  The geometric factor `2^{-ℓ/d}` makes the sum uniform in `m`. -/
theorem tsum_logShell_single_block_le {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    (∑' l : ℕ, (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) ^ l *
        brsLogWeight d l m) ≤
      ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) *
          ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹)⁻¹ := by
  set y : ℝ := (2 : ℝ) ^ (1 / (d : ℝ)) with hy
  have hy1 : 1 < y := by
    rw [hy]
    exact one_lt_two_rpow_inv_d hd
  have hypos : 0 < y := lt_trans zero_lt_one hy1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogd : (0 : ℝ) < (Real.log 2) ^ (1 / (d : ℝ)) :=
    Real.rpow_pos_of_pos hlog2 _
  set z : ENNReal := ENNReal.ofReal y⁻¹ with hz
  -- rewrite each term
  have hterm : ∀ l : ℕ, z ^ l * brsLogWeight d l m =
      ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) * y ^ m) *
        (if m + 1 ≤ l then z ^ l else 0) := by
    intro l
    by_cases hl : m < l
    · rw [brsLogWeight_eq hd hl, if_pos (by omega), hy, mul_comm]
    · have hl' : ¬ (m + 1 ≤ l) := by omega
      rw [brsLogWeight, if_neg hl, if_neg hl', mul_zero, mul_zero]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, tsum_geometric_tail]
  -- collect the constants
  have hzpow : z ^ (m + 1) = ENNReal.ofReal ((y⁻¹) ^ (m + 1)) := by
    rw [hz, ← ENNReal.ofReal_pow (by positivity)]
  rw [hzpow, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' (le_of_eq ?_) le_rfl
  congr 1
  rw [show (y⁻¹) ^ (m + 1) = (y⁻¹) ^ m * y⁻¹ by rw [pow_succ]]
  rw [show (Real.log 2) ^ (1 / (d : ℝ)) * y ^ m * ((y⁻¹) ^ m * y⁻¹) =
      (Real.log 2) ^ (1 / (d : ℝ)) * y⁻¹ * (y ^ m * (y⁻¹) ^ m) by ring,
    show y ^ m * (y⁻¹) ^ m = 1 by
      rw [← mul_pow, mul_inv_cancel₀ hypos.ne', one_pow],
    mul_one]

/-- **The double sum over grouped shells and logarithmic blocks.** -/
theorem tsum_logShell_block_le {d : ℕ} (hd : 2 ≤ d) {q : ℝ} (g : ℝ → ℂ) :
    (∑' l : ℕ, (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) ^ l *
        ∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m ^ q) ≤
      ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) *
          ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) *
          (1 - ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹)⁻¹ *
        ∑' m : ℕ, brsLogBlockNorm d g m ^ q := by
  set z : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹ with hz
  set M : ENNReal := ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) *
    ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) *
    (1 - ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹)⁻¹ with hM
  calc (∑' l : ℕ, z ^ l *
        ∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m ^ q)
      = ∑' l : ℕ, ∑' m : ℕ,
          z ^ l * (brsLogWeight d l m * brsLogBlockNorm d g m ^ q) := by
        refine tsum_congr fun l => ?_
        rw [ENNReal.tsum_mul_left]
    _ = ∑' m : ℕ, ∑' l : ℕ,
          z ^ l * (brsLogWeight d l m * brsLogBlockNorm d g m ^ q) :=
        ENNReal.tsum_comm
    _ = ∑' m : ℕ, (∑' l : ℕ, z ^ l * brsLogWeight d l m) *
          brsLogBlockNorm d g m ^ q := by
        refine tsum_congr fun m => ?_
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun l => ?_
        ring
    _ ≤ ∑' m : ℕ, M * brsLogBlockNorm d g m ^ q := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        refine mul_le_mul' ?_ le_rfl
        rw [hM, hz]
        exact tsum_logShell_single_block_le hd m
    _ = M * ∑' m : ℕ, brsLogBlockNorm d g m ^ q := ENNReal.tsum_mul_left

/-- The half-open logarithmic block, so that the family tiles `(0, 1/2]`. -/
def brsLogBlockIoc (m : ℕ) : Set ℝ :=
  Ioc ((2 : ℝ) ^ (-(2 ^ (m + 1) : ℤ))) ((2 : ℝ) ^ (-(2 ^ m : ℤ)))

theorem measurableSet_brsLogBlockIoc (m : ℕ) :
    MeasurableSet (brsLogBlockIoc m) := by
  rw [brsLogBlockIoc]
  exact measurableSet_Ioc

theorem brsLogBlockIoc_disjoint :
    Pairwise (Function.onFun Disjoint brsLogBlockIoc) := by
  intro i j hij
  have hkey : ∀ a b : ℕ, a < b → Disjoint (brsLogBlockIoc a) (brsLogBlockIoc b) := by
    intro a b hab
    refine Set.disjoint_left.mpr fun s hsa hsb => ?_
    have hlow : (2 : ℝ) ^ (-(2 ^ (a + 1) : ℤ)) < s := hsa.1
    have hup : s ≤ (2 : ℝ) ^ (-(2 ^ b : ℤ)) := hsb.2
    have hstep : (2 : ℝ) ^ (-(2 ^ b : ℤ)) ≤ (2 : ℝ) ^ (-(2 ^ (a + 1) : ℤ)) :=
      two_zpow_pow_le (by omega)
    linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact hkey i j h
  · exact (hkey j i h).symm

theorem brsLogBlockIoc_subset_Ioi (m : ℕ) : brsLogBlockIoc m ⊆ Ioi (0 : ℝ) := by
  intro s hs
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-(2 ^ (m + 1) : ℤ)) := by positivity
  have h := hs.1
  simp only [mem_Ioi]
  linarith

/-- **The logarithmic blocks recover the global `L^{p_d}` norm.** -/
theorem tsum_brsLogBlockNorm_rpow_le {d : ℕ} (hd : 2 ≤ d) (g : ℝ → ℂ) :
    (∑' m : ℕ, brsLogBlockNorm d g m ^ ((d : ℝ) / ((d : ℝ) - 1))) ≤
      ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hpd : (0 : ℝ) < (d : ℝ) / ((d : ℝ) - 1) := div_pos hdpos hd1
  have hterm : ∀ m : ℕ,
      brsLogBlockNorm d g m ^ ((d : ℝ) / ((d : ℝ) - 1)) =
        ∫⁻ s in brsLogBlockIoc m,
          (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1)) := by
    intro m
    rw [brsLogBlockNorm, ← ENNReal.rpow_mul,
      show ((d : ℝ) - 1) / (d : ℝ) * ((d : ℝ) / ((d : ℝ) - 1)) = 1 by field_simp,
      ENNReal.rpow_one, brsLogBlock, brsLogBlockIoc]
    exact (setLIntegral_congr Ioc_ae_eq_Icc).symm
  rw [tsum_congr hterm,
    ← lintegral_iUnion (s := brsLogBlockIoc) measurableSet_brsLogBlockIoc
      brsLogBlockIoc_disjoint]
  refine lintegral_mono_set ?_
  exact Set.iUnion_subset brsLogBlockIoc_subset_Ioi

/-- Splitting a `q`-th power of a sum. -/
theorem ennreal_rpow_add_le {X Y : ENNReal} {q : ℝ} (hq : 0 ≤ q) :
    (X + Y) ^ q ≤ 2 ^ q * (X ^ q + Y ^ q) := by
  have hmax : X + Y ≤ 2 * max X Y := by
    have h1 : X ≤ max X Y := le_max_left _ _
    have h2 : Y ≤ max X Y := le_max_right _ _
    calc X + Y ≤ max X Y + max X Y := add_le_add h1 h2
      _ = 2 * max X Y := by rw [two_mul]
  calc (X + Y) ^ q ≤ (2 * max X Y) ^ q := ENNReal.rpow_le_rpow hmax hq
    _ = 2 ^ q * (max X Y) ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq
    _ ≤ 2 ^ q * (X ^ q + Y ^ q) := by
        refine mul_le_mul' le_rfl ?_
        rcases le_total X Y with h | h
        · rw [max_eq_right h]
          exact le_add_self
        · rw [max_eq_left h]
          exact le_self_add

/-- The zeroth grouped shell is empty. -/
theorem brsOmega_zero (E : Set ℝ) : brsOmega E 0 = ∅ := by
  rw [brsOmega]
  simp

/-- The grouped shells are pairwise disjoint, including the empty one. -/
theorem brsOmega_disjoint' (E : Set ℝ) {l l' : ℕ} (hll : l ≠ l') :
    Disjoint (brsOmega E l) (brsOmega E l') := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · rw [hl, brsOmega_zero]
    exact disjoint_bot_left
  rcases Nat.eq_zero_or_pos l' with hl' | hl'
  · rw [hl', brsOmega_zero]
    exact disjoint_bot_right
  exact brsOmega_disjoint E hl hl' hll

/-- The first neighbourhood is bounded. -/
theorem brsU_zero_subset {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) :
    brsU E 0 ⊆ Icc (-2 : ℝ) 5 := by
  intro r hr
  have hdist : Metric.infDist r E ≤ 2 * (2 : ℝ) ^ (-(0 : ℕ) : ℤ) := hr
  have hdist' : Metric.infDist r E ≤ 2 := by simpa using hdist
  obtain ⟨t, htE, hrt⟩ := (Metric.infDist_lt_iff hEne).mp
    (lt_of_le_of_lt hdist' (by norm_num : (2 : ℝ) < 3))
  have ht1 : (1 : ℝ) ≤ t := (hE htE).1
  have ht2 : t ≤ 2 := (hE htE).2
  rw [Real.dist_eq, abs_lt] at hrt
  exact ⟨by linarith [hrt.1], by linarith [hrt.2]⟩

theorem volume_brsU_zero_le {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hEne : E.Nonempty) : volume (brsU E 0) ≤ ENNReal.ofReal 7 := by
  refine le_trans (measure_mono (brsU_zero_subset hE hEne)) ?_
  rw [Real.volume_Icc]
  refine ENNReal.ofReal_le_ofReal ?_
  norm_num

/-- **The total measure of the grouped shells.** -/
theorem tsum_volume_brsOmega_le {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hEne : E.Nonempty) :
    (∑' l : ℕ, volume (brsOmega E l)) ≤ ENNReal.ofReal 7 := by
  have hdisj : Pairwise (Function.onFun Disjoint (brsOmega E)) := by
    intro l l' hll
    exact brsOmega_disjoint' E hll
  have hsub : (⋃ l : ℕ, brsOmega E l) ⊆ brsU E 0 := by
    refine Set.iUnion_subset fun l => ?_
    rcases Nat.eq_zero_or_pos l with hl | hl
    · rw [hl, brsOmega_zero]
      exact Set.empty_subset _
    · exact fun r hr =>
        brsU_subset_of_le E (Nat.zero_le (2 ^ (l - 1))) (brsOmega_subset_brsU hl hr)
  calc (∑' l : ℕ, volume (brsOmega E l))
      = volume (⋃ l : ℕ, brsOmega E l) :=
        (measure_iUnion hdisj (fun l => measurableSet_brsOmega E l)).symm
    _ ≤ volume (brsU E 0) := measure_mono hsub
    _ ≤ ENNReal.ofReal 7 := volume_brsU_zero_le hE hEne

/-- Every positive shell index lies in exactly one dyadic group. -/
theorem exists_grouped_shell {n : ℕ} (hn : 1 ≤ n) :
    ∃ l : ℕ, 1 ≤ l ∧ n ∈ Finset.Ico (2 ^ (l - 1)) (2 ^ l) := by
  classical
  have hex : ∃ l : ℕ, n < 2 ^ l := ⟨n, Nat.lt_two_pow_self⟩
  have hlt : n < 2 ^ Nat.find hex := Nat.find_spec hex
  have hl1 : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, pow_zero] at hlt
      omega
    · exact h
  have hmin : ¬ (n < 2 ^ (Nat.find hex - 1)) := Nat.find_min hex (by omega)
  exact ⟨Nat.find hex, hl1, Finset.mem_Ico.mpr ⟨by omega, hlt⟩⟩

/-- **Reduction to the zeroth shell and the grouped shells.** -/
theorem lintegral_le_brsD_zero_add_tsum_brsOmega {d : ℕ} {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) (hEnull : volume (closure E) = 0)
    {p q : ℝ} (hq : 0 < q) (g : ℝ → ℂ) :
    (∫⁻ r, ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q) ≤
      (∫⁻ r in brsD E 0,
          ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q) +
        ∑' l : ℕ, ∫⁻ r in brsOmega E l,
          ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q := by
  set F : ℝ → ENNReal := fun r =>
    ENNReal.ofReal r ^ (d - 1) * brsMainMaximal d E p g r ^ q with hF
  have hzero : ∀ r, r ∉ brsU E 0 → F r = 0 := by
    intro r hr
    rw [hF]
    simp only []
    rw [brsMainMaximal_eq_zero_of_notMem_brsU_zero hE g hr,
      ENNReal.zero_rpow_of_pos hq, mul_zero]
  have hcover : brsU E 0 ⊆ (brsD E 0 ∪ ⋃ l : ℕ, brsOmega E l) ∪ closure E := by
    intro r hr
    by_cases hmem : r ∈ ⋃ n : ℕ, brsD E n
    · obtain ⟨n, hrn⟩ := Set.mem_iUnion.mp hmem
      refine Or.inl ?_
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact Or.inl (hn ▸ hrn)
      · obtain ⟨l, hl, hnl⟩ := exists_grouped_shell hn
        refine Or.inr (Set.mem_iUnion.mpr ⟨l, ?_⟩)
        rw [brsOmega]
        exact Set.mem_iUnion₂.mpr ⟨n, hnl, hrn⟩
    · refine Or.inr ?_
      have hd0 := infDist_eq_zero_of_notMem_iUnion_brsD hr hmem
      rwa [← Metric.mem_closure_iff_infDist_zero hEne] at hd0
  calc (∫⁻ r, F r) = ∫⁻ r in brsU E 0, F r := by
        rw [← lintegral_indicator (measurableSet_brsU E 0)]
        refine lintegral_congr fun r => ?_
        by_cases hr : r ∈ brsU E 0
        · rw [Set.indicator_of_mem hr]
        · rw [Set.indicator_of_notMem hr, hzero r hr]
    _ ≤ ∫⁻ r in (brsD E 0 ∪ ⋃ l : ℕ, brsOmega E l) ∪ closure E, F r :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ r in brsD E 0 ∪ ⋃ l : ℕ, brsOmega E l, F r) +
          ∫⁻ r in closure E, F r := lintegral_union_le _ _ _
    _ = ∫⁻ r in brsD E 0 ∪ ⋃ l : ℕ, brsOmega E l, F r := by
        rw [setLIntegral_measure_zero _ _ hEnull, add_zero]
    _ ≤ (∫⁻ r in brsD E 0, F r) + ∫⁻ r in ⋃ l : ℕ, brsOmega E l, F r :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ r in brsD E 0, F r) + ∑' l : ℕ, ∫⁻ r in brsOmega E l, F r :=
        add_le_add le_rfl (lintegral_iUnion_le _ _)

/-- On the zeroth shell the endpoint main term is controlled by the top
piece alone. -/
theorem brsMainMaximal_le_on_brsD_zero {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {g : ℝ → ℂ} (hg : Measurable g) {r : ℝ}
    (hr : r ∈ brsD E 0) :
    brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ≤
      ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
        (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) * ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) *
          brsTopNorm d g) := by
  have hcut := brsMainMaximal_le_on_brsD (p := (d : ℝ) / ((d : ℝ) - 1)) hd hE g hr
  rw [brs_endpoint_exponent hd] at hcut
  refine le_trans hcut ?_
  refine mul_le_mul' le_rfl ?_
  have hwin : Icc ((2 : ℝ) ^ (-(0 : ℕ) : ℤ)) 6 ⊆ Icc (1 / 2 : ℝ) 6 := by
    refine Icc_subset_Icc ?_ le_rfl
    norm_num
  refine le_trans (lintegral_mono_set hwin) ?_
  rw [brsTopNorm]
  exact lintegral_top_piece_le hd hg

/-- **The zeroth shell contributes a bounded multiple of the top norm.** -/
theorem lintegral_brsD_zero_le {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {q : ℝ} (hq : 0 < q)
    {g : ℝ → ℂ} (hg : Measurable g) :
    (∫⁻ r in brsD E 0, ENNReal.ofReal r ^ (d - 1) *
        brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q) ≤
      ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
          (ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
            (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
                ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) * brsTopNorm d g)) ^ q *
        ENNReal.ofReal 7 := by
  set W : ENNReal := ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
    (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) * ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) *
      brsTopNorm d g) with hW
  set K : ENNReal := ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) * W ^ q with hK
  have hpoint : ∀ r ∈ brsD E 0,
      ENNReal.ofReal r ^ (d - 1) *
        brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q ≤ K := by
    intro r hr
    have hrU0 : r ∈ brsU E 0 := hr.1
    have hweight := weight_le_of_mem_brsU_zero (d := d) hE hEne hrU0
    have hmax : brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q ≤ W ^ q := by
      refine ENNReal.rpow_le_rpow ?_ hq.le
      rw [hW]
      exact brsMainMaximal_le_on_brsD_zero hd hE hg hr
    rw [hK]
    exact mul_le_mul' hweight hmax
  calc (∫⁻ r in brsD E 0, ENNReal.ofReal r ^ (d - 1) *
        brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q)
      ≤ ∫⁻ _r in brsD E 0, K :=
        setLIntegral_mono' (measurableSet_brsD E 0) hpoint
    _ = K * volume (brsD E 0) := setLIntegral_const _ _
    _ ≤ K * ENNReal.ofReal 7 := by
        refine mul_le_mul' le_rfl ?_
        refine le_trans (measure_mono ?_) (volume_brsU_zero_le hE hEne)
        exact fun r hr => hr.1
    _ = ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) * W ^ q * ENNReal.ofReal 7 := by rw [hK]

section Prop46

open Auto.FractalDimensions

/-- **The endpoint shell factor collapses.**  The total block weight of the
shell, raised to the power `q - 1`, cancels against the measure bound for
`Ω_ℓ` down to the geometric factor `2^{-ℓ/d}`. -/
theorem logShell_factor_identity {d : ℕ} {q K : ℝ} (hK : 0 ≤ K) {l : ℕ}
    (hl : 1 ≤ l) :
    (K * ((2 : ℝ) ^ (1 / (d : ℝ))) ^ l) ^ (q - 1) *
        ((2 : ℝ) ^ (l - 1)) ^ (-(q / (d : ℝ))) =
      K ^ (q - 1) * ((2 : ℝ) ^ (1 / (d : ℝ))) ^ q *
        (((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) ^ l := by
  have hcast : (((l - 1 : ℕ) : ℝ)) = (l : ℝ) - 1 := by
    have : (1 : ℕ) ≤ l := hl
    push_cast [Nat.cast_sub this]
    ring
  rw [Real.mul_rpow hK (by positivity), two_rpow_pow (1 / (d : ℝ)) l,
    two_rpow_rpow, two_rpow_rpow, two_rpow_inv_pow,
    ← Real.rpow_natCast (2 : ℝ) (l - 1), Real.rpow_natCast (2 : ℝ) (l - 1),
    ← Real.rpow_natCast (2 : ℝ) (l - 1), two_rpow_rpow]
  rw [show (K ^ (q - 1) * (2 : ℝ) ^ (1 / (d : ℝ) * ↑l * (q - 1))) *
      (2 : ℝ) ^ ((l - 1 : ℕ) * -(q / (d : ℝ))) =
      K ^ (q - 1) * ((2 : ℝ) ^ (1 / (d : ℝ) * ↑l * (q - 1)) *
        (2 : ℝ) ^ ((l - 1 : ℕ) * -(q / (d : ℝ)))) by ring,
    show K ^ (q - 1) * (2 : ℝ) ^ (1 / (d : ℝ) * q) *
        (2 : ℝ) ^ (-(1 / (d : ℝ)) * ↑l) =
      K ^ (q - 1) * ((2 : ℝ) ^ (1 / (d : ℝ) * q) *
        (2 : ℝ) ^ (-(1 / (d : ℝ)) * ↑l)) by ring]
  congr 1
  rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num), hcast]
  congr 1
  field_simp
  ring

/-- **The endpoint per-shell estimate.**  Weighted Hölder in the block index
turns the shell sum into a geometric factor times the `q`-th powers of the
block norms. -/
theorem logShell_term_le {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {q B : ℝ} (hq : 1 ≤ q)
    (hB : 0 < B)
    (hcov : ∀ l : ℕ, 1 ≤ l →
      ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (B ^ q * (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) *
          (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (d : ℝ)))))
    (g : ℝ → ℂ) {l : ℕ} (hl : 1 ≤ l) :
    (∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m) ^ q *
        volume (brsOmega E l) ≤
      ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
          ((Real.log 2) ^ (1 / (d : ℝ)) / ((2 : ℝ) ^ (1 / (d : ℝ)) - 1)) ^ (q - 1) *
          ((2 : ℝ) ^ (1 / (d : ℝ))) ^ q) *
        (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) ^ l *
        (∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m ^ q) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hq1 : (0 : ℝ) ≤ q - 1 := by linarith
  set y : ℝ := (2 : ℝ) ^ (1 / (d : ℝ)) with hy
  have hy1 : 1 < y := by
    rw [hy]
    exact one_lt_two_rpow_inv_d hd
  have hypos : (0 : ℝ) < y := lt_trans zero_lt_one hy1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := (Real.log 2) ^ (1 / (d : ℝ)) / (y - 1) with hKdef
  have hKpos : (0 : ℝ) < K := by
    rw [hKdef]
    exact div_pos (Real.rpow_pos_of_pos hlog2 _) (by linarith)
  set G : ℕ → ENNReal := fun m => brsLogBlockNorm d g m with hG
  set w : ℕ → ENNReal := fun m => brsLogWeight d l m with hw
  -- weighted Hölder in the block index
  have hhol : (∑' m : ℕ, w m * G m) ^ q ≤
      (∑' m : ℕ, w m * G m ^ q) * (∑' m : ℕ, w m) ^ (q - 1) := by
    refine le_trans (ENNReal.rpow_le_rpow (tsum_weighted_le w G hq) hq0.le) ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
    refine mul_le_mul' le_rfl (le_of_eq ?_)
    congr 1
    field_simp
  -- the total weight of the shell
  have hKy : (0 : ℝ) < K * y ^ l := mul_pos hKpos (pow_pos hypos l)
  have hweight : (∑' m : ℕ, w m) ^ (q - 1) ≤
      ENNReal.ofReal ((K * y ^ l) ^ (q - 1)) := by
    have hsum : (∑' m : ℕ, w m) ≤ ENNReal.ofReal (K * y ^ l) := by
      rw [hw]
      refine le_trans (tsum_brsLogWeight_le hd l) (le_of_eq ?_)
      congr 1
      rw [hKdef, hy]
      ring
    calc (∑' m : ℕ, w m) ^ (q - 1) ≤ (ENNReal.ofReal (K * y ^ l)) ^ (q - 1) :=
          ENNReal.rpow_le_rpow hsum hq1
      _ = ENNReal.ofReal ((K * y ^ l) ^ (q - 1)) :=
          ENNReal.ofReal_rpow_of_pos hKy
  -- the measure of the shell
  have hvol : volume (brsOmega E l) ≤
      ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
        ((2 : ℝ) ^ (l - 1)) ^ (-(q / (d : ℝ)))) :=
    volume_brsOmega_le_of_cov hE hEne hq0 hd hB hcov hl
  calc (∑' m : ℕ, w m * G m) ^ q * volume (brsOmega E l)
      ≤ ((∑' m : ℕ, w m * G m ^ q) * ENNReal.ofReal ((K * y ^ l) ^ (q - 1))) *
          ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
            ((2 : ℝ) ^ (l - 1)) ^ (-(q / (d : ℝ)))) :=
        mul_le_mul' (le_trans hhol (mul_le_mul' le_rfl hweight)) hvol
    _ = ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
              ((2 : ℝ) ^ (l - 1)) ^ (-(q / (d : ℝ)))) *
            ENNReal.ofReal ((K * y ^ l) ^ (q - 1)) *
          (∑' m : ℕ, w m * G m ^ q) := by ring
    _ = ENNReal.ofReal ((7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ)))) *
            ((K * y ^ l) ^ (q - 1) * ((2 : ℝ) ^ (l - 1)) ^ (-(q / (d : ℝ))))) *
          (∑' m : ℕ, w m * G m ^ q) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
    _ = ENNReal.ofReal ((7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ)))) *
            (K ^ (q - 1) * y ^ q * (y⁻¹) ^ l)) *
          (∑' m : ℕ, w m * G m ^ q) := by
        rw [logShell_factor_identity (q := q) (K := K) hKpos.le hl]
    _ = ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
            K ^ (q - 1) * y ^ q) * ENNReal.ofReal ((y⁻¹) ^ l) *
          (∑' m : ℕ, w m * G m ^ q) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
    _ = ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
            K ^ (q - 1) * y ^ q) * (ENNReal.ofReal y⁻¹) ^ l *
          (∑' m : ℕ, w m * G m ^ q) := by
        rw [ENNReal.ofReal_pow (by positivity)]

/-- The local norm on the top piece is dominated by the global one. -/
theorem brsTopNorm_le {d : ℕ} (hd : 2 ≤ d) (g : ℝ → ℂ) :
    brsTopNorm d g ≤
      (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
        (((d : ℝ) - 1) / (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  rw [brsTopNorm]
  refine ENNReal.rpow_le_rpow (lintegral_mono_set ?_) (by positivity)
  intro s hs
  have h : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num) hs.1
  exact h

/-- The `q`-th powers of the block norms sum to at most the `q`-th power of the
global `L^{p_d}` norm. -/
theorem tsum_brsLogBlockNorm_pow_le {d : ℕ} (hd : 2 ≤ d) {q : ℝ}
    (hpq : (d : ℝ) / ((d : ℝ) - 1) ≤ q) (g : ℝ → ℂ) :
    (∑' m : ℕ, brsLogBlockNorm d g m ^ q) ≤
      ((∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
        (((d : ℝ) - 1) / (d : ℝ))) ^ q := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hpd : (0 : ℝ) < (d : ℝ) / ((d : ℝ) - 1) := div_pos hdpos hd1
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le hpd hpq
  have hinv : 1 / ((d : ℝ) / ((d : ℝ) - 1)) = ((d : ℝ) - 1) / (d : ℝ) := one_div_div _ _
  have h1 := tsum_rpow_le_tsum_rpow (brsLogBlockNorm d g) hpd hpq
  rw [hinv] at h1
  have h2 : (∑' m : ℕ, brsLogBlockNorm d g m ^ q) ^ (1 / q) ≤
      (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
        (((d : ℝ) - 1) / (d : ℝ)) := by
    refine le_trans h1 ?_
    exact ENNReal.rpow_le_rpow (tsum_brsLogBlockNorm_rpow_le hd g) (by positivity)
  calc (∑' m : ℕ, brsLogBlockNorm d g m ^ q)
      = ((∑' m : ℕ, brsLogBlockNorm d g m ^ q) ^ (1 / q)) ^ q := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
    _ ≤ _ := ENNReal.rpow_le_rpow h2 hq0.le

/-- **The grouped shells collected.** -/
theorem tsum_brsOmega_le {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {q B : ℝ} (hq : 1 ≤ q)
    (hB : 0 < B)
    (hcov : ∀ l : ℕ, 1 ≤ l →
      ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (B ^ q * (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) *
          (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (d : ℝ)))))
    {g : ℝ → ℂ} (hg : Measurable g) :
    (∑' l : ℕ, ∫⁻ r in brsOmega E l, ENNReal.ofReal r ^ (d - 1) *
        brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q) ≤
      ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
          ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q * 2 ^ q *
        (ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
              ((Real.log 2) ^ (1 / (d : ℝ)) /
                ((2 : ℝ) ^ (1 / (d : ℝ)) - 1)) ^ (q - 1) *
              ((2 : ℝ) ^ (1 / (d : ℝ))) ^ q) *
            (ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) *
                ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) *
              (1 - ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹)⁻¹) *
            (∑' m : ℕ, brsLogBlockNorm d g m ^ q) +
          ENNReal.ofReal 7 *
            (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
              ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) * brsTopNorm d g) ^ q) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  set A : ENNReal := ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) with hA
  set T : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
    ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) * brsTopNorm d g with hT
  set S : ℕ → ENNReal := fun l =>
    ∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m with hS
  set D : ENNReal := ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) * A ^ q * 2 ^ q with hD
  set cst : ℝ := 7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
    ((Real.log 2) ^ (1 / (d : ℝ)) / ((2 : ℝ) ^ (1 / (d : ℝ)) - 1)) ^ (q - 1) *
    ((2 : ℝ) ^ (1 / (d : ℝ))) ^ q with hcst
  set M : ENNReal := ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) *
    ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) * (1 - ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹)⁻¹
    with hM
  set z : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹ with hz
  -- the per-shell bound, split into the block sum and the top piece
  have hper : ∀ l : ℕ,
      (∫⁻ r in brsOmega E l, ENNReal.ofReal r ^ (d - 1) *
        brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q) ≤
        D * (S l ^ q * volume (brsOmega E l) + T ^ q * volume (brsOmega E l)) := by
    intro l
    rcases Nat.eq_zero_or_pos l with hl | hl
    · rw [hl, brsOmega_zero]
      simp
    · refine le_trans (lintegral_brsOmega_le hd hE hEne hq0 hg hl) ?_
      have h1 : (A * (S l + T)) ^ q ≤ A ^ q * (2 ^ q * (S l ^ q + T ^ q)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
        exact mul_le_mul' le_rfl (ennreal_rpow_add_le hq0.le)
      calc ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) * (A * (S l + T)) ^ q *
            volume (brsOmega E l)
          ≤ ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
              (A ^ q * (2 ^ q * (S l ^ q + T ^ q))) * volume (brsOmega E l) :=
            mul_le_mul' (mul_le_mul' le_rfl h1) le_rfl
        _ = D * (S l ^ q * volume (brsOmega E l) +
              T ^ q * volume (brsOmega E l)) := by
            rw [hD]
            ring
  refine le_trans (ENNReal.tsum_le_tsum hper) ?_
  rw [ENNReal.tsum_mul_left, hD]
  refine mul_le_mul' le_rfl ?_
  rw [ENNReal.tsum_add]
  refine add_le_add ?_ ?_
  · -- the block sums
    have hshell : ∀ l : ℕ, S l ^ q * volume (brsOmega E l) ≤
        ENNReal.ofReal cst *
          (z ^ l * (∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m ^ q)) := by
      intro l
      rcases Nat.eq_zero_or_pos l with hl | hl
      · rw [hl, brsOmega_zero]
        simp
      · refine le_trans (logShell_term_le hd hE hEne hq hB hcov g hl) (le_of_eq ?_)
        rw [hcst, hz]
        ring
    refine le_trans (ENNReal.tsum_le_tsum hshell) ?_
    rw [ENNReal.tsum_mul_left]
    calc ENNReal.ofReal cst *
          (∑' l : ℕ, z ^ l *
            ∑' m : ℕ, brsLogWeight d l m * brsLogBlockNorm d g m ^ q)
        ≤ ENNReal.ofReal cst * (M * ∑' m : ℕ, brsLogBlockNorm d g m ^ q) := by
          refine mul_le_mul' le_rfl ?_
          rw [hz, hM]
          exact tsum_logShell_block_le hd g
      _ = ENNReal.ofReal cst * M * ∑' m : ℕ, brsLogBlockNorm d g m ^ q :=
          (mul_assoc _ _ _).symm
  · -- the top piece
    rw [ENNReal.tsum_mul_left]
    rw [mul_comm]
    exact mul_le_mul' (tsum_volume_brsOmega_le hE hEne) le_rfl

/-- **The endpoint bound with an explicit finite constant.** -/
theorem exists_endpoint_bound {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) (hEnull : volume (closure E) = 0)
    {q B : ℝ} (hpq : (d : ℝ) / ((d : ℝ) - 1) ≤ q) (hB : 0 < B)
    (hcov : ∀ l : ℕ, 1 ≤ l →
      ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (B ^ q * (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) *
          (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (d : ℝ))))) :
    ∃ Λ : ENNReal, Λ ≠ ⊤ ∧ ∀ g : ℝ → ℂ, Measurable g →
      (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
          brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q) ≤
        Λ * ((∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
          (((d : ℝ) - 1) / (d : ℝ))) ^ q := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hpd1 : (1 : ℝ) ≤ (d : ℝ) / ((d : ℝ) - 1) := by
    rw [le_div_iff₀ hd1]
    linarith
  have hq : (1 : ℝ) ≤ q := le_trans hpd1 hpq
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  refine ⟨ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
        (ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
          ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
            ((11 : ℝ) / 2) ^ (1 / (d : ℝ)))) ^ q * ENNReal.ofReal 7 +
      ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
          ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q * 2 ^ q *
        (ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
              ((Real.log 2) ^ (1 / (d : ℝ)) /
                ((2 : ℝ) ^ (1 / (d : ℝ)) - 1)) ^ (q - 1) *
              ((2 : ℝ) ^ (1 / (d : ℝ))) ^ q) *
            (ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) *
                ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) *
              (1 - ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹)⁻¹) +
          ENNReal.ofReal 7 *
            ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
              ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) ^ q), ?_, ?_⟩
  · -- finiteness of the constant
    have hy1 : 1 < (2 : ℝ) ^ (1 / (d : ℝ)) := one_lt_two_rpow_inv_d hd
    have hypos : (0 : ℝ) < (2 : ℝ) ^ (1 / (d : ℝ)) := by positivity
    have hzlt : ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹ < 1 := by
      rw [ENNReal.ofReal_lt_one]
      have h := (div_lt_one hypos).mpr hy1
      simpa [one_div] using h
    have hsub : (1 : ENNReal) - ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹ ≠ 0 := by
      intro h
      rw [tsub_eq_zero_iff_le] at h
      exact absurd hzlt (not_lt.mpr h)
    have hinv : ((1 : ENNReal) -
        ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr hsub
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
        ENNReal.ofReal_ne_top
      exact ENNReal.rpow_ne_top_of_nonneg hq0.le
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le
          ENNReal.ofReal_ne_top)) (ENNReal.rpow_ne_top_of_nonneg hq0.le
            (by simp))) ?_
      refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hinv)
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)
  · intro g hg
    have hNtop : brsTopNorm d g ≤
        (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
          (((d : ℝ) - 1) / (d : ℝ)) := brsTopNorm_le hd g
    have hblocks := tsum_brsLogBlockNorm_pow_le hd hpq g
    refine le_trans (lintegral_le_brsD_zero_add_tsum_brsOmega hE hEne hEnull hq0 g) ?_
    rw [add_mul]
    refine add_le_add ?_ ?_
    · -- the zeroth shell
      refine le_trans (lintegral_brsD_zero_le hd hE hEne hq0 hg) ?_
      have hstep : (ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
          (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
            ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) * brsTopNorm d g)) ^ q ≤
          (ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
            ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
              ((11 : ℝ) / 2) ^ (1 / (d : ℝ)))) ^ q *
            ((∫⁻ s in Ioi (0 : ℝ),
              (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
                (((d : ℝ) - 1) / (d : ℝ))) ^ q := by
        rw [← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
        exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hNtop hq0.le)
      calc ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
            (ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
              (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
                ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) * brsTopNorm d g)) ^ q *
            ENNReal.ofReal 7
          ≤ ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
              ((ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) *
                ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
                  ((11 : ℝ) / 2) ^ (1 / (d : ℝ)))) ^ q *
                ((∫⁻ s in Ioi (0 : ℝ),
                  (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
                    (((d : ℝ) - 1) / (d : ℝ))) ^ q) * ENNReal.ofReal 7 :=
            mul_le_mul' (mul_le_mul' le_rfl hstep) le_rfl
        _ = _ := by ring
    · -- the grouped shells
      refine le_trans (tsum_brsOmega_le hd hE hEne hq hB hcov hg) ?_
      have htop : ENNReal.ofReal 7 *
          (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
            ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) * brsTopNorm d g) ^ q ≤
          ENNReal.ofReal 7 *
            (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
              ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) ^ q *
              ((∫⁻ s in Ioi (0 : ℝ),
                (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
                  (((d : ℝ) - 1) / (d : ℝ))) ^ q) := by
        refine mul_le_mul' le_rfl ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
        exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hNtop hq0.le)
      calc ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
            ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q * 2 ^ q *
            (ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
                  ((Real.log 2) ^ (1 / (d : ℝ)) /
                    ((2 : ℝ) ^ (1 / (d : ℝ)) - 1)) ^ (q - 1) *
                  ((2 : ℝ) ^ (1 / (d : ℝ))) ^ q) *
                (ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) *
                    ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) *
                  (1 - ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹)⁻¹) *
                (∑' m : ℕ, brsLogBlockNorm d g m ^ q) +
              ENNReal.ofReal 7 *
                (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
                  ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) * brsTopNorm d g) ^ q)
          ≤ ENNReal.ofReal ((5 : ℝ) ^ (d - 1)) *
              ENNReal.ofReal ((2 / 3 : ℝ) ^ (1 - (d : ℝ))) ^ q * 2 ^ q *
              (ENNReal.ofReal (7 * B ^ q * (Real.log 2) ^ (-(q / (d : ℝ))) *
                    ((Real.log 2) ^ (1 / (d : ℝ)) /
                      ((2 : ℝ) ^ (1 / (d : ℝ)) - 1)) ^ (q - 1) *
                    ((2 : ℝ) ^ (1 / (d : ℝ))) ^ q) *
                  (ENNReal.ofReal ((Real.log 2) ^ (1 / (d : ℝ)) *
                      ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹) *
                    (1 - ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)))⁻¹)⁻¹) *
                  ((∫⁻ s in Ioi (0 : ℝ),
                    (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
                      (((d : ℝ) - 1) / (d : ℝ))) ^ q +
                ENNReal.ofReal 7 *
                  (ENNReal.ofReal ((2 : ℝ) ^ (1 / (d : ℝ)) *
                    ((11 : ℝ) / 2) ^ (1 / (d : ℝ))) ^ q *
                    ((∫⁻ s in Ioi (0 : ℝ),
                      (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
                        (((d : ℝ) - 1) / (d : ℝ))) ^ q)) :=
            mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hblocks) htop)
        _ = _ := by ring

/-- **Proposition 4.6.**  The endpoint estimate for the main term. -/
theorem prop46_brsMainMaximal {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) (hEnull : volume (closure E) = 0)
    {q B : ℝ} (hpq : (d : ℝ) / ((d : ℝ) - 1) ≤ q) (hB : 0 < B)
    (hcov : ∀ l : ℕ, 1 ≤ l →
      ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (B ^ q * (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) *
          (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (d : ℝ))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℂ, Measurable g →
      (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
          brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C *
          (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
            (((d : ℝ) - 1) / (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hpd1 : (1 : ℝ) ≤ (d : ℝ) / ((d : ℝ) - 1) := by
    rw [le_div_iff₀ hd1]
    linarith
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one (le_trans hpd1 hpq)
  obtain ⟨Λ, hΛ, hkey⟩ := exists_endpoint_bound hd hE hEne hEnull hpq hB hcov
  have hfin : Λ ^ (1 / q) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hΛ
  have htoReal : (0 : ℝ) ≤ (Λ ^ (1 / q)).toReal := ENNReal.toReal_nonneg
  refine ⟨(Λ ^ (1 / q)).toReal + 1, by linarith, fun g hg => ?_⟩
  calc (∫⁻ r, ENNReal.ofReal r ^ (d - 1) *
        brsMainMaximal d E ((d : ℝ) / ((d : ℝ) - 1)) g r ^ q) ^ (1 / q)
      ≤ (Λ * ((∫⁻ s in Ioi (0 : ℝ),
          (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
            (((d : ℝ) - 1) / (d : ℝ))) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (hkey g hg) (by positivity)
    _ = Λ ^ (1 / q) * (∫⁻ s in Ioi (0 : ℝ),
          (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
            (((d : ℝ) - 1) / (d : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
    _ ≤ ENNReal.ofReal ((Λ ^ (1 / q)).toReal + 1) *
          (∫⁻ s in Ioi (0 : ℝ),
            (ENNReal.ofReal ‖g s‖) ^ ((d : ℝ) / ((d : ℝ) - 1))) ^
              (((d : ℝ) - 1) / (d : ℝ)) := by
        refine mul_le_mul' ?_ le_rfl
        exact le_trans (le_of_eq (ENNReal.ofReal_toReal hfin).symm)
          (ENNReal.ofReal_le_ofReal (by linarith))

/-- The covering number decreases when the scale grows. -/
theorem intervalCoveringNumber_mono_scale {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    {δ δ' : ℝ} (hδ : 0 < δ) (hle : δ ≤ δ') :
    intervalCoveringNumber E δ' ≤ intervalCoveringNumber E δ := by
  obtain ⟨ι, hι, hcard⟩ := exists_intervalCover_card_eq_intervalCoveringNumber hE hδ
  rw [← hcard]
  exact intervalCoveringNumber_le_card (hι.mono_scale hle)

/-- A finite interval cover bounds the measure of the closure. -/
theorem volume_closure_le_coveringNumber_mul {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {δ : ℝ} (hδ : 0 < δ) :
    volume (closure E) ≤
      ENNReal.ofReal ((intervalCoveringNumber E δ : ℝ) * δ) := by
  obtain ⟨ι, hι, hcard⟩ := exists_intervalCover_card_eq_intervalCoveringNumber hE hδ
  have hclosed : IsClosed (⋃ a ∈ ι, Icc (a - δ / 2) (a + δ / 2)) := by
    refine Set.Finite.isClosed_biUnion ι.finite_toSet fun a _ => isClosed_Icc
  have hsub : closure E ⊆ ⋃ a ∈ ι, Icc (a - δ / 2) (a + δ / 2) :=
    closure_minimal hι hclosed
  calc volume (closure E) ≤ volume (⋃ a ∈ ι, Icc (a - δ / 2) (a + δ / 2)) :=
        measure_mono hsub
    _ ≤ ∑ a ∈ ι, volume (Icc (a - δ / 2) (a + δ / 2)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _a ∈ ι, ENNReal.ofReal δ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Real.volume_Icc]
        congr 1
        ring
    _ = (ι.card : ℕ) • ENNReal.ofReal δ := by rw [Finset.sum_const]
    _ = ENNReal.ofReal ((intervalCoveringNumber E δ : ℝ) * δ) := by
        rw [nsmul_eq_mul, hcard,
          ENNReal.ofReal_mul (Nat.cast_nonneg (intervalCoveringNumber E δ)),
          ENNReal.ofReal_natCast]

/-- **A set of upper Minkowski exponent `β < 1` has null closure.** -/
theorem volume_closure_eq_zero_of_minkowski {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1)
    (hM : HasUpperMinkowskiExponent E β) : volume (closure E) = 0 := by
  set ε : ℝ := (1 - β) / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    linarith
  obtain ⟨C, hC, hbound⟩ := intervalCoveringNumber_upper_bound_of_hasUpperMinkowskiExponent hM ε hεpos
  set γ : ℝ := 1 - (β + ε) with hγ
  have hγpos : 0 < γ := by
    rw [hγ, hε]
    linarith
  -- the scales
  have hδpos : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) + 1)) := by
    intro n
    positivity
  have hδlt : ∀ n : ℕ, (2 : ℝ) ^ (-((n : ℝ) + 1)) < 1 := by
    intro n
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hstep : ∀ n : ℕ, volume (closure E) ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ (-γ)) ^ (n + 1)) := by
    intro n
    have h1 := volume_closure_le_coveringNumber_mul hE (hδpos n)
    have h2 : ((intervalCoveringNumber E ((2 : ℝ) ^ (-((n : ℝ) + 1))) : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) + 1)) ≤ C * ((2 : ℝ) ^ (-γ)) ^ (n + 1) := by
      have hcov := hbound _ (hδpos n) (hδlt n)
      have hmul := mul_le_mul_of_nonneg_right hcov (hδpos n).le
      refine le_trans hmul (le_of_eq ?_)
      rw [two_rpow_rpow, two_rpow_pow]
      rw [show (2 : ℝ) ^ (-((n : ℝ) + 1)) = (2 : ℝ) ^ (-((n : ℝ) + 1)) from rfl]
      rw [mul_assoc, ← Real.rpow_add (by norm_num)]
      congr 1
      rw [hγ]
      push_cast
      ring
    exact le_trans h1 (ENNReal.ofReal_le_ofReal h2)
  -- the scales shrink geometrically
  have hratio : (0 : ℝ) ≤ (2 : ℝ) ^ (-γ) := by positivity
  have hratio1 : (2 : ℝ) ^ (-γ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo : Tendsto (fun n : ℕ => C * ((2 : ℝ) ^ (-γ)) ^ (n + 1)) atTop
      (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratio1
    have h2 : Tendsto (fun n : ℕ => ((2 : ℝ) ^ (-γ)) ^ (n + 1)) atTop (nhds 0) :=
      h.comp (Filter.tendsto_add_atTop_nat 1)
    simpa using h2.const_mul C
  have hlim : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (C * ((2 : ℝ) ^ (-γ)) ^ (n + 1))) atTop (nhds 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hgeo
    simpa [Function.comp_def] using this
  have hle : volume (closure E) ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hstep)
  exact le_antisymm hle (by simp)

/-- **(4.9).**  A Minkowski covering exponent `β` strictly below `q a + 1`
supplies the dyadic covering hypothesis of Proposition 4.5. -/
theorem exists_cov_bound_of_minkowski {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    {β : ℝ} (hβ0 : 0 ≤ β) (hM : HasUpperMinkowskiExponent E β) {q a : ℝ}
    (hq : 0 < q) (hlt : β < q * a + 1) :
    ∃ S : ℝ, 0 < S ∧ ∀ n : ℕ,
      ((intervalCoveringNumber E ((2 : ℝ) ^ (-(n : ℤ))) : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (S ^ q * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1))) := by
  set ε : ℝ := (q * a + 1 - β) / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    linarith
  have hsum : β + ε ≤ q * a + 1 := by
    rw [hε]
    linarith
  obtain ⟨C, hC, hbound⟩ :=
    intervalCoveringNumber_upper_bound_of_hasUpperMinkowskiExponent hM ε hεpos
  have hβε : 0 < β + ε := by linarith
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (β + ε) :=
    Real.one_le_rpow (by norm_num) hβε.le
  set A : ℝ := C * (2 : ℝ) ^ (β + ε) with hA
  have hApos : 0 < A := by
    rw [hA]
    positivity
  refine ⟨A ^ (1 / q), Real.rpow_pos_of_pos hApos _, fun n => ?_⟩
  have hAq : (A ^ (1 / q)) ^ q = A := by
    rw [← Real.rpow_mul hApos.le, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one]
  rw [hAq]
  -- the scale
  have hδ : (2 : ℝ) ^ (-(n : ℤ)) = (2 : ℝ) ^ (-(n : ℝ)) := two_zpow_eq_rpow n
  have hδpos : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℤ)) := by positivity
  have hkey : ((intervalCoveringNumber E ((2 : ℝ) ^ (-(n : ℤ))) : ℕ) : ℝ) ≤
      A * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1)) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- the scale `1`: pass to the scale `1/2`
      subst hn
      have hhalf : (2 : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-((0 : ℕ) : ℤ)) := by
        norm_num
      have hmono := intervalCoveringNumber_mono_scale hE
        (δ := (2 : ℝ) ^ (-(1 : ℝ))) (by positivity) hhalf
      have hcov := hbound ((2 : ℝ) ^ (-(1 : ℝ))) (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
      have hcast : ((intervalCoveringNumber E ((2 : ℝ) ^ (-((0 : ℕ) : ℤ))) : ℕ) : ℝ) ≤
          ((intervalCoveringNumber E ((2 : ℝ) ^ (-(1 : ℝ))) : ℕ) : ℝ) := by
        exact_mod_cast hmono
      have hval : C * ((2 : ℝ) ^ (-(1 : ℝ))) ^ (-(β + ε)) = A := by
        rw [hA, two_rpow_rpow, show (-(1 : ℝ)) * (-(β + ε)) = β + ε by ring]
      have hone : ((2 : ℝ) ^ (-((0 : ℕ) : ℤ))) ^ (-(q * a + 1)) = 1 := by
        norm_num
      rw [hone, mul_one]
      exact le_trans hcast (le_trans hcov (le_of_eq hval))
    · have hlt1 : (2 : ℝ) ^ (-(n : ℤ)) < 1 := by
        rw [hδ]
        refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      refine le_trans (hbound _ hδpos hlt1) ?_
      have hmono : ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(β + ε)) ≤
          ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1)) := by
        refine Real.rpow_le_rpow_of_exponent_ge hδpos hlt1.le ?_
        linarith
      calc C * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(β + ε))
          ≤ C * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1)) :=
            mul_le_mul_of_nonneg_left hmono hC.le
        _ ≤ A * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hA]
            nlinarith
  calc ((intervalCoveringNumber E ((2 : ℝ) ^ (-(n : ℤ))) : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((intervalCoveringNumber E ((2 : ℝ) ^ (-(n : ℤ))) : ℕ) : ℝ) := by
        rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (A * ((2 : ℝ) ^ (-(n : ℤ))) ^ (-(q * a + 1))) :=
        ENNReal.ofReal_le_ofReal hkey

/-- The primitive of a continuous function is continuous. -/
theorem continuous_primitive {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) :
    Continuous (fun x : ℝ => ∫ s in (0 : ℝ)..x, f₀ s) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hderiv := intervalIntegral.integral_hasStrictDerivAt_right
    (hf₀.intervalIntegrable (μ := volume) 0 x)
    (hf₀.stronglyMeasurableAtFilter _ _) hf₀.continuousAt
  exact hderiv.hasDerivAt.continuousAt

/-- An interval integral of a continuous function, in terms of its primitive. -/
theorem intervalIntegral_eq_primitive_sub {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀)
    (a b : ℝ) :
    (∫ s in a..b, f₀ s) =
      (∫ s in (0 : ℝ)..b, f₀ s) - ∫ s in (0 : ℝ)..a, f₀ s := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := a) (c := b)
    (hf₀.intervalIntegrable (μ := volume) 0 a)
    (hf₀.intervalIntegrable (μ := volume) a b)
  rw [← h]
  ring

/-- Joint continuity of the two-sided window integral `∫_{y-x}^{y+x}`. -/
theorem continuous_window_integral {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) :
    Continuous (fun z : ℝ × ℝ => ∫ s in (z.2 - z.1)..(z.2 + z.1), f₀ s) := by
  have hF := continuous_primitive hf₀
  have heq : (fun z : ℝ × ℝ => ∫ s in (z.2 - z.1)..(z.2 + z.1), f₀ s) =
      fun z : ℝ × ℝ => (∫ s in (0 : ℝ)..(z.2 + z.1), f₀ s) -
        ∫ s in (0 : ℝ)..(z.2 - z.1), f₀ s := by
    funext z
    exact intervalIntegral_eq_primitive_sub hf₀ _ _
  rw [heq]
  exact (hF.comp (continuous_snd.add continuous_fst)).sub
    (hF.comp (continuous_snd.sub continuous_fst))

/-- Rationals approximate from below inside `[1, ∞)`. -/
theorem exists_rat_le_close {t δ : ℝ} (ht : 1 ≤ t) (hδ : 0 < δ) :
    ∃ c : ℚ, 1 ≤ (c : ℝ) ∧ (c : ℝ) ≤ t ∧ t - (c : ℝ) < δ := by
  rcases eq_or_lt_of_le ht with h | h
  · refine ⟨1, by norm_num, by rw [← h]; norm_num, ?_⟩
    rw [← h]
    simpa using hδ
  · obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (max_lt h (by linarith : t - δ < t))
    have hmax1 : (1 : ℝ) ≤ (c : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hc1)
    have hmax2 : t - δ < (c : ℝ) := lt_of_le_of_lt (le_max_right (1 : ℝ) (t - δ)) hc1
    exact ⟨c, hmax1, hc2.le, by linarith⟩

/-- Rationals approximate from above inside `(-∞, 2]`. -/
theorem exists_rat_ge_close {t δ : ℝ} (ht : t ≤ 2) (hδ : 0 < δ) :
    ∃ c : ℚ, (c : ℝ) ≤ 2 ∧ t ≤ (c : ℝ) ∧ (c : ℝ) - t < δ := by
  rcases eq_or_lt_of_le ht with h | h
  · refine ⟨2, by norm_num, by rw [h]; norm_num, ?_⟩
    rw [h]
    simpa using hδ
  · obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (lt_min h (by linarith : t < t + δ))
    have hmin1 : (c : ℝ) ≤ 2 := le_of_lt (lt_of_lt_of_le hc2 (min_le_left _ _))
    have hmin2 : (c : ℝ) < t + δ := lt_of_lt_of_le hc2 (min_le_right (2 : ℝ) (t + δ))
    exact ⟨c, hmin1, hc1.le, by linarith⟩

/-- A sequence of rationals increasing to `t` from below. -/
theorem exists_rat_seq_le {t : ℝ} (ht : 1 ≤ t) :
    ∃ c : ℕ → ℚ, (∀ n, 1 ≤ ((c n : ℚ) : ℝ)) ∧ (∀ n, ((c n : ℚ) : ℝ) ≤ t) ∧
      Tendsto (fun n => ((c n : ℚ) : ℝ)) atTop (nhds t) := by
  choose c hc1 hc2 hc3 using fun n : ℕ =>
    exists_rat_le_close ht (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
  refine ⟨c, hc1, hc2, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : 1 / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hpos]
    have h1 : (1 / ε) < (n : ℝ) := lt_of_lt_of_le hN hnN
    rw [div_lt_iff₀ hε] at h1
    nlinarith
  have h1 := hc3 n
  have h2 := hc2 n
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

/-- A sequence of rationals decreasing to `t` from above. -/
theorem exists_rat_seq_ge {t : ℝ} (ht : t ≤ 2) :
    ∃ c : ℕ → ℚ, (∀ n, ((c n : ℚ) : ℝ) ≤ 2) ∧ (∀ n, t ≤ ((c n : ℚ) : ℝ)) ∧
      Tendsto (fun n => ((c n : ℚ) : ℝ)) atTop (nhds t) := by
  choose c hc1 hc2 hc3 using fun n : ℕ =>
    exists_rat_ge_close ht (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
  refine ⟨c, hc1, hc2, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : 1 / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hpos]
    have h1 : (1 / ε) < (n : ℝ) := lt_of_lt_of_le hN hnN
    rw [div_lt_iff₀ hε] at h1
    nlinarith
  have h1 := hc3 n
  have h2 := hc2 n
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

/-- **The first remainder is a countable supremum.**  The dilation supremum may
be taken over the rationals, because the window integral is continuous in the
dilation parameter. -/
theorem brsRemainderOne_eq_rat_iSup {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) (r : ℝ) :
    brsRemainderOne f₀ r =
      ⨆ c : ℚ, (if ((1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2) ∧ (c : ℝ) ≤ r / 2 then
        ENNReal.ofReal (((c : ℝ))⁻¹ *
          ‖∫ s in (r - (c : ℝ))..(r + (c : ℝ)), f₀ s‖) else 0) := by
  refine le_antisymm ?_ ?_
  · rw [brsRemainderOne]
    refine iSup₂_le fun t ht => ?_
    obtain ⟨⟨ht1, ht2⟩, ht3⟩ := ht
    obtain ⟨c, hc1, hc2, hctend⟩ := exists_rat_seq_le ht1
    have hGcont : ContinuousAt
        (fun u : ℝ => u⁻¹ * ‖∫ s in (r - u)..(r + u), f₀ s‖) t := by
      have hwin : ContinuousAt
          (fun u : ℝ => ∫ s in (r - u)..(r + u), f₀ s) t :=
        ((continuous_window_integral hf₀).comp
          (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => r))
            ).continuousAt
      exact (continuousAt_inv₀ (by linarith : t ≠ 0)).mul hwin.norm
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
        ((((c n : ℚ) : ℝ))⁻¹ *
          ‖∫ s in (r - ((c n : ℚ) : ℝ))..(r + ((c n : ℚ) : ℝ)), f₀ s‖)) atTop
        (nhds (ENNReal.ofReal (t⁻¹ * ‖∫ s in (r - t)..(r + t), f₀ s‖))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hGcont.tendsto.comp hctend)
    refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    refine le_iSup_of_le (c n) ?_
    rw [if_pos ⟨⟨hc1 n, le_trans (hc2 n) ht2⟩, le_trans (hc2 n) ht3⟩]
  · refine iSup_le fun c => ?_
    by_cases hc : ((1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2) ∧ (c : ℝ) ≤ r / 2
    · rw [if_pos hc, brsRemainderOne]
      exact le_iSup₂_of_le (c : ℝ) ⟨⟨hc.1.1, hc.1.2⟩, hc.2⟩ le_rfl
    · rw [if_neg hc]
      simp

/-- **The first remainder is measurable.** -/
theorem measurable_brsRemainderOne {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) :
    Measurable (brsRemainderOne f₀) := by
  have heq : brsRemainderOne f₀ = fun r : ℝ =>
      ⨆ c : ℚ, (if ((1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2) ∧ (c : ℝ) ≤ r / 2 then
        ENNReal.ofReal (((c : ℝ))⁻¹ *
          ‖∫ s in (r - (c : ℝ))..(r + (c : ℝ)), f₀ s‖) else 0) :=
    funext (brsRemainderOne_eq_rat_iSup hf₀)
  rw [heq]
  refine Measurable.iSup fun c => ?_
  have hfun : Measurable (fun r : ℝ => ENNReal.ofReal (((c : ℝ))⁻¹ *
      ‖∫ s in (r - (c : ℝ))..(r + (c : ℝ)), f₀ s‖)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine (continuous_const.mul ?_).measurable
    exact (((continuous_window_integral hf₀).comp
      (continuous_const.prodMk continuous_id)).norm)
  by_cases hc : (1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2
  · have hset : MeasurableSet {r : ℝ | (c : ℝ) ≤ r / 2} :=
      measurableSet_le measurable_const (measurable_id.div_const 2)
    have hrw : (fun r : ℝ =>
        (if ((1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2) ∧ (c : ℝ) ≤ r / 2 then
          ENNReal.ofReal (((c : ℝ))⁻¹ *
            ‖∫ s in (r - (c : ℝ))..(r + (c : ℝ)), f₀ s‖) else 0)) =
        Set.indicator {r : ℝ | (c : ℝ) ≤ r / 2}
          (fun r => ENNReal.ofReal (((c : ℝ))⁻¹ *
            ‖∫ s in (r - (c : ℝ))..(r + (c : ℝ)), f₀ s‖)) := by
      funext r
      by_cases hr : (c : ℝ) ≤ r / 2
      · rw [if_pos ⟨hc, hr⟩,
          Set.indicator_of_mem (show r ∈ {r : ℝ | (c : ℝ) ≤ r / 2} from hr)]
      · rw [if_neg (by tauto),
          Set.indicator_of_notMem (show r ∉ {r : ℝ | (c : ℝ) ≤ r / 2} from hr)]
    rw [hrw]
    exact hfun.indicator hset
  · have hrw : (fun r : ℝ =>
        (if ((1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2) ∧ (c : ℝ) ≤ r / 2 then
          ENNReal.ofReal (((c : ℝ))⁻¹ *
            ‖∫ s in (r - (c : ℝ))..(r + (c : ℝ)), f₀ s‖) else 0)) =
        fun _ : ℝ => (0 : ENNReal) := by
      funext r
      rw [if_neg (by tauto)]
    rw [hrw]
    exact measurable_const

/-- **The second remainder is a countable supremum.** -/
theorem brsRemainderTwo_eq_rat_iSup {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) (r : ℝ) :
    brsRemainderTwo f₀ r =
      ⨆ c : ℚ, (if ((1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2) ∧ 3 * r / 2 ≤ (c : ℝ) then
        ENNReal.ofReal (r⁻¹ *
          ‖∫ s in ((c : ℝ) - r)..((c : ℝ) + r), f₀ s‖) else 0) := by
  refine le_antisymm ?_ ?_
  · rw [brsRemainderTwo]
    refine iSup₂_le fun t ht => ?_
    obtain ⟨⟨ht1, ht2⟩, ht3⟩ := ht
    obtain ⟨c, hc1, hc2, hctend⟩ := exists_rat_seq_ge ht2
    have hGcont : ContinuousAt
        (fun u : ℝ => r⁻¹ * ‖∫ s in (u - r)..(u + r), f₀ s‖) t := by
      have hwin : ContinuousAt
          (fun u : ℝ => ∫ s in (u - r)..(u + r), f₀ s) t :=
        ((continuous_window_integral hf₀).comp
          ((continuous_const : Continuous fun _ : ℝ => r).prodMk continuous_id)
            ).continuousAt
      exact continuousAt_const.mul hwin.norm
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
        (r⁻¹ * ‖∫ s in (((c n : ℚ) : ℝ) - r)..(((c n : ℚ) : ℝ) + r), f₀ s‖))
        atTop (nhds (ENNReal.ofReal (r⁻¹ * ‖∫ s in (t - r)..(t + r), f₀ s‖)))  :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hGcont.tendsto.comp hctend)
    refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    refine le_iSup_of_le (c n) ?_
    rw [if_pos ⟨⟨le_trans ht1 (hc2 n), hc1 n⟩, le_trans ht3 (hc2 n)⟩]
  · refine iSup_le fun c => ?_
    by_cases hc : ((1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2) ∧ 3 * r / 2 ≤ (c : ℝ)
    · rw [if_pos hc, brsRemainderTwo]
      exact le_iSup₂_of_le (c : ℝ) ⟨⟨hc.1.1, hc.1.2⟩, hc.2⟩ le_rfl
    · rw [if_neg hc]
      simp

/-- **The second remainder is measurable.** -/
theorem measurable_brsRemainderTwo {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) :
    Measurable (brsRemainderTwo f₀) := by
  have heq : brsRemainderTwo f₀ = fun r : ℝ =>
      ⨆ c : ℚ, (if ((1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2) ∧ 3 * r / 2 ≤ (c : ℝ) then
        ENNReal.ofReal (r⁻¹ *
          ‖∫ s in ((c : ℝ) - r)..((c : ℝ) + r), f₀ s‖) else 0) :=
    funext (brsRemainderTwo_eq_rat_iSup hf₀)
  rw [heq]
  refine Measurable.iSup fun c => ?_
  have hfun : Measurable (fun r : ℝ => ENNReal.ofReal (r⁻¹ *
      ‖∫ s in ((c : ℝ) - r)..((c : ℝ) + r), f₀ s‖)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine measurable_inv.mul ?_
    exact (((continuous_window_integral hf₀).comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ =>
        (c : ℝ)))).norm).measurable
  by_cases hc : (1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2
  · have hset : MeasurableSet {r : ℝ | 3 * r / 2 ≤ (c : ℝ)} :=
      measurableSet_le ((measurable_const.mul measurable_id).div_const 2)
        measurable_const
    have hrw : (fun r : ℝ =>
        (if ((1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2) ∧ 3 * r / 2 ≤ (c : ℝ) then
          ENNReal.ofReal (r⁻¹ *
            ‖∫ s in ((c : ℝ) - r)..((c : ℝ) + r), f₀ s‖) else 0)) =
        Set.indicator {r : ℝ | 3 * r / 2 ≤ (c : ℝ)}
          (fun r => ENNReal.ofReal (r⁻¹ *
            ‖∫ s in ((c : ℝ) - r)..((c : ℝ) + r), f₀ s‖)) := by
      funext r
      by_cases hr : 3 * r / 2 ≤ (c : ℝ)
      · rw [if_pos ⟨hc, hr⟩,
          Set.indicator_of_mem (show r ∈ {r : ℝ | 3 * r / 2 ≤ (c : ℝ)} from hr)]
      · rw [if_neg (by tauto),
          Set.indicator_of_notMem
            (show r ∉ {r : ℝ | 3 * r / 2 ≤ (c : ℝ)} from hr)]
    rw [hrw]
    exact hfun.indicator hset
  · have hrw : (fun r : ℝ =>
        (if ((1 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2) ∧ 3 * r / 2 ≤ (c : ℝ) then
          ENNReal.ofReal (r⁻¹ *
            ‖∫ s in ((c : ℝ) - r)..((c : ℝ) + r), f₀ s‖) else 0)) =
        fun _ : ℝ => (0 : ENNReal) := by
      funext r
      rw [if_neg (by tauto)]
    rw [hrw]
    exact measurable_const

/-- The radial weight kills the negative half-line, so weighted integrals over
`ℝ` and over `(0,∞)` agree. -/
theorem lintegral_radial_weight_Ioi {D : ℕ} (hD : 2 ≤ D) (h : ℝ → ENNReal) :
    (∫⁻ s, ENNReal.ofReal s ^ (D - 1) * h s) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal s ^ (D - 1) * h s := by
  rw [← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs]
    have hs0 : s ≤ 0 := by
      simp only [mem_Ioi, not_lt] at hs
      exact hs
    rw [ENNReal.ofReal_eq_zero.mpr hs0, zero_pow (by omega : D - 1 ≠ 0), zero_mul]

/-- **The substitution identity for the `L^p` norms.** -/
theorem lintegral_profileSub_eq {D : ℕ} (hD : 2 ≤ D) {p : ℝ} (hp : 0 < p)
    (f₀ : ℝ → ℂ) :
    (∫⁻ s in Ioi (0 : ℝ),
        (ENNReal.ofReal ‖brsProfileSub D p (absProfile f₀) s‖) ^ p) =
      ∫⁻ s, ENNReal.ofReal s ^ (D - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p := by
  rw [lintegral_radial_weight_Ioi hD]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [enorm_brsProfileSub_rpow hD hp _ (le_of_lt hs), norm_absProfile]

/-- Three terms: the `q`-th power of a triple sum. -/
theorem ennreal_rpow_add_three_le {X Y Z : ENNReal} {q : ℝ} (hq : 1 ≤ q) :
    (X + Y + Z) ^ q ≤ 4 ^ q * (X ^ q + Y ^ q + Z ^ q) := by
  have hq0 : (0 : ℝ) ≤ q := le_trans zero_le_one hq
  have h2 : (2 : ENNReal) ^ q * (2 : ENNReal) ^ q = (4 : ENNReal) ^ q := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0]
    norm_num
  have hone : (1 : ENNReal) ≤ (2 : ENNReal) ^ q := by
    calc (1 : ENNReal) = (1 : ENNReal) ^ q := by rw [ENNReal.one_rpow]
      _ ≤ (2 : ENNReal) ^ q := ENNReal.rpow_le_rpow (by norm_num) hq0
  calc (X + Y + Z) ^ q ≤ 2 ^ q * ((X + Y) ^ q + Z ^ q) :=
        ennreal_rpow_add_le hq0
    _ ≤ 2 ^ q * (2 ^ q * (X ^ q + Y ^ q) + Z ^ q) :=
        mul_le_mul' le_rfl (add_le_add (ennreal_rpow_add_le hq0) le_rfl)
    _ ≤ 2 ^ q * (2 ^ q * (X ^ q + Y ^ q) + 2 ^ q * Z ^ q) := by
        refine mul_le_mul' le_rfl (add_le_add le_rfl ?_)
        calc Z ^ q = 1 * Z ^ q := (one_mul _).symm
          _ ≤ 2 ^ q * Z ^ q := mul_le_mul' hone le_rfl
    _ = 4 ^ q * (X ^ q + Y ^ q + Z ^ q) := by
        rw [← mul_add, ← mul_assoc, h2, add_assoc]

/-- Three terms: the `ℓ^q` norm is at most three times the `ℓ^1` norm. -/
theorem ennreal_rpow_sum_three_le {a b c : ENNReal} {q : ℝ} (hq : 1 ≤ q) :
    (a ^ q + b ^ q + c ^ q) ^ (1 / q) ≤ 3 * (a + b + c) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hmono : a ^ q + b ^ q + c ^ q ≤ 3 * (a + b + c) ^ q := by
    have ha : a ^ q ≤ (a + b + c) ^ q :=
      ENNReal.rpow_le_rpow (le_trans le_self_add le_self_add) hq0.le
    have hb : b ^ q ≤ (a + b + c) ^ q :=
      ENNReal.rpow_le_rpow (le_trans le_add_self le_self_add) hq0.le
    have hc : c ^ q ≤ (a + b + c) ^ q :=
      ENNReal.rpow_le_rpow le_add_self hq0.le
    calc a ^ q + b ^ q + c ^ q ≤ (a + b + c) ^ q + (a + b + c) ^ q +
          (a + b + c) ^ q := add_le_add (add_le_add ha hb) hc
      _ = 3 * (a + b + c) ^ q := by ring
  calc (a ^ q + b ^ q + c ^ q) ^ (1 / q)
      ≤ (3 * (a + b + c) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hmono (by positivity)
    _ = 3 ^ (1 / q) * (a + b + c) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
    _ ≤ 3 * (a + b + c) := by
        refine mul_le_mul' ?_ le_rfl
        calc (3 : ENNReal) ^ (1 / q) ≤ (3 : ENNReal) ^ (1 : ℝ) := by
              refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
              rw [div_le_one hq0]
              exact hq
          _ = 3 := ENNReal.rpow_one 3

/-- **The three pieces of Lemma 4.1 combined.** -/
theorem exists_combined_bound {D : ℕ} (hD : 2 ≤ D) {E : Set ℝ}
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hqpd : q < p * D)
    (hmain : ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℂ, Measurable g →
      (∫⁻ r, ENNReal.ofReal r ^ (D - 1) * brsMainMaximal D E p g r ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C *
          (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f₀ : ℝ → ℂ, Continuous f₀ →
      (∫⁻ r, ENNReal.ofReal r ^ (D - 1) *
          (brsMainMaximal D E p (brsProfileSub D p (absProfile f₀)) r +
            brsRemainderOne (absProfile f₀) r +
            brsRemainderTwo (absProfile f₀) r) ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C *
          (∫⁻ s, ENNReal.ofReal s ^ (D - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p) ^
            (1 / p) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hq : (1 : ℝ) ≤ q := le_trans hp hpq
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  obtain ⟨C₁, hC₁, hmainb⟩ := hmain
  obtain ⟨C₃, hC₃, hR₂⟩ := prop43_brsRemainderTwo hD hp hq0 hqpd
  set C₂ : ℝ := ((4 : ℝ) ^ ((1 - 1 / p) * (q - p)) *
    ((2 : ℝ) ^ (D - 1) * (4 : ℝ) ^ p)) ^ (1 / q) with hC₂
  have hC₂pos : 0 < C₂ := by
    rw [hC₂]
    have h1 : (0 : ℝ) < (4 : ℝ) ^ ((1 - 1 / p) * (q - p)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < (4 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine ⟨12 * (C₁ + C₂ + C₃), by positivity, fun f₀ hf₀ => ?_⟩
  have hcont : Continuous (absProfile f₀) := continuous_absProfile hf₀
  set Np : ENNReal :=
    (∫⁻ s, ENNReal.ofReal s ^ (D - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p) ^ (1 / p)
    with hNp
  set X : ℝ → ENNReal := fun r =>
    brsMainMaximal D E p (brsProfileSub D p (absProfile f₀)) r with hX
  set Y : ℝ → ENNReal := fun r => brsRemainderOne (absProfile f₀) r with hY
  set Z : ℝ → ENNReal := fun r => brsRemainderTwo (absProfile f₀) r with hZ
  set w : ℝ → ENNReal := fun r => ENNReal.ofReal r ^ (D - 1) with hw
  have hwmeas : Measurable w := by
    rw [hw]
    exact ENNReal.measurable_ofReal.pow_const _
  have hYmeas : Measurable (fun r => w r * Y r ^ q) := by
    refine hwmeas.mul ?_
    rw [hY]
    exact ENNReal.continuous_rpow_const.measurable.comp
      (measurable_brsRemainderOne hcont)
  have hZmeas : Measurable (fun r => w r * Z r ^ q) := by
    refine hwmeas.mul ?_
    rw [hZ]
    exact ENNReal.continuous_rpow_const.measurable.comp
      (measurable_brsRemainderTwo hcont)
  -- the three individual bounds
  set a : ENNReal := (∫⁻ r, w r * X r ^ q) ^ (1 / q) with ha
  set b : ENNReal := (∫⁻ r, w r * Y r ^ q) ^ (1 / q) with hb
  set c : ENNReal := (∫⁻ r, w r * Z r ^ q) ^ (1 / q) with hc
  have hbX : a ≤ ENNReal.ofReal C₁ * Np := by
    have hmeas : Measurable (brsProfileSub D p (absProfile f₀)) :=
      (continuous_brsProfileSub hD hp0 hcont).measurable
    refine le_trans (hmainb _ hmeas) ?_
    rw [hNp, lintegral_profileSub_eq hD hp0]
  have hbY : b ≤ ENNReal.ofReal C₂ * Np := by
    rw [hb, hC₂, hNp, hw, hY]
    exact prop42_brsRemainderOne hD hp hpq hf₀
  have hbZ : c ≤ ENNReal.ofReal C₃ * Np := by
    rw [hc, hNp, hw, hZ]
    exact hR₂ f₀ hf₀
  have haq : a ^ q = ∫⁻ r, w r * X r ^ q := by
    rw [ha, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
  have hbq : b ^ q = ∫⁻ r, w r * Y r ^ q := by
    rw [hb, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
  have hcq : c ^ q = ∫⁻ r, w r * Z r ^ q := by
    rw [hc, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
  have hpoint : ∀ r : ℝ, w r * (X r + Y r + Z r) ^ q ≤
      4 ^ q * (w r * X r ^ q + w r * Y r ^ q + w r * Z r ^ q) := by
    intro r
    calc w r * (X r + Y r + Z r) ^ q
        ≤ w r * (4 ^ q * (X r ^ q + Y r ^ q + Z r ^ q)) :=
          mul_le_mul' le_rfl (ennreal_rpow_add_three_le hq)
      _ = 4 ^ q * (w r * X r ^ q + w r * Y r ^ q + w r * Z r ^ q) := by ring
  have h4top : (4 : ENNReal) ^ q ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hq0.le (by norm_num)
  have hsplit : (∫⁻ r, 4 ^ q * (w r * X r ^ q + w r * Y r ^ q + w r * Z r ^ q)) =
      4 ^ q * (a ^ q + b ^ q + c ^ q) := by
    rw [lintegral_const_mul' _ _ h4top,
      lintegral_add_right' _ hZmeas.aemeasurable,
      lintegral_add_right' _ hYmeas.aemeasurable, haq, hbq, hcq]
  calc (∫⁻ r, w r * (X r + Y r + Z r) ^ q) ^ (1 / q)
      ≤ (∫⁻ r, 4 ^ q * (w r * X r ^ q + w r * Y r ^ q + w r * Z r ^ q)) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpoint) (by positivity)
    _ = (4 ^ q * (a ^ q + b ^ q + c ^ q)) ^ (1 / q) := by rw [hsplit]
    _ = 4 * (a ^ q + b ^ q + c ^ q) ^ (1 / q) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
    _ ≤ 4 * (3 * (a + b + c)) :=
        mul_le_mul' le_rfl (ennreal_rpow_sum_three_le hq)
    _ ≤ 4 * (3 * (ENNReal.ofReal C₁ * Np + ENNReal.ofReal C₂ * Np +
          ENNReal.ofReal C₃ * Np)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl
          (add_le_add (add_le_add hbX hbY) hbZ))
    _ = ENNReal.ofReal (12 * (C₁ + C₂ + C₃)) * Np := by
        rw [ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_add (by positivity) hC₃.le,
          ENNReal.ofReal_add hC₁.le hC₂pos.le]
        rw [show ENNReal.ofReal (12 : ℝ) = (12 : ENNReal) by
          rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num,
            ENNReal.ofReal_natCast]
          norm_num]
        ring

/-- The integrand of the main term after the substitution is continuous,
because `D ≥ 2` makes the power nonnegative. -/
theorem continuous_mainIntegrand {D : ℕ} (hD : 2 ≤ D) {f₀ : ℝ → ℂ}
    (hf₀ : Continuous f₀) :
    Continuous (fun s : ℝ => ((s ^ ((D : ℝ) - 2) : ℝ) : ℂ) * absProfile f₀ s) := by
  have hDR : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have h1 : Continuous (fun s : ℝ => (s ^ ((D : ℝ) - 2) : ℝ)) :=
    continuous_rpow_const_of_nonneg (by linarith)
  exact (Complex.continuous_ofReal.comp h1).mul (continuous_absProfile hf₀)

/-- On a window inside `[0, ∞)` the substituted integrand of the main term may
be replaced by the continuous one. -/
theorem mainMaximal_window_eq {D : ℕ} {p : ℝ} (hp : 0 < p) (f₀ : ℝ → ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ s in a..b, ((s ^ (((D : ℝ) - 1) * (1 - 1 / p) - 1) : ℝ) : ℂ) *
        brsProfileSub D p (absProfile f₀) s) =
      ∫ s in a..b, ((s ^ ((D : ℝ) - 2) : ℝ) : ℂ) * absProfile f₀ s := by
  refine intervalIntegral.integral_congr_ae
    (Filter.Eventually.of_forall fun s hs => ?_)
  have hmin : (0 : ℝ) ≤ min a b := le_min ha hb
  have hs0 : 0 < s := lt_of_le_of_lt hmin (Set.mem_Ioc.mp hs).1
  exact brsMainMaximal_integrand hp (absProfile f₀) hs0

/-- **The main term is measurable.**  For a continuous profile the window
integral is continuous in the dilation parameter, so the supremum may be taken
over a countable dense subset of `E`. -/
theorem measurable_brsMainMaximal {D : ℕ} (hD : 2 ≤ D) (E : Set ℝ) {p : ℝ}
    (hp : 0 < p) {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) :
    Measurable (fun r : ℝ =>
      brsMainMaximal D E p (brsProfileSub D p (absProfile f₀)) r) := by
  classical
  -- the continuous primitive of the substituted integrand
  set h : ℝ → ℂ := fun s => ((s ^ ((D : ℝ) - 2) : ℝ) : ℂ) * absProfile f₀ s with hh
  have hhcont : Continuous h := by
    rw [hh]
    exact continuous_mainIntegrand hD hf₀
  set H : ℝ → ℂ := fun x => ∫ s in (0 : ℝ)..x, h s with hH
  have hHcont : Continuous H := by
    rw [hH]
    exact continuous_primitive hhcont
  set Ψ : ℝ → ℝ → ENNReal := fun t r =>
    ENNReal.ofReal (r ^ (1 - (D : ℝ)) * ‖H (r + t) - H |r - t|‖) with hΨ
  -- the sup terms agree with `Ψ` on the admissible range
  have hterm : ∀ t r : ℝ, r / 2 < t → t < 3 * r / 2 →
      ENNReal.ofReal (r ^ (1 - (D : ℝ)) *
        ‖∫ s in |r - t|..(r + t),
          ((s ^ ((((D : ℝ) - 1) * (1 - 1 / p) - 1)) : ℝ) : ℂ) *
            brsProfileSub D p (absProfile f₀) s‖) = Ψ t r := by
    intro t r ht1 ht2
    have hr : 0 < r := by linarith
    have ht : 0 < t := by linarith
    rw [hΨ]
    congr 2
    rw [mainMaximal_window_eq hp f₀ (abs_nonneg _) (by linarith : (0:ℝ) ≤ r + t),
      intervalIntegral_eq_primitive_sub hhcont]
  -- a countable dense subset of `E`
  obtain ⟨T, hTE, hTcount, hTdense⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace E).exists_countable_dense_subset
  haveI : Countable (↥T) := hTcount.to_subtype
  have hkey : ∀ r : ℝ,
      brsMainMaximal D E p (brsProfileSub D p (absProfile f₀)) r =
        ⨆ t : ↥T, (if r / 2 < (t : ℝ) ∧ (t : ℝ) < 3 * r / 2 then Ψ (t : ℝ) r
          else 0) := by
    intro r
    refine le_antisymm ?_ ?_
    · rw [brsMainMaximal]
      refine iSup₂_le fun t ht => ?_
      obtain ⟨htE, ht1, ht2⟩ := ht
      have hr : 0 < r := by
        have := ht1
        have := ht2
        linarith
      rw [hterm t r ht1 ht2]
      -- approximate `t` by points of `T`
      have hmem : t ∈ closure T := hTdense htE
      obtain ⟨u, huT, hutend⟩ := mem_closure_iff_seq_limit.mp hmem
      have hΨcont : ContinuousAt (fun v : ℝ => Ψ v r) t := by
        rw [hΨ]
        refine (ENNReal.continuous_ofReal.comp ?_).continuousAt
        refine continuous_const.mul ?_
        exact ((hHcont.comp (continuous_const.add continuous_id)).sub
          (hHcont.comp (continuous_abs.comp
            (continuous_const.sub continuous_id)))).norm
      have hlim : Tendsto (fun n : ℕ => Ψ (u n) r) atTop (nhds (Ψ t r)) :=
        hΨcont.tendsto.comp hutend
      have hev : ∀ᶠ n in atTop, Ψ (u n) r ≤
          ⨆ t : ↥T, (if r / 2 < (t : ℝ) ∧ (t : ℝ) < 3 * r / 2 then Ψ (t : ℝ) r
            else 0) := by
        have h1 : ∀ᶠ n in atTop, r / 2 < u n ∧ u n < 3 * r / 2 := by
          have hopen : IsOpen (Ioo (r / 2) (3 * r / 2)) := isOpen_Ioo
          have := hutend.eventually (hopen.mem_nhds (by exact ⟨ht1, ht2⟩))
          filter_upwards [this] with n hn
          exact ⟨hn.1, hn.2⟩
        filter_upwards [h1] with n hn
        refine le_iSup_of_le ⟨u n, huT n⟩ ?_
        rw [if_pos hn]
      exact le_of_tendsto hlim hev
    · refine iSup_le fun t => ?_
      by_cases hc : r / 2 < (t : ℝ) ∧ (t : ℝ) < 3 * r / 2
      · rw [if_pos hc, ← hterm (t : ℝ) r hc.1 hc.2, brsMainMaximal]
        exact le_iSup₂_of_le (t : ℝ) ⟨hTE t.2, hc.1, hc.2⟩ le_rfl
      · rw [if_neg hc]
        simp
  rw [funext hkey]
  refine Measurable.iSup fun t => ?_
  have hΨmeas : Measurable (fun r : ℝ => Ψ (t : ℝ) r) := by
    rw [hΨ]
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.mul ?_ ?_
    · exact (by fun_prop : Measurable fun r : ℝ => r ^ (1 - (D : ℝ)))
    · refine (Continuous.measurable ?_)
      exact ((hHcont.comp (continuous_id.add continuous_const)).sub
        (hHcont.comp (continuous_abs.comp
          (continuous_id.sub continuous_const)))).norm
  have hset : MeasurableSet {r : ℝ | r / 2 < (t : ℝ) ∧ (t : ℝ) < 3 * r / 2} := by
    have h1 : MeasurableSet {r : ℝ | r / 2 < (t : ℝ)} :=
      measurableSet_lt (measurable_id.div_const 2) measurable_const
    have h2 : MeasurableSet {r : ℝ | (t : ℝ) < 3 * r / 2} :=
      measurableSet_lt measurable_const
        ((measurable_const.mul measurable_id).div_const 2)
    exact h1.inter h2
  have hrw : (fun r : ℝ =>
      (if r / 2 < (t : ℝ) ∧ (t : ℝ) < 3 * r / 2 then Ψ (t : ℝ) r else 0)) =
      Set.indicator {r : ℝ | r / 2 < (t : ℝ) ∧ (t : ℝ) < 3 * r / 2}
        (fun r => Ψ (t : ℝ) r) := by
    funext r
    by_cases hr : r / 2 < (t : ℝ) ∧ (t : ℝ) < 3 * r / 2
    · rw [if_pos hr, Set.indicator_of_mem
        (show r ∈ {r : ℝ | r / 2 < (t : ℝ) ∧ (t : ℝ) < 3 * r / 2} from hr)]
    · rw [if_neg hr, Set.indicator_of_notMem
        (show r ∉ {r : ℝ | r / 2 < (t : ℝ) ∧ (t : ℝ) < 3 * r / 2} from hr)]
  rw [hrw]
  exact hΨmeas.indicator hset

/-- The radial lift of a profile is norm-radial. -/
theorem isNormRadial_lift (D : ℕ) (f₀ : ℝ → ℂ) :
    _root_.Auto.RadialFourierTransform.IsNormRadial
      (fun x : Euclidean D => f₀ ‖x‖) := by
  intro x y hxy
  simp only [hxy]

/-- **The `L^p` norm of a radial lift in polar coordinates.** -/
theorem eLpNorm_lift_eq {D : ℕ} (hD : 2 ≤ D) {p : ℝ} (hp : 0 < p) {f₀ : ℝ → ℂ}
    (hf₀ : Continuous f₀) :
    eLpNorm (fun x : Euclidean D => f₀ ‖x‖) (ENNReal.ofReal p) volume =
      ENNReal.ofReal (surfaceMass D) ^ (1 / p) *
        (∫⁻ s, ENNReal.ofReal s ^ (D - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p) ^
          (1 / p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  set G : ℝ → ENNReal := fun r => (ENNReal.ofReal ‖f₀ r‖) ^ p with hG
  have hGmeas : Measurable G := by
    rw [hG]
    exact ENNReal.continuous_rpow_const.measurable.comp
      (hf₀.norm.measurable.ennreal_ofReal)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, ENNReal.toReal_ofReal hp.le]
  have hcongr : (∫⁻ x : Euclidean D, ‖f₀ ‖x‖‖ₑ ^ p) = ∫⁻ x : Euclidean D, G ‖x‖ := by
    refine lintegral_congr fun x => ?_
    rw [hG]
    simp only []
    rw [← ofReal_norm (f₀ ‖x‖)]
  rw [hcongr, lintegral_euclidean_radial (by omega : 0 < D) G hGmeas,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p),
    ← lintegral_radial_weight_Ioi hD G, hG]

/-- **The radial strong bound for continuous profiles.**  Lemma 4.1 plus the
propositions of §4, transported to the ambient Euclidean norm. -/
theorem eLpNorm_M_lift_le {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hqpd : q < p * ((d + 1 : ℕ) : ℝ))
    (hmain : ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℂ, Measurable g →
      (∫⁻ r, ENNReal.ofReal r ^ (d + 1 - 1) *
          brsMainMaximal (d + 1) E p g r ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C *
          (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f₀ : ℝ → ℂ, Continuous f₀ →
      eLpNorm (M E (fun y : Euclidean (d + 1) => f₀ ‖y‖)) (ENNReal.ofReal q)
          volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun x : Euclidean (d + 1) => f₀ ‖x‖) (ENNReal.ofReal p)
            volume := by
  have hD : 2 ≤ d + 1 := by omega
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hq : (1 : ℝ) ≤ q := le_trans hp hpq
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hsm : 0 < surfaceMass (d + 1) := surfaceMass_pos (by omega)
  obtain ⟨C₀, hC₀, hdecomp⟩ := le_brsDecomposition hd hE hp0
  obtain ⟨K, hK, hcomb⟩ := exists_combined_bound hD (E := E) hp hpq hqpd hmain
  refine ⟨C₀ * K * surfaceMass (d + 1) ^ (1 / q - 1 / p), ?_, fun f₀ hf₀ => ?_⟩
  · have h1 : (0 : ℝ) < surfaceMass (d + 1) ^ (1 / q - 1 / p) :=
      Real.rpow_pos_of_pos hsm _
    positivity
  set S : ℝ → ENNReal := fun r =>
    brsMainMaximal (d + 1) E p (brsProfileSub (d + 1) p (absProfile f₀)) r +
      brsRemainderOne (absProfile f₀) r +
      brsRemainderTwo (absProfile f₀) r with hS
  set Np : ENNReal :=
    (∫⁻ s, ENNReal.ofReal s ^ (d + 1 - 1) * (ENNReal.ofReal ‖f₀ s‖) ^ p) ^ (1 / p)
    with hNp
  have hcont : Continuous (absProfile f₀) := continuous_absProfile hf₀
  have hSmeas : Measurable (fun r : ℝ => S r ^ q) := by
    refine ENNReal.continuous_rpow_const.measurable.comp ?_
    rw [hS]
    exact ((measurable_brsMainMaximal hD E hp0 hf₀).add
      (measurable_brsRemainderOne hcont)).add (measurable_brsRemainderTwo hcont)
  -- the pointwise decomposition, away from the origin
  have hae : ∀ᵐ x : Euclidean (d + 1) ∂volume,
      ‖M E (fun y : Euclidean (d + 1) => f₀ ‖y‖) x‖ₑ ^ q ≤
        (ENNReal.ofReal C₀ * S ‖x‖) ^ q := by
    have hnull : ∀ᵐ x : Euclidean (d + 1) ∂volume, x ≠ 0 := by
      have h : volume ({(0 : Euclidean (d + 1))} : Set (Euclidean (d + 1))) = 0 := by
        simp
      rw [← compl_mem_ae_iff] at h
      filter_upwards [h] with x hx
      simpa using hx
    filter_upwards [hnull] with x hx
    refine ENNReal.rpow_le_rpow ?_ hq0.le
    have hpt := hdecomp f₀ hf₀ x hx
    rw [hS]
    simpa using hpt
  -- the radial integral
  have hbound : (∫⁻ x : Euclidean (d + 1),
      ‖M E (fun y : Euclidean (d + 1) => f₀ ‖y‖) x‖ₑ ^ q) ≤
      ENNReal.ofReal C₀ ^ q * ENNReal.ofReal (surfaceMass (d + 1)) *
        (ENNReal.ofReal K * Np) ^ q := by
    have hstep1 : (∫⁻ x : Euclidean (d + 1),
        ‖M E (fun y : Euclidean (d + 1) => f₀ ‖y‖) x‖ₑ ^ q) ≤
        ∫⁻ x : Euclidean (d + 1), ENNReal.ofReal C₀ ^ q * (S ‖x‖) ^ q := by
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with x hx
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
      exact hx
    have hstep2 : (∫⁻ x : Euclidean (d + 1),
        ENNReal.ofReal C₀ ^ q * (S ‖x‖) ^ q) =
        ENNReal.ofReal C₀ ^ q * (ENNReal.ofReal (surfaceMass (d + 1)) *
          ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (d + 1 - 1) * S r ^ q) := by
      rw [lintegral_const_mul' _ _
        (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top),
        lintegral_euclidean_radial (by omega : 0 < d + 1)
          (fun r => S r ^ q) hSmeas]
    have hstep3 : (∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal r ^ (d + 1 - 1) * S r ^ q) ≤ (ENNReal.ofReal K * Np) ^ q := by
      have hfull : (∫⁻ r in Ioi (0 : ℝ),
          ENNReal.ofReal r ^ (d + 1 - 1) * S r ^ q) ≤
          ∫⁻ r, ENNReal.ofReal r ^ (d + 1 - 1) * S r ^ q :=
        lintegral_mono' Measure.restrict_le_self fun _ => le_rfl
      refine le_trans hfull ?_
      have hcb := hcomb f₀ hf₀
      have hraise : (∫⁻ r, ENNReal.ofReal r ^ (d + 1 - 1) * S r ^ q) =
          ((∫⁻ r, ENNReal.ofReal r ^ (d + 1 - 1) * S r ^ q) ^ (1 / q)) ^ q := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
      rw [hraise]
      refine ENNReal.rpow_le_rpow ?_ hq0.le
      rw [hS, hNp] at *
      exact hcb
    calc (∫⁻ x : Euclidean (d + 1),
        ‖M E (fun y : Euclidean (d + 1) => f₀ ‖y‖) x‖ₑ ^ q)
        ≤ ∫⁻ x : Euclidean (d + 1), ENNReal.ofReal C₀ ^ q * (S ‖x‖) ^ q := hstep1
      _ = ENNReal.ofReal C₀ ^ q * (ENNReal.ofReal (surfaceMass (d + 1)) *
            ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (d + 1 - 1) * S r ^ q) :=
          hstep2
      _ ≤ ENNReal.ofReal C₀ ^ q * (ENNReal.ofReal (surfaceMass (d + 1)) *
            (ENNReal.ofReal K * Np) ^ q) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hstep3)
      _ = ENNReal.ofReal C₀ ^ q * ENNReal.ofReal (surfaceMass (d + 1)) *
            (ENNReal.ofReal K * Np) ^ q := by ring
  -- take `q`-th roots and rewrite both norms
  have hq0' : ENNReal.ofReal q ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hq0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le, eLpNorm_lift_eq hD hp0 hf₀, ← hNp]
  refine le_trans (ENNReal.rpow_le_rpow hbound (by positivity)) (le_of_eq ?_)
  have hinv : (0 : ℝ) ≤ 1 / q := by positivity
  have hsplit : (ENNReal.ofReal C₀ ^ q * ENNReal.ofReal (surfaceMass (d + 1)) *
        (ENNReal.ofReal K * Np) ^ q) ^ (1 / q) =
      (ENNReal.ofReal C₀ * ENNReal.ofReal (surfaceMass (d + 1)) ^ (1 / q) *
        ENNReal.ofReal K) * Np := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hinv, ENNReal.mul_rpow_of_nonneg _ _ hinv,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne']
    simp only [ENNReal.rpow_one]
    ring
  have hscalar : ENNReal.ofReal C₀ *
        ENNReal.ofReal (surfaceMass (d + 1)) ^ (1 / q) * ENNReal.ofReal K =
      ENNReal.ofReal (C₀ * K * surfaceMass (d + 1) ^ (1 / q - 1 / p)) *
        ENNReal.ofReal (surfaceMass (d + 1)) ^ (1 / p) := by
    rw [ENNReal.ofReal_rpow_of_pos hsm, ENNReal.ofReal_rpow_of_pos hsm,
      ← ENNReal.ofReal_mul hC₀.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show C₀ * K * surfaceMass (d + 1) ^ (1 / q - 1 / p) *
          surfaceMass (d + 1) ^ (1 / p) =
        C₀ * K * (surfaceMass (d + 1) ^ (1 / q - 1 / p) *
          surfaceMass (d + 1) ^ (1 / p)) by ring,
      ← Real.rpow_add hsm, show (1 / q - 1 / p) + 1 / p = 1 / q by ring]
    ring
  rw [hsplit, hscalar, mul_assoc]

/-- The maximal function of a continuous radial datum is measurable. -/
theorem measurable_M_lift {D : ℕ} (E : Set ℝ) {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀) :
    Measurable (M E (fun y : Euclidean D => f₀ ‖y‖)) := by
  have hcont : Continuous (fun y : Euclidean D => f₀ ‖y‖) :=
    hf₀.comp continuous_norm
  change Measurable (_root_.Spherical.restrictedSphericalMaximal E
    (fun y : Euclidean D => f₀ ‖y‖))
  rw [Auto.Spherical.Bourgain.restrictedSphericalMaximal_eq_restrictedNormalizedSphericalMaximal]
  exact Auto.Spherical.PowerWeights.measurable_restrictedNormalizedSphericalMaximal
    E _ hcont

/-- **The radial strong type on the continuous-profile core.**  This is the
`§4` upper bound in its final form: given the main-term estimate in the range
under consideration, the spherical maximal operator maps radial data with a
continuous profile from `L^p` to `L^q`. -/
theorem memLp_and_eLpNorm_M_lift_le {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hqpd : q < p * ((d + 1 : ℕ) : ℝ))
    (hmain : ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℂ, Measurable g →
      (∫⁻ r, ENNReal.ofReal r ^ (d + 1 - 1) *
          brsMainMaximal (d + 1) E p g r ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C *
          (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^ p) ^ (1 / p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f₀ : ℝ → ℂ, Continuous f₀ →
      MemLp (fun x : Euclidean (d + 1) => f₀ ‖x‖) (ENNReal.ofReal p) volume →
        MemLp (M E (fun x : Euclidean (d + 1) => f₀ ‖x‖)) (ENNReal.ofReal q)
            volume ∧
          eLpNorm (M E (fun x : Euclidean (d + 1) => f₀ ‖x‖))
              (ENNReal.ofReal q) volume ≤
            ENNReal.ofReal C *
              eLpNorm (fun x : Euclidean (d + 1) => f₀ ‖x‖) (ENNReal.ofReal p)
                volume := by
  obtain ⟨C, hC, hbound⟩ := eLpNorm_M_lift_le hd hE hp hpq hqpd hmain
  refine ⟨C, hC, fun f₀ hf₀ hmem => ⟨⟨?_, ?_⟩, hbound f₀ hf₀⟩⟩
  · exact (measurable_M_lift E hf₀).aestronglyMeasurable
  · refine lt_of_le_of_lt (hbound f₀ hf₀) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmem.2

/-- The exponent `a = D - 1 - D/p` of the radial main term, in the form
required by Proposition 4.5. -/
theorem brs_exponent_form {d : ℕ} {p a : ℝ} (hp : 0 < p)
    (hae : (d : ℝ) - ((d : ℝ) + 1) / p = a) :
    (((((d + 1 : ℕ) : ℝ)) - 1) * (1 - 1 / p) - 1) + 1 - 1 / p = a := by
  rw [← hae]
  push_cast
  field_simp
  ring

/-- **Theorem 1.1, the upper bound below the critical exponent.**  If `E` has
upper Minkowski exponent `β < 1` and the exponent pair satisfies the strict
inequalities of `Δ_β`, then the spherical maximal operator is of strong type
on radial data with a continuous profile. -/
theorem thm11_core_small_p {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hM : HasUpperMinkowskiExponent E β) {p q a : ℝ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hqpd : q < p * ((d + 1 : ℕ) : ℝ))
    (hae : (d : ℝ) - ((d : ℝ) + 1) / p = a) (ha : a < 0)
    (hβlt : β < q * a + 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f₀ : ℝ → ℂ, Continuous f₀ →
      MemLp (fun x : Euclidean (d + 1) => f₀ ‖x‖) (ENNReal.ofReal p) volume →
        MemLp (M E (fun x : Euclidean (d + 1) => f₀ ‖x‖)) (ENNReal.ofReal q)
            volume ∧
          eLpNorm (M E (fun x : Euclidean (d + 1) => f₀ ‖x‖))
              (ENNReal.ofReal q) volume ≤
            ENNReal.ofReal C *
              eLpNorm (fun x : Euclidean (d + 1) => f₀ ‖x‖) (ENNReal.ofReal p)
                volume := by
  have hD : 2 ≤ d + 1 := by omega
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hq : (1 : ℝ) ≤ q := le_trans hp hpq
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hEnull : volume (closure E) = 0 :=
    volume_closure_eq_zero_of_minkowski hE hβ0 hβ1 hM
  obtain ⟨S, hS, hcov⟩ := exists_cov_bound_of_minkowski hE hβ0 hM hq0 hβlt
  have hmain := prop45_brsMainMaximal (d := d + 1) hD hE hEne hEnull hp hq hpq
    (brs_exponent_form hp0 hae) ha hS hcov
  exact memLp_and_eLpNorm_M_lift_le hd hE hp hpq hqpd hmain

/-- **Theorem 1.1, the upper bound above the critical exponent.**  For
`p > p_D` no covering hypothesis on `E` is needed. -/
theorem thm11_core_large_p {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hqpd : q < p * ((d + 1 : ℕ) : ℝ))
    (hpd : (((d + 1 : ℕ) : ℝ)) / ((((d + 1 : ℕ) : ℝ)) - 1) < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f₀ : ℝ → ℂ, Continuous f₀ →
      MemLp (fun x : Euclidean (d + 1) => f₀ ‖x‖) (ENNReal.ofReal p) volume →
        MemLp (M E (fun x : Euclidean (d + 1) => f₀ ‖x‖)) (ENNReal.ofReal q)
            volume ∧
          eLpNorm (M E (fun x : Euclidean (d + 1) => f₀ ‖x‖))
              (ENNReal.ofReal q) volume ≤
            ENNReal.ofReal C *
              eLpNorm (fun x : Euclidean (d + 1) => f₀ ‖x‖) (ENNReal.ofReal p)
                volume := by
  have hD : 2 ≤ d + 1 := by omega
  have hq0 : (0 : ℝ) < q :=
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hp) hpq
  have hmain := prop44_brsMainMaximal (d := d + 1) hD hE hpd hq0
  exact memLp_and_eLpNorm_M_lift_le hd hE hp hpq hqpd hmain

/-- **Theorem 1.1, the endpoint upper bound at `p = p_D`.**  Here the
logarithmic covering condition of Proposition 4.6 is used. -/
theorem thm11_core_endpoint {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hM : HasUpperMinkowskiExponent E β) {q B : ℝ} (hB : 0 < B)
    (hpq : (((d + 1 : ℕ) : ℝ)) / ((((d + 1 : ℕ) : ℝ)) - 1) ≤ q)
    (hqpd : q < (((d + 1 : ℕ) : ℝ)) / ((((d + 1 : ℕ) : ℝ)) - 1) *
      ((d + 1 : ℕ) : ℝ))
    (hcov : ∀ l : ℕ, 1 ≤ l →
      ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (B ^ q * (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) *
          (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / ((d + 1 : ℕ) : ℝ))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ f₀ : ℝ → ℂ, Continuous f₀ →
      MemLp (fun x : Euclidean (d + 1) => f₀ ‖x‖)
          (ENNReal.ofReal ((((d + 1 : ℕ) : ℝ)) / ((((d + 1 : ℕ) : ℝ)) - 1)))
          volume →
        MemLp (M E (fun x : Euclidean (d + 1) => f₀ ‖x‖)) (ENNReal.ofReal q)
            volume ∧
          eLpNorm (M E (fun x : Euclidean (d + 1) => f₀ ‖x‖))
              (ENNReal.ofReal q) volume ≤
            ENNReal.ofReal C *
              eLpNorm (fun x : Euclidean (d + 1) => f₀ ‖x‖)
                (ENNReal.ofReal ((((d + 1 : ℕ) : ℝ)) /
                  ((((d + 1 : ℕ) : ℝ)) - 1))) volume := by
  have hD : 2 ≤ d + 1 := by omega
  have hDR : (2 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hD
  have hD1 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) - 1 := by linarith
  have hpd1 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) - 1) := by
    rw [le_div_iff₀ hD1]
    linarith
  have hEnull : volume (closure E) = 0 :=
    volume_closure_eq_zero_of_minkowski hE hβ0 hβ1 hM
  obtain ⟨C, hC, hb⟩ :=
    prop46_brsMainMaximal (d := d + 1) hD hE hEne hEnull hpq hB hcov
  have hmain : ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℂ, Measurable g →
      (∫⁻ r, ENNReal.ofReal r ^ (d + 1 - 1) *
          brsMainMaximal (d + 1) E
            (((d + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) - 1)) g r ^ q) ^ (1 / q) ≤
        ENNReal.ofReal C *
          (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal ‖g s‖) ^
            (((d + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) - 1))) ^
              (1 / (((d + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) - 1))) := by
    refine ⟨C, hC, fun g hg => ?_⟩
    rw [one_div_div]
    exact hb g hg
  exact memLp_and_eLpNorm_M_lift_le hd hE hpd1 hpq hqpd hmain

/-- The three closed half-planes cutting out `Δ_β`. -/
def DeltaHalfplanes (d : ℕ) (beta : ℝ) : Set ExponentPoint :=
  {z : ExponentPoint | z.2 ≤ z.1 ∧ z.1 ≤ (d : ℝ) * z.2 ∧
    0 ≤ (1 - beta) * z.2 + ((d : ℝ) - 1) - (d : ℝ) * z.1}

theorem convex_DeltaHalfplanes (d : ℕ) (beta : ℝ) :
    Convex ℝ (DeltaHalfplanes d beta) := by
  have h1 : Convex ℝ {z : ExponentPoint | z.2 - z.1 ≤ 0} := by
    refine convex_halfSpace_le ?_ 0
    exact ⟨fun a b => by simp only [Prod.fst_add, Prod.snd_add]; ring,
      fun c a => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩
  have h2 : Convex ℝ {z : ExponentPoint | z.1 - (d : ℝ) * z.2 ≤ 0} := by
    refine convex_halfSpace_le ?_ 0
    exact ⟨fun a b => by simp only [Prod.fst_add, Prod.snd_add]; ring,
      fun c a => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩
  have h3 : Convex ℝ
      {z : ExponentPoint | -((1 - beta) * z.2 - (d : ℝ) * z.1) ≤ (d : ℝ) - 1} := by
    refine convex_halfSpace_le ?_ _
    exact ⟨fun a b => by simp only [Prod.fst_add, Prod.snd_add]; ring,
      fun c a => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩
  have hset : DeltaHalfplanes d beta =
      {z : ExponentPoint | z.2 - z.1 ≤ 0} ∩
        ({z : ExponentPoint | z.1 - (d : ℝ) * z.2 ≤ 0} ∩
          {z : ExponentPoint |
            -((1 - beta) * z.2 - (d : ℝ) * z.1) ≤ (d : ℝ) - 1}) := by
    ext z
    simp only [DeltaHalfplanes, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2]⟩
    · intro h
      exact ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2]⟩
  rw [hset]
  exact h1.inter (h2.inter h3)

/-- **`Δ_β` lies in the three half-planes.** -/
theorem Delta_subset_halfplanes {d : ℕ} (hd : 2 ≤ d) {beta : ℝ} (hβ0 : 0 ≤ beta) :
    Delta d beta ⊆ DeltaHalfplanes d beta := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) < (d : ℝ) - 1 + beta := by linarith
  have hB : (0 : ℝ) < (d : ℝ) ^ 2 - 1 + beta := by nlinarith
  rw [Delta]
  refine convexHull_min ?_ (convex_DeltaHalfplanes d beta)
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h | h | h
  · rw [h, Q1]
    refine ⟨le_rfl, by norm_num, ?_⟩
    show (0 : ℝ) ≤ (1 - beta) * (0 : ℝ) + ((d : ℝ) - 1) - (d : ℝ) * (0 : ℝ)
    linarith
  · rw [h, Q2]
    refine ⟨le_rfl, ?_, ?_⟩
    · have h1 : ((d : ℝ) - 1) / ((d : ℝ) - 1 + beta) ≤
          (d : ℝ) * (((d : ℝ) - 1) / ((d : ℝ) - 1 + beta)) := by
        have hc : (0 : ℝ) ≤ ((d : ℝ) - 1) / ((d : ℝ) - 1 + beta) :=
          div_nonneg (by linarith) hA.le
        nlinarith
      exact h1
    · have hc : ((d : ℝ) - 1) / ((d : ℝ) - 1 + beta) * ((d : ℝ) - 1 + beta) =
          (d : ℝ) - 1 := div_mul_cancel₀ _ hA.ne'
      nlinarith [hc]
  · rw [h, P3rad]
    have hc : ((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1 + beta) * ((d : ℝ) ^ 2 - 1 + beta) =
        (d : ℝ) - 1 := div_mul_cancel₀ _ hB.ne'
    have hx : (d : ℝ) * ((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1 + beta) =
        (d : ℝ) * (((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1 + beta)) := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hx]
      have hpos : (0 : ℝ) ≤ ((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1 + beta) :=
        div_nonneg (by linarith) hB.le
      nlinarith
    · rw [hx]
    · rw [hx]
      nlinarith [hc]

/-- **Interior points of `Δ_β` satisfy the strict inequalities.** -/
theorem interior_Delta_strict {d : ℕ} (hd : 2 ≤ d) {beta : ℝ} (hβ0 : 0 ≤ beta)
    {z : ExponentPoint} (hz : z ∈ interior (Delta d beta)) :
    z.2 < z.1 ∧ z.1 < (d : ℝ) * z.2 ∧
      0 < (1 - beta) * z.2 + ((d : ℝ) - 1) - (d : ℝ) * z.1 := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  have hsub : Metric.ball z ε ⊆ DeltaHalfplanes d beta := fun w hw =>
    Delta_subset_halfplanes hd hβ0 (interior_subset (hball hw))
  have hpert : ∀ t : ℝ, |t| < ε → (z.1 + t, z.2) ∈ DeltaHalfplanes d beta := by
    intro t ht
    refine hsub ?_
    rw [Metric.mem_ball, Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq]
      simpa using ht
    · simpa using hε
  have hminus := hpert (-(ε / 2)) (by
    rw [abs_of_nonpos (by linarith)]
    linarith)
  have hplus := hpert (ε / 2) (by
    rw [abs_of_nonneg (by linarith)]
    linarith)
  obtain ⟨hm1, -, -⟩ := hminus
  obtain ⟨-, hp2, hp3⟩ := hplus
  refine ⟨by simpa using (by linarith [hm1] : z.2 < z.1), ?_, ?_⟩
  · have h : z.1 + ε / 2 ≤ (d : ℝ) * z.2 := hp2
    linarith
  · have h : 0 ≤ (1 - beta) * z.2 + ((d : ℝ) - 1) - (d : ℝ) * (z.1 + ε / 2) := hp3
    nlinarith

/-- **The critical-line consequence of a radial bound.**  On the segment where
`(1-β)/q + d - 1 - d/p = 0` — the edge `[P₂,β, P₃,β^rad]` of `Δ_β` — a radial
`L^p → L^q` bound forces the entropy quantity `δ^β N(E,δ)` to stay bounded. -/
theorem sup_finite_of_hasRadialStrongType_critical {d : ℕ} (hd : 0 < d)
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) {p q β : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hcrit : (1 - β) / q + (d : ℝ) - 1 - (d : ℝ) / p = 0)
    (h : HasRadialStrongType d E (ENNReal.ofReal p) (ENNReal.ofReal q)) :
    ∃ A : ℝ, 0 < A ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 2 →
      δ ^ β * ((intervalCoveringNumber E δ : ℕ) : ℝ) ≤ A := by
  obtain ⟨K, hK, hbound⟩ :=
    coveringNumber_test_bound_of_hasRadialStrongType hd hE hp hq h
  have hexp : (d : ℝ) - 1 + 1 / q - (d : ℝ) / p = β / q := by
    have h1 : (1 - β) / q = 1 / q - β / q := by ring
    rw [h1] at hcrit
    linarith
  refine ⟨(2 : ℝ) ^ β * K ^ q, ?_, ?_⟩
  · have h2 : (0 : ℝ) < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : (0 : ℝ) < K ^ q := Real.rpow_pos_of_pos hK _
    positivity
  intro δ hδ hδ2
  set δ' : ℝ := δ / 2 with hδ'
  have hδ'pos : 0 < δ' := by
    rw [hδ']
    linarith
  have hδ'1 : δ' ≤ 1 := by
    rw [hδ']
    linarith
  have hδeq : 2 * δ' = δ := by
    rw [hδ']
    ring
  have hb := hbound δ' hδ'pos hδ'1
  rw [hexp, hδeq] at hb
  -- raise the estimate to the `q`-th power
  set N : ℝ := ((intervalCoveringNumber E δ : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := by
    rw [hN]
    exact Nat.cast_nonneg _
  have hlhs : (0 : ℝ) ≤ N ^ (1 / q) * δ' ^ (β / q) := by
    have h1 : (0 : ℝ) ≤ N ^ (1 / q) := Real.rpow_nonneg hN0 _
    have h2 : (0 : ℝ) ≤ δ' ^ (β / q) := Real.rpow_nonneg hδ'pos.le _
    positivity
  have hpow := Real.rpow_le_rpow hlhs hb hq.le
  have hexpand : (N ^ (1 / q) * δ' ^ (β / q)) ^ q = N * δ' ^ β := by
    rw [Real.mul_rpow (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hδ'pos.le _),
      ← Real.rpow_mul hN0, ← Real.rpow_mul hδ'pos.le, one_div,
      inv_mul_cancel₀ hq.ne', Real.rpow_one, div_mul_cancel₀ β hq.ne']
  rw [hexpand] at hpow
  -- undo the halving of the scale
  have hhalf : δ' ^ β = δ ^ β / (2 : ℝ) ^ β := by
    rw [hδ', Real.div_rpow hδ.le (by norm_num)]
  rw [hhalf] at hpow
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  rw [mul_comm]
  calc N * δ ^ β = (N * (δ ^ β / (2 : ℝ) ^ β)) * (2 : ℝ) ^ β := by
        field_simp
    _ ≤ K ^ q * (2 : ℝ) ^ β := mul_le_mul_of_nonneg_right hpow h2pos.le
    _ = (2 : ℝ) ^ β * K ^ q := by ring

/-- **Theorem 1.1(ii), the failure on the critical edge.**  If the entropy
quantity `δ^β N(E,δ)` is unbounded, then no point of the edge
`[P₂,β, P₃,β^rad]` is a point of radial strong type. -/
theorem not_hasRadialStrongType_of_sup_infinite {d : ℕ} (hd : 0 < d)
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) {p q β : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hcrit : (1 - β) / q + (d : ℝ) - 1 - (d : ℝ) / p = 0)
    (hsup : ∀ A : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 2 ∧
      A < δ ^ β * ((intervalCoveringNumber E δ : ℕ) : ℝ)) :
    ¬ HasRadialStrongType d E (ENNReal.ofReal p) (ENNReal.ofReal q) := by
  intro h
  obtain ⟨A, -, hA⟩ :=
    sup_finite_of_hasRadialStrongType_critical hd hE hp hq hcrit h
  obtain ⟨δ, hδ, hδ2, hlt⟩ := hsup A
  exact absurd (hA δ hδ hδ2) (not_le.mpr hlt)

/-- An exponential beats every power: `2^{γ x}` dominates `x^s` with an
explicit constant, obtained from `1 + y ≤ exp y` applied `n` times. -/
theorem two_rpow_mul_le {γ s : ℝ} (hγ : 0 < γ) (hs : 0 ≤ s) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 1 ≤ x → x ^ s ≤ M * (2 : ℝ) ^ (γ * x) := by
  obtain ⟨n, hn⟩ := exists_nat_ge s
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set n' : ℕ := n + 1 with hn'
  have hn'pos : 0 < n' := by omega
  have hsn : s ≤ (n' : ℝ) := by
    have : (n : ℝ) ≤ (n' : ℝ) := by
      rw [hn']
      push_cast
      linarith
    linarith
  refine ⟨((n' : ℝ) / (γ * Real.log 2)) ^ n', ?_, fun x hx => ?_⟩
  · have hd : (0 : ℝ) < (n' : ℝ) / (γ * Real.log 2) := by
      refine div_pos ?_ (by positivity)
      exact_mod_cast hn'pos
    positivity
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hn'R : (0 : ℝ) < (n' : ℝ) := by exact_mod_cast hn'pos
  -- the exponential lower bound
  have hexp : ((γ * x * Real.log 2) / (n' : ℝ)) ^ n' ≤ (2 : ℝ) ^ (γ * x) := by
    have hpos : (0 : ℝ) ≤ (γ * x * Real.log 2) / (n' : ℝ) := by positivity
    have hstep : ((γ * x * Real.log 2) / (n' : ℝ)) ^ n' ≤
        (Real.exp ((γ * x * Real.log 2) / (n' : ℝ))) ^ n' := by
      refine pow_le_pow_left₀ hpos ?_ n'
      have h := Real.add_one_le_exp ((γ * x * Real.log 2) / (n' : ℝ))
      linarith
    refine le_trans hstep (le_of_eq ?_)
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1
    field_simp
  -- compare the powers of `x`
  have hxs : x ^ s ≤ x ^ (n' : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hsn
  have hxn : x ^ (n' : ℝ) = x ^ n' := by
    rw [Real.rpow_natCast]
  have hkey : x ^ n' ≤ ((n' : ℝ) / (γ * Real.log 2)) ^ n' *
      ((γ * x * Real.log 2) / (n' : ℝ)) ^ n' := by
    rw [← mul_pow]
    refine le_of_eq ?_
    congr 1
    field_simp
  calc x ^ s ≤ x ^ n' := by rw [← hxn]; exact hxs
    _ ≤ ((n' : ℝ) / (γ * Real.log 2)) ^ n' *
          ((γ * x * Real.log 2) / (n' : ℝ)) ^ n' := hkey
    _ ≤ ((n' : ℝ) / (γ * Real.log 2)) ^ n' * (2 : ℝ) ^ (γ * x) := by
        refine mul_le_mul_of_nonneg_left hexp ?_
        have hd : (0 : ℝ) < (n' : ℝ) / (γ * Real.log 2) := by
          refine div_pos hn'R (by positivity)
        positivity

/-- **The logarithmic covering hypothesis from `β < 1`.**  A set of upper
Minkowski exponent `β < 1` satisfies the doubly exponential covering condition
of Proposition 4.6. -/
theorem exists_logcov_bound_of_minkowski {E : Set ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hM : HasUpperMinkowskiExponent E β) {q : ℝ} (hq : 0 < q)
    {D : ℕ} (hD : 2 ≤ D) :
    ∃ B : ℝ, 0 < B ∧ ∀ l : ℕ, 1 ≤ l →
      ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (B ^ q * (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) *
          (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (D : ℝ)))) := by
  have hDR : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set ε : ℝ := (1 - β) / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    linarith
  set γ : ℝ := 1 - (β + ε) with hγ
  have hγpos : 0 < γ := by
    rw [hγ, hε]
    linarith
  obtain ⟨C, hC, hcov⟩ :=
    intervalCoveringNumber_upper_bound_of_hasUpperMinkowskiExponent hM ε hεpos
  obtain ⟨M, hMpos, hgrow⟩ := two_rpow_mul_le (γ := γ) (s := q / (D : ℝ)) hγpos
    (by positivity)
  -- the constant
  refine ⟨(C * M * (Real.log 2) ^ (q / (D : ℝ))) ^ (1 / q), ?_, ?_⟩
  · refine Real.rpow_pos_of_pos ?_ _
    have h1 : (0 : ℝ) < (Real.log 2) ^ (q / (D : ℝ)) :=
      Real.rpow_pos_of_pos hlog2 _
    positivity
  intro l hl
  set m : ℝ := (2 : ℝ) ^ (l - 1) with hm
  have hm1 : (1 : ℝ) ≤ m := by
    rw [hm]
    exact one_le_pow₀ (by norm_num)
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  -- the scale
  have hδeq : (2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ)) = (2 : ℝ) ^ (-m) := by
    rw [hm, ← Real.rpow_intCast (2 : ℝ) (-(2 ^ (l - 1) : ℤ))]
    congr 1
    push_cast
    ring
  have hδpos : (0 : ℝ) < (2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ)) := by positivity
  have hδlt : (2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ)) < 1 := by
    rw [hδeq]
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    linarith
  have hb := hcov _ hδpos hδlt
  -- rewrite the covering bound in terms of `m`
  have hbound : ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ) ≤
      C * (2 : ℝ) ^ (m * (β + ε)) := by
    refine le_trans hb (le_of_eq ?_)
    rw [hδeq, two_rpow_rpow]
    congr 1
    ring
  -- the target, in terms of `m`
  have hsplit : (2 : ℝ) ^ (m * (β + ε)) * (2 : ℝ) ^ (γ * m) = (2 : ℝ) ^ m := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    rw [hγ]
    ring
  have hms : (0 : ℝ) < m ^ (q / (D : ℝ)) := Real.rpow_pos_of_pos hmpos _
  have hstep : (2 : ℝ) ^ (m * (β + ε)) * m ^ (q / (D : ℝ)) ≤ M * (2 : ℝ) ^ m := by
    calc (2 : ℝ) ^ (m * (β + ε)) * m ^ (q / (D : ℝ))
        ≤ (2 : ℝ) ^ (m * (β + ε)) * (M * (2 : ℝ) ^ (γ * m)) :=
          mul_le_mul_of_nonneg_left (hgrow m hm1) (by positivity)
      _ = M * ((2 : ℝ) ^ (m * (β + ε)) * (2 : ℝ) ^ (γ * m)) := by ring
      _ = M * (2 : ℝ) ^ m := by rw [hsplit]
  have htarget : C * (2 : ℝ) ^ (m * (β + ε)) ≤
      C * M * (2 : ℝ) ^ m * m ^ (-(q / (D : ℝ))) := by
    have hfin : (2 : ℝ) ^ (m * (β + ε)) ≤
        M * (2 : ℝ) ^ m * m ^ (-(q / (D : ℝ))) := by
      rw [Real.rpow_neg hmpos.le, ← div_eq_mul_inv, le_div_iff₀ hms]
      exact hstep
    calc C * (2 : ℝ) ^ (m * (β + ε))
        ≤ C * (M * (2 : ℝ) ^ m * m ^ (-(q / (D : ℝ)))) :=
          mul_le_mul_of_nonneg_left hfin hC.le
      _ = C * M * (2 : ℝ) ^ m * m ^ (-(q / (D : ℝ))) := by ring
  -- assemble
  have hfinal : ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ) ≤
      ((C * M * (Real.log 2) ^ (q / (D : ℝ))) ^ (1 / q)) ^ q *
        (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) *
        (((2 : ℝ) ^ (l - 1)) * Real.log 2) ^ (-(q / (D : ℝ))) := by
    have hpow : ((C * M * (Real.log 2) ^ (q / (D : ℝ))) ^ (1 / q)) ^ q =
        C * M * (Real.log 2) ^ (q / (D : ℝ)) := by
      have hbase : (0 : ℝ) < C * M * (Real.log 2) ^ (q / (D : ℝ)) := by
        have h1 : (0 : ℝ) < (Real.log 2) ^ (q / (D : ℝ)) :=
          Real.rpow_pos_of_pos hlog2 _
        positivity
      rw [← Real.rpow_mul hbase.le, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one]
    have hmpow : (2 : ℝ) ^ ((2 ^ (l - 1) : ℤ)) = (2 : ℝ) ^ m := by
      rw [hm, ← Real.rpow_intCast (2 : ℝ) ((2 ^ (l - 1) : ℤ))]
      congr 1
      push_cast
      ring
    have hlogsplit : (m * Real.log 2) ^ (-(q / (D : ℝ))) =
        m ^ (-(q / (D : ℝ))) * (Real.log 2) ^ (-(q / (D : ℝ))) :=
      Real.mul_rpow hmpos.le hlog2.le
    have hcancel : (Real.log 2) ^ (q / (D : ℝ)) *
        (Real.log 2) ^ (-(q / (D : ℝ))) = 1 := by
      rw [← Real.rpow_add hlog2]
      simp
    rw [hpow, hmpow, ← hm, hlogsplit]
    calc ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ)
        ≤ C * (2 : ℝ) ^ (m * (β + ε)) := hbound
      _ ≤ C * M * (2 : ℝ) ^ m * m ^ (-(q / (D : ℝ))) := htarget
      _ = C * M * (Real.log 2) ^ (q / (D : ℝ)) * (2 : ℝ) ^ m *
            (m ^ (-(q / (D : ℝ))) * (Real.log 2) ^ (-(q / (D : ℝ)))) := by
          rw [show C * M * (Real.log 2) ^ (q / (D : ℝ)) * (2 : ℝ) ^ m *
                (m ^ (-(q / (D : ℝ))) * (Real.log 2) ^ (-(q / (D : ℝ)))) =
              C * M * (2 : ℝ) ^ m * m ^ (-(q / (D : ℝ))) *
                ((Real.log 2) ^ (q / (D : ℝ)) *
                  (Real.log 2) ^ (-(q / (D : ℝ)))) by ring, hcancel, mul_one]
  calc ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal
          ((intervalCoveringNumber E ((2 : ℝ) ^ (-(2 ^ (l - 1) : ℤ))) : ℕ) : ℝ) := by
        rw [ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal

/-- **`Δ_β` lies in the unit square.** -/
theorem Delta_subset_unitSquare {d : ℕ} (hd : 2 ≤ d) {beta : ℝ} (hβ0 : 0 ≤ beta)
    (hβ1 : beta ≤ 1) :
    Delta d beta ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) < (d : ℝ) - 1 + beta := by linarith
  have hB : (0 : ℝ) < (d : ℝ) ^ 2 - 1 + beta := by nlinarith
  rw [Delta]
  refine convexHull_min ?_ (convex_Icc _ _|>.prod (convex_Icc _ _))
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h | h | h
  · rw [h, Q1]
    exact ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩
  · rw [h, Q2]
    have hc0 : (0 : ℝ) ≤ ((d : ℝ) - 1) / ((d : ℝ) - 1 + beta) :=
      div_nonneg (by linarith) hA.le
    have hc1 : ((d : ℝ) - 1) / ((d : ℝ) - 1 + beta) ≤ 1 := by
      rw [div_le_one hA]
      linarith
    exact ⟨⟨hc0, hc1⟩, ⟨hc0, hc1⟩⟩
  · rw [h, P3rad]
    have hx0 : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1 + beta) := by
      refine div_nonneg ?_ hB.le
      nlinarith
    have hx1 : (d : ℝ) * ((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1 + beta) ≤ 1 := by
      rw [div_le_one hB]
      nlinarith
    have hy0 : (0 : ℝ) ≤ ((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1 + beta) :=
      div_nonneg (by linarith) hB.le
    have hy1 : ((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1 + beta) ≤ 1 := by
      rw [div_le_one hB]
      nlinarith
    exact ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩

/-- Strong `L^p_rad → L^q` boundedness on radial data with a continuous
profile.  This is the class on which the upper bounds of §4 operate: Lemma 4.1
represents the spherical average of such a datum by its kernel formula. -/
def HasRadialStrongTypeCont (D : ℕ) (E : Set ℝ) (p q : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f₀ : ℝ → ℂ, Continuous f₀ →
    MemLp (fun x : Euclidean D => f₀ ‖x‖) (ENNReal.ofReal p) volume →
      MemLp (M E (fun x : Euclidean D => f₀ ‖x‖)) (ENNReal.ofReal q) volume ∧
        eLpNorm (M E (fun x : Euclidean D => f₀ ‖x‖)) (ENNReal.ofReal q)
            volume ≤
          ENNReal.ofReal C *
            eLpNorm (fun x : Euclidean D => f₀ ‖x‖) (ENNReal.ofReal p) volume

/-- The type set of the continuous-profile core, in reciprocal coordinates. -/
def radialTypeSetCont (D : ℕ) (E : Set ℝ) : Set ExponentPoint :=
  {z | ∃ p q : ℝ, 1 ≤ p ∧ 1 ≤ q ∧ z = (1 / p, 1 / q) ∧
    HasRadialStrongTypeCont D E p q}

/-- The full radial type set is contained in the continuous-profile one. -/
theorem hasRadialStrongTypeCont_of_hasRadialStrongType {D : ℕ} {E : Set ℝ}
    {p q : ℝ} (h : HasRadialStrongType D E (ENNReal.ofReal p)
      (ENNReal.ofReal q)) :
    HasRadialStrongTypeCont D E p q := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun f₀ hf₀ hmem => ?_⟩
  exact hbound _ hmem (isNormRadial_lift D f₀)

/-- **Theorem 1.1, the sufficiency half.**  Every interior point of `Δ_β` is a
point of radial strong type on the continuous-profile core. -/
theorem interior_Delta_subset_radialTypeSetCont {d : ℕ} (hd : 2 ≤ d)
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hM : HasUpperMinkowskiExponent E β) :
    interior (Delta (d + 1) β) ⊆ radialTypeSetCont (d + 1) E := by
  have hD : 2 ≤ d + 1 := by omega
  have hDR : (2 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hD
  have hD1 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) - 1 := by linarith
  intro z hz
  obtain ⟨h1, h2, h3⟩ := interior_Delta_strict hD hβ0 hz
  obtain ⟨⟨hz10, hz11⟩, ⟨hz20, hz21⟩⟩ :=
    Delta_subset_unitSquare hD hβ0 hβ1.le (interior_subset hz)
  -- the exponents
  have hz2pos : 0 < z.2 := by
    rcases eq_or_lt_of_le hz20 with h | h
    · exfalso
      rw [← h] at h2
      simp only [mul_zero] at h2
      linarith
    · exact h
  have hz1pos : 0 < z.1 := lt_trans hz2pos h1
  set p : ℝ := 1 / z.1 with hp
  set q : ℝ := 1 / z.2 with hq
  have hp1 : 1 ≤ p := by
    rw [hp, le_div_iff₀ hz1pos]
    linarith
  have hq1 : 1 ≤ q := by
    rw [hq, le_div_iff₀ hz2pos]
    linarith
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hzp : z.1 = 1 / p := by
    rw [hp, one_div_one_div]
  have hzq : z.2 = 1 / q := by
    rw [hq, one_div_one_div]
  have hpq : p ≤ q := by
    rw [hp, hq]
    exact one_div_le_one_div_of_le hz2pos h1.le
  have hqpd : q < p * ((d + 1 : ℕ) : ℝ) := by
    have hpD : p * ((d + 1 : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) / z.1 := by
      rw [hp]
      field_simp
    rw [hq, hpD, div_lt_div_iff₀ hz2pos hz1pos, one_mul]
    exact h2
  refine ⟨p, q, hp1, hq1, ?_, ?_⟩
  · rw [← hzp, ← hzq]
  -- the three branches
  by_cases hcase : ((d + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) - 1) < p
  · exact thm11_core_large_p hd hE hp1 hpq hqpd hcase
  · rcases eq_or_lt_of_le (not_lt.mp hcase) with hEq | hlt
    · -- the endpoint `p = p_D`
      obtain ⟨B, hB, hcov⟩ :=
        exists_logcov_bound_of_minkowski hβ0 hβ1 hM hq0 (D := d + 1) hD
      have hpq' : ((d + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) - 1) ≤ q := by
        rw [← hEq]
        exact hpq
      have hqpd' : q < ((d + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) - 1) *
          ((d + 1 : ℕ) : ℝ) := by
        rw [← hEq]
        exact hqpd
      have hgoal := thm11_core_endpoint hd hE hEne hβ0 hβ1 hM hB hpq' hqpd' hcov
      rw [HasRadialStrongTypeCont, hEq]
      exact hgoal
    · -- below the critical exponent
      set a : ℝ := (d : ℝ) - ((d : ℝ) + 1) / p with ha
      have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        have h2d : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      have hlt' : p < ((d : ℝ) + 1) / (d : ℝ) := by
        have hkey : ((d + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) - 1) =
            ((d : ℝ) + 1) / (d : ℝ) := by
          rw [hcast, add_sub_cancel_right]
        rw [hkey] at hlt
        exact hlt
      have hanel : a < 0 := by
        rw [ha, sub_neg, lt_div_iff₀ hp0]
        rw [lt_div_iff₀ hdpos] at hlt'
        nlinarith [hlt']
      have hβlt : β < q * a + 1 := by
        rw [hzp, hzq, hcast] at h3
        have h3' : 0 < (1 - β) * (1 / q) + a := by
          rw [ha]
          have hsimp : ((d : ℝ) + 1 - 1) = (d : ℝ) := by ring
          have hmul : ((d : ℝ) + 1) * (1 / p) = ((d : ℝ) + 1) / p := by
            field_simp
          rw [hsimp, hmul] at h3
          linarith
        have hmul := mul_lt_mul_of_pos_left h3' hq0
        rw [mul_zero] at hmul
        have hexp : q * ((1 - β) * (1 / q) + a) = (1 - β) + q * a := by
          field_simp
        rw [hexp] at hmul
        linarith
      exact thm11_core_small_p hd hE hEne hβ0 hβ1 hM hp1 hpq hqpd ha.symm hanel
        hβlt

/-- **Theorem 1.1 of BRS, both inclusions.**  For `E ⊆ [1,2]` of upper
Minkowski dimension `β < 1`, every interior point of `Δ_β` is a point of
radial strong type (on the continuous-profile core), and every point of the
radial type set lies in `Δ_β`. -/
theorem thm11_radialTypeSet {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hM : HasUpperMinkowskiExponent E β)
    (hdim : upperMinkowskiDimension E = β) :
    interior (Delta (d + 1) β) ⊆ radialTypeSetCont (d + 1) E ∧
      radialTypeSet (d + 1) E ⊆ Delta (d + 1) β :=
  ⟨interior_Delta_subset_radialTypeSetCont hd hE hEne hβ0 hβ1 hM,
    radialTypeSet_subset_Delta (by omega) hE hEne hdim⟩

/-! ## The ambient-two slice identity

In the plane the equatorial sphere is `S⁰`, so the height density degenerates
to `(1 - t²)^{-1/2}`.  The repository already carries the planar height
identity in its *angular* form
(`integral_comp_last_unitSurfaceMeasure_two`), which avoids the singular
density altogether; the reflection argument transports it to an arbitrary
unit direction exactly as in ambient dimension `d + 1 ≥ 3`. -/

/-- **The planar sphere slice identity.**  Integrating a continuous function of
the height `⟪ω, e⟫` over the unit circle is the angular integral of the same
function of `cos φ`. -/
theorem integral_comp_inner_unitSurfaceMeasure_two (e : Euclidean 2)
    (he : ‖e‖ = 1) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ ω : Metric.sphere (0 : Euclidean 2) 1,
        F (inner ℝ (ω : Euclidean 2) e) ∂unitSurfaceMeasure 2) =
      (surfaceMass 1 : ℂ) * ∫ φ in (0 : ℝ)..Real.pi, F (Real.cos φ) := by
  set a : Euclidean 2 := lastAxis 1 with ha
  have hna : ‖a‖ = 1 := by
    rw [ha, lastAxis]
    exact norm_euclideanSucc_last 1
  set u : Euclidean 2 ≃ₗᵢ[ℝ] Euclidean 2 :=
    Submodule.reflection (ℝ ∙ (a - e))ᗮ with hu
  have hua : u a = e := Submodule.reflection_sub (by rw [hna, he])
  set uSphere : Metric.sphere (0 : Euclidean 2) 1 ≃ₜ
      Metric.sphere (0 : Euclidean 2) 1 :=
    u.toHomeomorph.subtype (fun x => by
      simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
      rw [u.norm_map]) with huSphere
  have hmeasure : Measure.map uSphere (unitSurfaceMeasure 2) =
      unitSurfaceMeasure 2 := by
    simpa only [huSphere] using map_unitSurfaceMeasure_linearIsometry 2 u
  have hpres : MeasurePreserving uSphere (unitSurfaceMeasure 2)
      (unitSurfaceMeasure 2) := ⟨uSphere.continuous.measurable, hmeasure⟩
  have hcomp := hpres.integral_comp uSphere.measurableEmbedding
    (fun ω : Metric.sphere (0 : Euclidean 2) 1 =>
      F (inner ℝ (ω : Euclidean 2) e))
  calc
    (∫ ω : Metric.sphere (0 : Euclidean 2) 1,
        F (inner ℝ (ω : Euclidean 2) e) ∂unitSurfaceMeasure 2) =
        ∫ ω : Metric.sphere (0 : Euclidean 2) 1,
          F (inner ℝ ((uSphere ω : Metric.sphere (0 : Euclidean 2) 1) :
            Euclidean 2) e) ∂unitSurfaceMeasure 2 := hcomp.symm
    _ = ∫ ω : Metric.sphere (0 : Euclidean 2) 1,
          F ((ω : Euclidean 2) (Fin.last 1)) ∂unitSurfaceMeasure 2 := by
        apply integral_congr_ae
        filter_upwards with ω
        have hval : ((uSphere ω : Metric.sphere (0 : Euclidean 2) 1) :
            Euclidean 2) = u (ω : Euclidean 2) := rfl
        rw [hval, ← hua, u.inner_map_map]
        rw [ha, lastAxis, inner_euclideanSucc_last]
    _ = (surfaceMass 1 : ℂ) * ∫ φ in (0 : ℝ)..Real.pi, F (Real.cos φ) :=
        integral_comp_last_unitSurfaceMeasure_two F hF

/-- **The planar radial spherical average.**  For a radial datum the circular
average is the angular integral of its profile along the law of cosines. -/
theorem sphericalAverage_comp_norm_two (f₀ : ℝ → ℂ) (hf₀ : Continuous f₀)
    {x : Euclidean 2} (hx : x ≠ 0) (t : ℝ) :
    _root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x =
      (((surfaceMass 2)⁻¹ * surfaceMass 1 : ℝ) : ℂ) *
        ∫ φ in (0 : ℝ)..Real.pi,
          f₀ (Real.sqrt (‖x‖ ^ 2 + t ^ 2 + 2 * ‖x‖ * t * Real.cos φ)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set e : Euclidean 2 := ‖x‖⁻¹ • x with he
  have hne : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    field_simp
  set F : ℝ → ℂ := fun v => f₀ (Real.sqrt (‖x‖ ^ 2 + t ^ 2 + 2 * ‖x‖ * t * v))
    with hF
  have hFcont : Continuous F := by
    rw [hF]
    exact hf₀.comp (Real.continuous_sqrt.comp (by fun_prop))
  have hpoint : ∀ ω : Metric.sphere (0 : Euclidean 2) 1,
      f₀ ‖x + t • (ω : Euclidean 2)‖ = F (inner ℝ (ω : Euclidean 2) e) := by
    intro ω
    have hω : ‖(ω : Euclidean 2)‖ = 1 := by
      simpa using ω.2
    have hinner : inner ℝ (ω : Euclidean 2) e =
        ‖x‖⁻¹ * inner ℝ x (ω : Euclidean 2) := by
      rw [he, real_inner_smul_right, real_inner_comm]
    have hsq : ‖x + t • (ω : Euclidean 2)‖ ^ 2 =
        ‖x‖ ^ 2 + t ^ 2 + 2 * ‖x‖ * t * inner ℝ (ω : Euclidean 2) e := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hω,
        mul_one, hinner]
      have habs : |t| ^ 2 = t ^ 2 := sq_abs t
      rw [habs]
      field_simp
      ring
    rw [hF]
    congr 1
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  calc
    _root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x =
        (((surfaceMass 2)⁻¹ : ℝ) : ℂ) *
          ∫ ω : Metric.sphere (0 : Euclidean 2) 1,
            f₀ ‖x + t • (ω : Euclidean 2)‖ ∂unitSurfaceMeasure 2 := by
      rw [_root_.Auto.Spherical.PowerWeights.sphericalAverage_eq_normalizedSphericalAverage,
        normalizedSphericalAverage, SurfaceMeasureDecay.sphericalAverage]
      push_cast
      ring
    _ = (((surfaceMass 2)⁻¹ : ℝ) : ℂ) *
          ∫ ω : Metric.sphere (0 : Euclidean 2) 1,
            F (inner ℝ (ω : Euclidean 2) e) ∂unitSurfaceMeasure 2 := by
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      exact hpoint ω
    _ = (((surfaceMass 2)⁻¹ : ℝ) : ℂ) *
          ((surfaceMass 1 : ℂ) *
            ∫ φ in (0 : ℝ)..Real.pi, F (Real.cos φ)) := by
      rw [integral_comp_inner_unitSurfaceMeasure_two e hne F hFcont]
    _ = (((surfaceMass 2)⁻¹ * surfaceMass 1 : ℝ) : ℂ) *
          ∫ φ in (0 : ℝ)..Real.pi, F (Real.cos φ) := by
      push_cast
      ring

/-- The planar kernel of (4.2): the `D = 2` case of `brsKernel`, where the
exponent `D - 3 = -1` makes the square roots appear in the denominator. -/
def brsKernelTwo (t r s : ℝ) : ℝ :=
  s / (Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2))

/-- The law of cosines, as the radius attached to an angle. -/
def cosineRadius (r t φ : ℝ) : ℝ :=
  Real.sqrt (r ^ 2 + t ^ 2 + 2 * r * t * Real.cos φ)

theorem cosineRadius_zero {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    cosineRadius r t 0 = r + t := by
  rw [cosineRadius, Real.cos_zero]
  rw [show r ^ 2 + t ^ 2 + 2 * r * t * 1 = (r + t) ^ 2 by ring]
  exact Real.sqrt_sq (by linarith)

theorem cosineRadius_pi (r t : ℝ) : cosineRadius r t Real.pi = |r - t| := by
  rw [cosineRadius, Real.cos_pi]
  rw [show r ^ 2 + t ^ 2 + 2 * r * t * (-1) = (r - t) ^ 2 by ring]
  exact Real.sqrt_sq_eq_abs _

theorem continuous_cosineRadius (r t : ℝ) : Continuous (cosineRadius r t) := by
  unfold cosineRadius
  exact Real.continuous_sqrt.comp (by fun_prop)

/-- The radicand of the law of cosines is positive below the antipode. -/
theorem one_add_cos_pos {φ : ℝ} (hφ : φ ∈ Ioo (0 : ℝ) Real.pi) :
    0 < 1 + Real.cos φ := by
  have hhalf : 0 < Real.cos (φ / 2) := by
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], by linarith [hφ.2]⟩
  have hsq : Real.cos (φ / 2) ^ 2 = 1 / 2 + Real.cos φ / 2 := by
    have h := Real.cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    exact h
  nlinarith [hhalf, hsq]

/-- The radicand of the law of cosines is positive below the antipode. -/
theorem cosineRadius_sq_pos {r t φ : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hφ : φ ∈ Ioo (0 : ℝ) Real.pi) :
    0 < r ^ 2 + t ^ 2 + 2 * r * t * Real.cos φ := by
  have hone := one_add_cos_pos hφ
  have hrt : 0 < r * t := mul_pos hr ht
  nlinarith [sq_nonneg (r - t), hone, hrt]

theorem cosineRadius_pos {r t φ : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hφ : φ ∈ Ioo (0 : ℝ) Real.pi) : 0 < cosineRadius r t φ := by
  rw [cosineRadius]
  exact Real.sqrt_pos.mpr (cosineRadius_sq_pos hr ht hφ)

/-- The derivative of the law-of-cosines radius. -/
theorem hasDerivAt_cosineRadius {r t φ : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hφ : φ ∈ Ioo (0 : ℝ) Real.pi) :
    HasDerivAt (cosineRadius r t)
      (-(r * t * Real.sin φ) / cosineRadius r t φ) φ := by
  have hpos := cosineRadius_sq_pos hr ht hφ
  have hinner : HasDerivAt (fun φ : ℝ => r ^ 2 + t ^ 2 + 2 * r * t * Real.cos φ)
      (2 * r * t * (-Real.sin φ)) φ := by
    have h := (Real.hasDerivAt_cos φ).const_mul (2 * r * t)
    simpa using h.const_add (r ^ 2 + t ^ 2)
  have h := hinner.sqrt (ne_of_gt hpos)
  unfold cosineRadius
  refine h.congr_deriv ?_
  field_simp

/-- The radius is strictly decreasing in the angle. -/
theorem strictAntiOn_cosineRadius {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    StrictAntiOn (cosineRadius r t) (Icc (0 : ℝ) Real.pi) := by
  intro a ha b hb hab
  have hcos : Real.cos b < Real.cos a :=
    Real.strictAntiOn_cos ha hb hab
  have hrt : 0 < r * t := mul_pos hr ht
  have hlt : r ^ 2 + t ^ 2 + 2 * r * t * Real.cos b <
      r ^ 2 + t ^ 2 + 2 * r * t * Real.cos a := by nlinarith
  rw [cosineRadius, cosineRadius]
  refine Real.sqrt_lt_sqrt ?_ hlt
  nlinarith [sq_nonneg (r - t), Real.neg_one_le_cos b, hrt]

/-- **The angular window is the radial window.** -/
theorem image_cosineRadius {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    cosineRadius r t '' Ioo (0 : ℝ) Real.pi = Ioo (|r - t|) (r + t) := by
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  refine le_antisymm ?_ ?_
  · have hsub := (strictAntiOn_cosineRadius hr ht).image_Ioo_subset
    rw [cosineRadius_zero hr ht, cosineRadius_pi] at hsub
    exact hsub
  · have hIVT := intermediate_value_Ioo' hpi
      ((continuous_cosineRadius r t).continuousOn (s := Icc (0 : ℝ) Real.pi))
    rw [cosineRadius_zero hr ht, cosineRadius_pi] at hIVT
    exact hIVT

/-- The kernel identity behind the substitution: the Jacobian of the law of
cosines cancels the planar kernel. -/
theorem abs_deriv_mul_kernelTwo {r t φ : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hφ : φ ∈ Ioo (0 : ℝ) Real.pi) :
    |(-(r * t * Real.sin φ) / cosineRadius r t φ)| *
        (2 * brsKernelTwo t r (cosineRadius r t φ)) = 1 := by
  have hspos := cosineRadius_pos hr ht hφ
  have hsin : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have hrt : 0 < r * t := mul_pos hr ht
  set s : ℝ := cosineRadius r t φ with hs
  have hssq : s ^ 2 = r ^ 2 + t ^ 2 + 2 * r * t * Real.cos φ := by
    rw [hs, cosineRadius, Real.sq_sqrt (cosineRadius_sq_pos hr ht hφ).le]
  have hA : (r + t) ^ 2 - s ^ 2 = 2 * (r * t) * (1 - Real.cos φ) := by
    rw [hssq]
    ring
  have hB : s ^ 2 - (r - t) ^ 2 = 2 * (r * t) * (1 + Real.cos φ) := by
    rw [hssq]
    ring
  have h1c : (0 : ℝ) ≤ 1 - Real.cos φ := by linarith [Real.cos_le_one φ]
  have h2c : (0 : ℝ) ≤ 1 + Real.cos φ := (one_add_cos_pos hφ).le
  have hprod : Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) =
      2 * (r * t) * Real.sin φ := by
    rw [hA, hB, ← Real.sqrt_mul (by
      have : (0 : ℝ) ≤ 2 * (r * t) := by positivity
      exact mul_nonneg this h1c)]
    rw [show 2 * (r * t) * (1 - Real.cos φ) * (2 * (r * t) * (1 + Real.cos φ)) =
        (2 * (r * t)) ^ 2 * (1 - Real.cos φ ^ 2) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      show 1 - Real.cos φ ^ 2 = Real.sin φ ^ 2 by
        have := Real.sin_sq_add_cos_sq φ
        linarith, Real.sqrt_sq hsin.le]
  have habs : |(-(r * t * Real.sin φ) / s)| = r * t * Real.sin φ / s := by
    rw [abs_div, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg hspos.le]
  rw [habs, brsKernelTwo, hprod]
  field_simp

/-- **The kernel representation (4.1)–(4.2) in ambient dimension two.**  The
angular integral of the profile is the kernel integral over the radial
window. -/
theorem integral_kernelTwo_eq_angle {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (f₀ : ℝ → ℂ) :
    (∫ s in Ioo (|r - t|) (r + t), (2 * brsKernelTwo t r s) • f₀ s) =
      ∫ φ in Ioo (0 : ℝ) Real.pi, f₀ (cosineRadius r t φ) := by
  have hderiv : ∀ φ ∈ Ioo (0 : ℝ) Real.pi,
      HasDerivWithinAt (cosineRadius r t)
        (-(r * t * Real.sin φ) / cosineRadius r t φ) (Ioo (0 : ℝ) Real.pi) φ := by
    intro φ hφ
    exact (hasDerivAt_cosineRadius hr ht hφ).hasDerivWithinAt
  have hinj : InjOn (cosineRadius r t) (Ioo (0 : ℝ) Real.pi) :=
    (strictAntiOn_cosineRadius hr ht).injOn.mono Ioo_subset_Icc_self
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv
    hinj (fun s => (2 * brsKernelTwo t r s) • f₀ s)
  rw [image_cosineRadius hr ht] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioo fun φ hφ => ?_
  rw [smul_smul, abs_deriv_mul_kernelTwo hr ht hφ, one_smul]

/-! ## The test function of Lemma 3.5

BRS Lemma 3.5 tests the operator on the indicator of a thin annulus at the
*left endpoint* of the dilation interval `J`.  Its spherical average at radii
`|x| ≈ t - t_L` is large on a tangential cap of chordal width `√(δ/|x|)`,
which is what produces the exponent `(d-1)/2`. -/

/-- The test function `g_δ` of BRS Lemma 3.5: the indicator of the annulus of
radius `tL` and thickness `δ`. -/
def brsAnnulusTest (d : ℕ) (tL δ : ℝ) : Euclidean d → ℂ :=
  fun y => (Icc (tL - δ) (tL + δ)).indicator (fun _ => (1 : ℂ)) ‖y‖

theorem measurable_brsAnnulusTest (d : ℕ) (tL δ : ℝ) :
    Measurable (brsAnnulusTest d tL δ) :=
  measurable_indicator_lift d _ _

theorem isNormRadial_brsAnnulusTest (d : ℕ) (tL δ : ℝ) :
    _root_.Auto.RadialFourierTransform.IsNormRadial (brsAnnulusTest d tL δ) :=
  isNormRadial_indicator_lift d _ _

theorem eLpNorm_brsAnnulusTest (d : ℕ) (tL δ : ℝ) {p : ℝ} (hp : 0 < p) :
    eLpNorm (brsAnnulusTest d tL δ) (ENNReal.ofReal p) volume =
      volume (radialAnnulusIcc d (tL - δ) (tL + δ)) ^ (1 / p) :=
  eLpNorm_indicator_lift d _ _ hp

theorem memLp_brsAnnulusTest {d : ℕ} (hd : 0 < d) {tL δ : ℝ} (htL : 1 ≤ tL)
    (htL2 : tL ≤ 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {p : ℝ} (hp : 0 < p) :
    MemLp (brsAnnulusTest d tL δ) (ENNReal.ofReal p) volume := by
  refine ⟨(measurable_brsAnnulusTest d tL δ).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_brsAnnulusTest d tL δ hp]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  have hvol := volume_thin_shell_le hd htL htL2 hδ hδ1
  refine (lt_of_le_of_lt hvol ?_).ne
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  exact (measure_mono Metric.ball_subset_closedBall).trans_lt measure_closedBall_lt_top

/-- **(3.5) of BRS.**  The interval constraint: every point of the tangential
cap of chordal radius `√(δ/(|x| t))` around the inward radial direction is
carried by the dilation `t` into the annulus of radius `t_L` and thickness
`δ`.  This is the geometric heart of Lemma 3.5. -/
theorem mem_annulus_of_mem_inwardCap {d : ℕ} {tL δ t : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (htL : 1 ≤ tL) {x : Euclidean d} (hxpos : 0 < ‖x‖) (htpos : 0 < t)
    (hclose : |t - ‖x‖ - tL| ≤ δ / 10) {ω : Euclidean d} (hωnorm : ‖ω‖ = 1)
    (hcapmem : dist ω (steinInwardRadialDirection x) <
      Real.sqrt (δ / (‖x‖ * t))) :
    ‖x + t • ω‖ ∈ Icc (tL - δ) (tL + δ) := by
  set a : ℝ := ‖x‖ with ha
  have hat : 0 < a * t := mul_pos hxpos htpos
  set v : Euclidean d := steinInwardRadialDirection x with hv
  have hvnorm : ‖v‖ = 1 := norm_steinInwardRadialDirection hxpos
  set h : ℝ := Real.sqrt (δ / (a * t)) with hh
  have hhsq : h ^ 2 = δ / (a * t) := by
    rw [hh, Real.sq_sqrt (by positivity)]
  have hinnerv : 1 - inner ℝ ω v < h ^ 2 / 2 := by
    have hsq : dist ω v ^ 2 = 2 - 2 * inner ℝ ω v := by
      rw [dist_eq_norm, norm_sub_sq_real, hωnorm, hvnorm]
      ring
    have hlt : dist ω v ^ 2 < h ^ 2 := by
      have hnn : 0 ≤ dist ω v := dist_nonneg
      nlinarith [hcapmem]
    rw [hsq] at hlt
    linarith
  have hinnerx : inner ℝ ω x ≤ -a * (1 - h ^ 2 / 2) := by
    have hvx : inner ℝ ω v = -(a⁻¹ * inner ℝ ω x) := by
      rw [hv, steinInwardRadialDirection, inner_neg_right, real_inner_smul_right, ha]
    rw [hvx] at hinnerv
    have hstep : a⁻¹ * inner ℝ ω x < h ^ 2 / 2 - 1 := by linarith
    have hmul := mul_lt_mul_of_pos_left hstep hxpos
    rw [← mul_assoc, mul_inv_cancel₀ hxpos.ne', one_mul] at hmul
    have heq : a * (h ^ 2 / 2 - 1) = -a * (1 - h ^ 2 / 2) := by ring
    linarith [hmul, heq.le, heq.ge]
  have hnormsq : ‖x + t • ω‖ ^ 2 = a ^ 2 + t ^ 2 + 2 * t * inner ℝ ω x := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, hωnorm, mul_one,
      real_inner_smul_right, sq_abs, ha]
    have hcomm : inner ℝ x ω = inner ℝ ω x := real_inner_comm _ _
    rw [hcomm]
    ring
  have hδeq : a * t * h ^ 2 = δ := by
    rw [hhsq]
    field_simp
  have hupper : ‖x + t • ω‖ ^ 2 ≤ (t - a) ^ 2 + δ := by
    have hstep : 2 * t * inner ℝ ω x ≤ 2 * t * (-a * (1 - h ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hinnerx (by positivity)
    calc ‖x + t • ω‖ ^ 2 = a ^ 2 + t ^ 2 + 2 * t * inner ℝ ω x := hnormsq
      _ ≤ a ^ 2 + t ^ 2 + 2 * t * (-a * (1 - h ^ 2 / 2)) := by linarith
      _ = (t - a) ^ 2 + a * t * h ^ 2 := by ring
      _ = (t - a) ^ 2 + δ := by rw [hδeq]
  have hcs : -a ≤ inner ℝ ω x := by
    have hle := abs_real_inner_le_norm ω x
    rw [hωnorm, one_mul] at hle
    have habs := abs_le.mp hle
    rw [ha]
    exact habs.1
  have hlower : (t - a) ^ 2 ≤ ‖x + t • ω‖ ^ 2 := by
    have hstep : 2 * t * (-a) ≤ 2 * t * inner ℝ ω x :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    calc (t - a) ^ 2 = a ^ 2 + t ^ 2 + 2 * t * (-a) := by ring
      _ ≤ a ^ 2 + t ^ 2 + 2 * t * inner ℝ ω x := by linarith
      _ = ‖x + t • ω‖ ^ 2 := hnormsq.symm
  have hta : tL - δ / 10 ≤ t - a := by
    rw [abs_le] at hclose
    linarith [hclose.1]
  have hta' : t - a ≤ tL + δ / 10 := by
    rw [abs_le] at hclose
    linarith [hclose.2]
  have htapos : 0 < t - a := by
    have h1 : (0 : ℝ) < tL - δ / 10 := by linarith
    linarith
  have hnn : 0 ≤ ‖x + t • ω‖ := norm_nonneg _
  constructor
  · have hsq1 : (tL - δ) ^ 2 ≤ (t - a) ^ 2 := by
      refine pow_le_pow_left₀ (by linarith) ?_ 2
      linarith
    have hsqge : (tL - δ) ^ 2 ≤ ‖x + t • ω‖ ^ 2 := by linarith [hlower, hsq1]
    calc tL - δ = Real.sqrt ((tL - δ) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ Real.sqrt (‖x + t • ω‖ ^ 2) := Real.sqrt_le_sqrt hsqge
      _ = ‖x + t • ω‖ := Real.sqrt_sq hnn
  · have hsq1 : (t - a) ^ 2 ≤ (tL + δ / 10) ^ 2 := pow_le_pow_left₀ htapos.le hta' 2
    have hsq2 : (tL + δ / 10) ^ 2 + δ ≤ (tL + δ) ^ 2 := by nlinarith [htL, hδ]
    have hsqle : ‖x + t • ω‖ ^ 2 ≤ (tL + δ) ^ 2 := by
      linarith [hupper, hsq1, hsq2]
    calc ‖x + t • ω‖ = Real.sqrt (‖x + t • ω‖ ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((tL + δ) ^ 2) := Real.sqrt_le_sqrt hsqle
      _ = tL + δ := Real.sqrt_sq (by linarith)

/-- **(3.4) of BRS.**  At radii `|x| ≈ t - t_L` the spherical average of the
annulus test function is bounded below by the measure of a tangential cap of
chordal radius `√(δ/(|x| t))`. -/
theorem le_sphericalAverage_annulusTest {d : ℕ} (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ tL δ t : ℝ, 0 < δ → δ ≤ 1 → 1 ≤ tL → tL ≤ 2 → 1 ≤ t →
      t ≤ 2 → ∀ x : Euclidean d, 4 * δ ≤ ‖x‖ * t →
        |t - ‖x‖ - tL| ≤ δ / 10 →
          ENNReal.ofReal (c * Real.sqrt (δ / (‖x‖ * t)) ^ (d - 1)) ≤
            ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t
              (brsAnnulusTest d tL δ) x‖ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨c₀, hc₀pos, hc₀top, hcap⟩ := exists_stein_unitSurfaceMeasure_cap_ge_power n
  have hmass : 0 < surfaceMass (n + 1) := surfaceMass_pos (by omega)
  set c : ℝ := c₀.toReal / surfaceMass (n + 1) with hc
  have hc₀real : 0 < c₀.toReal := ENNReal.toReal_pos hc₀pos.ne' hc₀top
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  refine ⟨c, hcpos, ?_⟩
  intro tL δ t hδ hδ1 htL htL2 ht1 ht2 x hδa hclose
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hxpos : 0 < ‖x‖ := by
    rcases lt_or_ge 0 ‖x‖ with h | h
    · exact h
    · exfalso
      have h0 : ‖x‖ = 0 := le_antisymm h (norm_nonneg _)
      rw [h0] at hδa
      simp only [zero_mul] at hδa
      linarith
  set a : ℝ := ‖x‖ with ha
  have hat : 0 < a * t := mul_pos hxpos htpos
  -- the cap radius
  set h : ℝ := Real.sqrt (δ / (a * t)) with hh
  have hhpos : 0 < h := by
    rw [hh]
    exact Real.sqrt_pos.mpr (div_pos hδ hat)
  have hhsq : h ^ 2 = δ / (a * t) := by
    rw [hh, Real.sq_sqrt (by positivity)]
  have hhhalf : h ≤ 1 / 2 := by
    have hle : δ / (a * t) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hat (by norm_num)]
      linarith
    have := Real.sqrt_le_sqrt hle
    rw [hh]
    refine le_trans this (le_of_eq ?_)
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  -- the inward cap
  set v : Euclidean (n + 1) := steinInwardRadialDirection x with hv
  have hvnorm : ‖v‖ = 1 := norm_steinInwardRadialDirection hxpos
  set A : Set (Metric.sphere (0 : Euclidean (n + 1)) 1) :=
    steinSphericalCap (n + 1) v h with hA
  have hAmeas : MeasurableSet A := measurableSet_steinSphericalCap _ _ _
  -- the annulus is hit by the whole cap
  have hone : ∀ ω ∈ A, (Icc (tL - δ) (tL + δ)).indicator (fun _ => (1 : ℝ))
      ‖x + t • (ω : Euclidean (n + 1))‖ = 1 := by
    intro ω hω
    have hωnorm : ‖(ω : Euclidean (n + 1))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have hdist : dist ((ω : Euclidean (n + 1))) v < h := hω
    exact Set.indicator_of_mem
      (mem_annulus_of_mem_inwardCap hδ hδ1 htL hxpos htpos hclose hωnorm hdist) _
  -- the average dominates the cap fraction
  have hgmeas : Measurable (fun y : Euclidean (n + 1) =>
      (Icc (tL - δ) (tL + δ)).indicator (fun _ => (1 : ℝ)) ‖y‖) :=
    (measurable_const.indicator measurableSet_Icc).comp continuous_norm.measurable
  have hgb : ∀ y : Euclidean (n + 1),
      ‖(Icc (tL - δ) (tL + δ)).indicator (fun _ => (1 : ℝ)) ‖y‖‖ ≤ 1 := by
    intro y
    by_cases hmem : ‖y‖ ∈ Icc (tL - δ) (tL + δ)
    · rw [Set.indicator_of_mem hmem]
      norm_num
    · rw [Set.indicator_of_notMem hmem]
      norm_num
  have hint := stein_integrable_sphere_comp_of_bounded_measurable hgmeas hgb t x
  have hnonneg : ∀ ω : Metric.sphere (0 : Euclidean (n + 1)) 1,
      0 ≤ (Icc (tL - δ) (tL + δ)).indicator (fun _ => (1 : ℝ))
        ‖x + t • (ω : Euclidean (n + 1))‖ := by
    intro ω
    by_cases hmem : ‖x + t • (ω : Euclidean (n + 1))‖ ∈ Icc (tL - δ) (tL + δ)
    · rw [Set.indicator_of_mem hmem]
      norm_num
    · rw [Set.indicator_of_notMem hmem]
  have hfrac := stein_cap_fraction_le_ennreal_norm_normalizedSphericalAverage
    (by omega : 0 < n + 1)
    (fun y : Euclidean (n + 1) =>
      (Icc (tL - δ) (tL + δ)).indicator (fun _ => (1 : ℝ)) ‖y‖)
    t x A hAmeas hint hnonneg hone
  have hcapbound := hcap v hvnorm h hhpos hhhalf
  -- the average agrees with the normalized one
  have hbridge : _root_.Spherical.sphericalAverage t (brsAnnulusTest (n + 1) tL δ) x =
      normalizedSphericalAverage (n + 1)
        (fun y : Euclidean (n + 1) =>
          (((Icc (tL - δ) (tL + δ)).indicator (fun _ => (1 : ℝ)) ‖y‖ : ℝ) : ℂ)) t x := by
    rw [_root_.Auto.Spherical.PowerWeights.sphericalAverage_eq_normalizedSphericalAverage]
    congr 1
    funext y
    rw [brsAnnulusTest]
    by_cases hmem : ‖y‖ ∈ Icc (tL - δ) (tL + δ)
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      norm_num
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      norm_num
  rw [hbridge]
  have hstep1 : ENNReal.ofReal (c * h ^ (n + 1 - 1)) =
      c₀ * ENNReal.ofReal (h ^ n) / ENNReal.ofReal (surfaceMass (n + 1)) := by
    have hn : n + 1 - 1 = n := by omega
    rw [hn, hc, div_mul_eq_mul_div, ENNReal.ofReal_div_of_pos hmass,
      ENNReal.ofReal_mul (le_of_lt hc₀real), ENNReal.ofReal_toReal hc₀top]
  calc ENNReal.ofReal (c * h ^ (n + 1 - 1))
      = c₀ * ENNReal.ofReal (h ^ n) / ENNReal.ofReal (surfaceMass (n + 1)) := hstep1
    _ ≤ unitSurfaceMeasure (n + 1) A / ENNReal.ofReal (surfaceMass (n + 1)) :=
        ENNReal.div_le_div_right hcapbound _
    _ ≤ _ := hfrac

/-- An elementary lower bound for a difference of powers: the largest term of
the geometric factorization. -/
theorem mul_pow_le_pow_succ_sub_pow_succ {b c : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b)
    (n : ℕ) : (b - c) * b ^ n ≤ b ^ (n + 1) - c ^ (n + 1) := by
  have hb : 0 ≤ b := le_trans hc hcb
  induction n with
  | zero => simp
  | succ k ih =>
    have hck : 0 ≤ c ^ (k + 1) := pow_nonneg hc _
    have hsplit : b ^ (k + 2) - c ^ (k + 2) =
        b * (b ^ (k + 1) - c ^ (k + 1)) + (b - c) * c ^ (k + 1) := by
      ring
    have hstep : b * ((b - c) * b ^ k) ≤ b * (b ^ (k + 1) - c ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left ih hb
    have hpos : 0 ≤ (b - c) * c ^ (k + 1) :=
      mul_nonneg (by linarith) hck
    calc (b - c) * b ^ (k + 1) = b * ((b - c) * b ^ k) := by ring
      _ ≤ b * (b ^ (k + 1) - c ^ (k + 1)) := hstep
      _ ≤ b * (b ^ (k + 1) - c ^ (k + 1)) + (b - c) * c ^ (k + 1) := by linarith
      _ = b ^ (k + 2) - c ^ (k + 2) := hsplit.symm

/-- **The thin annulus at radius `a` has volume at least `δ a^{d-1}/5`.**  This
is the volume factor of the `ℭ_E(δ,J)` lower bound. -/
theorem volume_radialAnnulus_ge {d : ℕ} (hd : 0 < d) {a δ : ℝ} (hδ : 0 < δ)
    (hδa : δ / 10 ≤ a) :
    ENNReal.ofReal (δ / 5 * a ^ (d - 1)) *
        volume (Metric.ball (0 : Euclidean d) 1) ≤
      volume (radialAnnulusIcc d (a - δ / 10) (a + δ / 10)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hlow : (0 : ℝ) ≤ a - δ / 10 := by linarith
  have hle : a - δ / 10 ≤ a + δ / 10 := by linarith
  rw [volume_radialAnnulusIcc hd hlow hle]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hkey := mul_pow_le_pow_succ_sub_pow_succ hlow hle n
  have hdiff : (a + δ / 10) - (a - δ / 10) = δ / 5 := by ring
  rw [hdiff] at hkey
  have hmono : a ^ n ≤ (a + δ / 10) ^ n := by
    refine pow_le_pow_left₀ (by linarith) (by linarith) n
  have hstep : δ / 5 * a ^ n ≤ δ / 5 * (a + δ / 10) ^ n :=
    mul_le_mul_of_nonneg_left hmono (by linarith)
  simp only [Nat.add_sub_cancel]
  linarith [hkey, hstep]

/-- The annuli attached to `δ`-separated radii are pairwise disjoint. -/
theorem radialAnnulus_disjoint_of_separated {d : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (hsep : δ ≤ |a - b|) :
    Disjoint (radialAnnulusIcc d (a - δ / 10) (a + δ / 10))
      (radialAnnulusIcc d (b - δ / 10) (b + δ / 10)) := by
  refine Set.disjoint_left.mpr fun x hxa hxb => ?_
  have h1 : ‖x‖ ∈ Icc (a - δ / 10) (a + δ / 10) := hxa
  have h2 : ‖x‖ ∈ Icc (b - δ / 10) (b + δ / 10) := hxb
  have hab : |a - b| ≤ δ / 5 := by
    rw [abs_le]
    constructor
    · linarith [h1.1, h1.2, h2.1, h2.2]
    · linarith [h1.1, h1.2, h2.1, h2.2]
  linarith [hsep, hab]

/-- **The union of the separated annuli of Lemma 3.5 is large.** -/
theorem volume_biUnion_annuli_ge {d : ℕ} (hd : 0 < d) {δ L tL : ℝ} (hδ : 0 < δ)
    (hδL : 10 * δ ≤ L) (T : Finset ℝ)
    (hright : ∀ t ∈ T, tL + L / 2 ≤ t ∧ t ≤ tL + L)
    (hsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s|) :
    ENNReal.ofReal ((T.card : ℝ) * (δ / 5 * (L / 2) ^ (d - 1))) *
        volume (Metric.ball (0 : Euclidean d) 1) ≤
      volume (⋃ t ∈ T, radialAnnulusIcc d (t - tL - δ / 10) (t - tL + δ / 10)) := by
  classical
  have hLpos : 0 < L := by linarith
  have hmeas : ∀ t ∈ T,
      MeasurableSet (radialAnnulusIcc d (t - tL - δ / 10) (t - tL + δ / 10)) :=
    fun t _ => measurableSet_radialAnnulusIcc d _ _
  have hdisj : (↑T : Set ℝ).PairwiseDisjoint
      (fun t => radialAnnulusIcc d (t - tL - δ / 10) (t - tL + δ / 10)) := by
    intro t ht s hs hts
    have hsepts : δ ≤ |t - s| := hsep t (by simpa using ht) s (by simpa using hs) hts
    have habs : |(t - tL) - (s - tL)| = |t - s| := by
      congr 1
      ring
    have := radialAnnulus_disjoint_of_separated (d := d) hδ
      (by rw [habs]; exact hsepts)
    exact this
  rw [measure_biUnion_finset hdisj hmeas]
  have hterm : ∀ t ∈ T,
      ENNReal.ofReal (δ / 5 * (L / 2) ^ (d - 1)) *
          volume (Metric.ball (0 : Euclidean d) 1) ≤
        volume (radialAnnulusIcc d (t - tL - δ / 10) (t - tL + δ / 10)) := by
    intro t ht
    obtain ⟨hlow, -⟩ := hright t ht
    have hat : δ / 10 ≤ t - tL := by linarith
    have hmono : (L / 2) ^ (d - 1) ≤ (t - tL) ^ (d - 1) := by
      refine pow_le_pow_left₀ (by linarith) (by linarith) _
    refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      (volume_radialAnnulus_ge hd hδ hat)
    have hδ5 : (0 : ℝ) ≤ δ / 5 := by linarith
    exact mul_le_mul_of_nonneg_left hmono hδ5
  calc ENNReal.ofReal ((T.card : ℝ) * (δ / 5 * (L / 2) ^ (d - 1))) *
        volume (Metric.ball (0 : Euclidean d) 1)
      = (T.card : ℕ) • (ENNReal.ofReal (δ / 5 * (L / 2) ^ (d - 1)) *
          volume (Metric.ball (0 : Euclidean d) 1)) := by
        rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg (T.card)),
          ENNReal.ofReal_natCast, mul_assoc]
    _ = ∑ _t ∈ T, ENNReal.ofReal (δ / 5 * (L / 2) ^ (d - 1)) *
          volume (Metric.ball (0 : Euclidean d) 1) := by
        rw [Finset.sum_const]
    _ ≤ ∑ t ∈ T, volume (radialAnnulusIcc d (t - tL - δ / 10) (t - tL + δ / 10)) :=
        Finset.sum_le_sum hterm

/-- **(3.3) of BRS.**  The `L^q` norm of the maximal function applied to the
annulus test function is bounded below by the entropy of a separated subset of
`E ∩ J` in the right half of `J`. -/
theorem le_eLpNorm_M_annulusTest {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {q : ℝ} (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ L tL : ℝ, 0 < δ → δ ≤ 1 → 10 * δ ≤ L → L ≤ 1 →
      1 ≤ tL → tL + L ≤ 2 → ∀ T : Finset ℝ, (↑T : Set ℝ) ⊆ E →
        (∀ t ∈ T, tL + L / 2 ≤ t ∧ t ≤ tL + L) →
        (∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s|) →
          ENNReal.ofReal (c * Real.sqrt (δ / L) ^ (d - 1)) *
              ENNReal.ofReal ((T.card : ℝ) * δ * L ^ (d - 1)) ^ (1 / q) ≤
            eLpNorm (M E (brsAnnulusTest d tL δ)) (ENNReal.ofReal q) volume := by
  classical
  obtain ⟨c₀, hc₀, hcap⟩ := le_sphericalAverage_annulusTest hd
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  have hVeq : volume (Metric.ball (0 : Euclidean d) 1) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hVtop]
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ (d - 1) := by positivity
  refine ⟨c₀ / 2 ^ (d - 1) * (V / (5 * 2 ^ (d - 1))) ^ (1 / q), ?_, ?_⟩
  · have h1 : (0 : ℝ) < V / (5 * 2 ^ (d - 1)) := by positivity
    have h2 : (0 : ℝ) < (V / (5 * 2 ^ (d - 1))) ^ (1 / q) :=
      Real.rpow_pos_of_pos h1 _
    positivity
  intro δ L tL hδ hδ1 hδL hL1 htL htLL T hTE hright hsep
  have hLpos : 0 < L := by linarith
  have hδLpos : 0 < δ / L := div_pos hδ hLpos
  have hsq : 0 ≤ Real.sqrt (δ / L) := Real.sqrt_nonneg _
  set S : Set (Euclidean d) :=
    ⋃ t ∈ T, radialAnnulusIcc d (t - tL - δ / 10) (t - tL + δ / 10) with hS
  have hSmeas : MeasurableSet S := by
    rw [hS]
    exact Finset.measurableSet_biUnion _
      fun t _ => measurableSet_radialAnnulusIcc d _ _
  -- the maximal function is large on `S`
  have hlarge : ∀ x ∈ S,
      ENNReal.ofReal (c₀ / 2 ^ (d - 1) * Real.sqrt (δ / L) ^ (d - 1)) ≤
        M E (brsAnnulusTest d tL δ) x := by
    intro x hx
    obtain ⟨t, htT, hxt⟩ : ∃ t ∈ T,
        x ∈ radialAnnulusIcc d (t - tL - δ / 10) (t - tL + δ / 10) := by
      rw [hS] at hx
      simpa only [Set.mem_iUnion, exists_prop] using hx
    obtain ⟨hlow, hhigh⟩ := hright t htT
    have htE : t ∈ E := hTE htT
    have htIcc : t ∈ Icc (1 : ℝ) 2 := hE htE
    have hxmem : ‖x‖ ∈ Icc (t - tL - δ / 10) (t - tL + δ / 10) := hxt
    have hxlow : t - tL - δ / 10 ≤ ‖x‖ := hxmem.1
    have hxhigh : ‖x‖ ≤ t - tL + δ / 10 := hxmem.2
    have hclose : |t - ‖x‖ - tL| ≤ δ / 10 := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have hxpos : 4 * δ ≤ ‖x‖ * t := by
      have h1 : L / 2 - δ / 10 ≤ ‖x‖ := by linarith
      have h2 : (1 : ℝ) ≤ t := htIcc.1
      have h3 : 4 * δ ≤ L / 2 - δ / 10 := by linarith
      nlinarith [h1, h2, h3, hδ]
    have havg := hcap tL δ t hδ hδ1 htL (by linarith) htIcc.1 htIcc.2 x hxpos hclose
    -- compare the cap radii
    have hxup : ‖x‖ * t ≤ 4 * L := by
      have h1 : ‖x‖ ≤ L + δ / 10 := by linarith
      have h2 : t ≤ 2 := htIcc.2
      have h3 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
      nlinarith [h1, h2, h3, hδ, hδL]
    have hratio : δ / (4 * L) ≤ δ / (‖x‖ * t) := by
      refine div_le_div_of_nonneg_left hδ.le ?_ hxup
      have h1 : (0 : ℝ) < ‖x‖ * t := by
        nlinarith [hxpos, hδ]
      exact h1
    have hsqrt : Real.sqrt (δ / L) / 2 ≤ Real.sqrt (δ / (‖x‖ * t)) := by
      have hhalf : Real.sqrt (δ / (4 * L)) = Real.sqrt (δ / L) / 2 := by
        rw [show δ / (4 * L) = (δ / L) * (1 / 4) by ring, Real.sqrt_mul hδLpos.le,
          show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        ring
      rw [← hhalf]
      exact Real.sqrt_le_sqrt hratio
    refine le_trans (le_trans (ENNReal.ofReal_le_ofReal ?_) havg) ?_
    · have hmono : (Real.sqrt (δ / L) / 2) ^ (d - 1) ≤
          Real.sqrt (δ / (‖x‖ * t)) ^ (d - 1) :=
        pow_le_pow_left₀ (by positivity) hsqrt _
      calc c₀ / 2 ^ (d - 1) * Real.sqrt (δ / L) ^ (d - 1)
          = c₀ * (Real.sqrt (δ / L) / 2) ^ (d - 1) := by
            rw [div_pow]
            ring
        _ ≤ c₀ * Real.sqrt (δ / (‖x‖ * t)) ^ (d - 1) :=
            mul_le_mul_of_nonneg_left hmono hc₀.le
    · unfold M _root_.Spherical.restrictedSphericalMaximal
      have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one htIcc.1
      exact le_iSup_of_le t (le_iSup_of_le ⟨htE, htpos⟩ le_rfl)
  have hlow := le_eLpNorm_of_const_le_on hSmeas
    (by positivity : (0 : ℝ) ≤ c₀ / 2 ^ (d - 1) * Real.sqrt (δ / L) ^ (d - 1))
    hlarge hq
  have hB : (0 : ℝ) ≤ V / (5 * 2 ^ (d - 1)) := by
    have h1 : (0 : ℝ) < 5 * 2 ^ (d - 1) := by positivity
    exact div_nonneg hVpos.le h1.le
  have hN : (0 : ℝ) ≤ (T.card : ℝ) * δ * L ^ (d - 1) := by
    have h1 : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ L ^ (d - 1) := pow_nonneg hLpos.le _
    have h3 : (0 : ℝ) ≤ (T.card : ℝ) * δ := mul_nonneg h1 hδ.le
    exact mul_nonneg h3 h2
  have hA : (0 : ℝ) ≤ c₀ / 2 ^ (d - 1) * Real.sqrt (δ / L) ^ (d - 1) := by
    have h1 : (0 : ℝ) ≤ c₀ / 2 ^ (d - 1) := div_nonneg hc₀.le hpow2.le
    exact mul_nonneg h1 (pow_nonneg hsq _)
  have hqinv : (0 : ℝ) ≤ 1 / q := by positivity
  have hvol : ENNReal.ofReal ((V / (5 * 2 ^ (d - 1))) *
      ((T.card : ℝ) * δ * L ^ (d - 1))) ≤ volume S := by
    have hcard : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
    have hinner : (0 : ℝ) ≤ δ / 5 * (L / 2) ^ (d - 1) := by
      have h1 : (0 : ℝ) ≤ δ / 5 := by linarith
      have h2 : (0 : ℝ) ≤ (L / 2) ^ (d - 1) := pow_nonneg (by linarith) _
      exact mul_nonneg h1 h2
    refine le_trans (le_of_eq ?_) (volume_biUnion_annuli_ge hd hδ hδL T hright hsep)
    rw [hVeq, ← ENNReal.ofReal_mul (mul_nonneg hcard hinner)]
    congr 1
    rw [div_pow]
    ring
  have hconst : ENNReal.ofReal (c₀ / 2 ^ (d - 1) *
        (V / (5 * 2 ^ (d - 1))) ^ (1 / q) * Real.sqrt (δ / L) ^ (d - 1)) *
        ENNReal.ofReal ((T.card : ℝ) * δ * L ^ (d - 1)) ^ (1 / q) =
      ENNReal.ofReal (c₀ / 2 ^ (d - 1) * Real.sqrt (δ / L) ^ (d - 1)) *
        ENNReal.ofReal ((V / (5 * 2 ^ (d - 1))) *
          ((T.card : ℝ) * δ * L ^ (d - 1))) ^ (1 / q) := by
    rw [show c₀ / 2 ^ (d - 1) * (V / (5 * 2 ^ (d - 1))) ^ (1 / q) *
          Real.sqrt (δ / L) ^ (d - 1) =
        (c₀ / 2 ^ (d - 1) * Real.sqrt (δ / L) ^ (d - 1)) *
          (V / (5 * 2 ^ (d - 1))) ^ (1 / q) by ring,
      ENNReal.ofReal_mul hA, mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_rpow_of_nonneg hB hqinv,
      ← ENNReal.mul_rpow_of_nonneg _ _ hqinv, ← ENNReal.ofReal_mul hB]
  calc ENNReal.ofReal (c₀ / 2 ^ (d - 1) *
        (V / (5 * 2 ^ (d - 1))) ^ (1 / q) * Real.sqrt (δ / L) ^ (d - 1)) *
        ENNReal.ofReal ((T.card : ℝ) * δ * L ^ (d - 1)) ^ (1 / q)
      = ENNReal.ofReal (c₀ / 2 ^ (d - 1) * Real.sqrt (δ / L) ^ (d - 1)) *
          ENNReal.ofReal ((V / (5 * 2 ^ (d - 1))) *
            ((T.card : ℝ) * δ * L ^ (d - 1))) ^ (1 / q) := hconst
    _ ≤ ENNReal.ofReal (c₀ / 2 ^ (d - 1) * Real.sqrt (δ / L) ^ (d - 1)) *
          volume S ^ (1 / q) :=
        mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hvol (by positivity))
    _ ≤ eLpNorm (M E (brsAnnulusTest d tL δ)) (ENNReal.ofReal q) volume := hlow

/-- The square root, as a real power. -/
theorem sqrt_pow_eq_rpow {d : ℕ} (hd : 0 < d) {z : ℝ} (hz : 0 ≤ z) :
    Real.sqrt z ^ (d - 1) = z ^ (((d : ℝ) - 1) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (z ^ (1 / 2 : ℝ)) (d - 1),
    ← Real.rpow_mul hz]
  congr 1
  have h1 : (1 : ℕ) ≤ d := hd
  push_cast [Nat.cast_sub h1]
  ring

/-- The `L^p` norm of the annulus test function is at most `(W δ)^{1/p}`. -/
theorem eLpNorm_brsAnnulusTest_le {d : ℕ} (hd : 0 < d) {tL δ : ℝ} (htL : 1 ≤ tL)
    (htL2 : tL ≤ 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {p : ℝ} (hp : 0 < p) :
    eLpNorm (brsAnnulusTest d tL δ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((2 * d * 3 ^ (d - 1) * δ *
        (volume (Metric.ball (0 : Euclidean d) 1)).toReal) ^ (1 / p)) := by
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  have hVeq : volume (Metric.ball (0 : Euclidean d) 1) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hVtop]
  have hδW : (0 : ℝ) ≤ 2 * d * 3 ^ (d - 1) * δ := by positivity
  rw [eLpNorm_brsAnnulusTest d tL δ hp]
  refine le_trans (ENNReal.rpow_le_rpow (volume_thin_shell_le hd htL htL2 hδ hδ1)
    (by positivity)) (le_of_eq ?_)
  rw [hVeq, ← ENNReal.ofReal_mul hδW,
    ← ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hδW hVpos.le) (by positivity)]

/-- **Lemma 3.5 of BRS, the entropy bound.**  A radial `L^p → L^q` bound forces
the quantity `ℭ_E(δ,J) = N(E ∩ J,δ)^{1/q} |J|^{-(d-1)(1/2-1/q)} δ^{(d-1)/2+1/q-1/p}`
to stay bounded, for every separated family in the right half of `J`. -/
theorem entropy_bound_of_hasRadialStrongType {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : HasRadialStrongType d E (ENNReal.ofReal p) (ENNReal.ofReal q)) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ L tL : ℝ, 0 < δ → δ ≤ 1 → 10 * δ ≤ L → L ≤ 1 →
      1 ≤ tL → tL + L ≤ 2 → ∀ T : Finset ℝ, (↑T : Set ℝ) ⊆ E →
        (∀ t ∈ T, tL + L / 2 ≤ t ∧ t ≤ tL + L) →
        (∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s|) →
          (T.card : ℝ) ^ (1 / q) * L ^ (-(((d : ℝ) - 1) * (1 / 2 - 1 / q))) *
              δ ^ (((d : ℝ) - 1) / 2 + 1 / q - 1 / p) ≤ K := by
  obtain ⟨C, hC, hbound⟩ := h
  obtain ⟨c, hc, hlow⟩ := le_eLpNorm_M_annulusTest hd hE hq
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  set W : ℝ := 2 * d * 3 ^ (d - 1) * V with hW
  have hWpos : 0 < W := by
    rw [hW]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  refine ⟨C * W ^ (1 / p) / c, div_pos (mul_pos hC (Real.rpow_pos_of_pos hWpos _)) hc,
    ?_⟩
  intro δ L tL hδ hδ1 hδL hL1 htL htLL T hTE hright hsep
  have hLpos : 0 < L := by linarith
  have hcard : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  have hδLpos : 0 < δ / L := div_pos hδ hLpos
  -- the operator bound applied to the test function
  have hmem := memLp_brsAnnulusTest hd htL (by linarith) hδ hδ1 hp
  have hrad := isNormRadial_brsAnnulusTest d tL δ
  have hup := (hbound _ hmem hrad).2
  have hnorm := eLpNorm_brsAnnulusTest_le hd htL (by linarith) hδ hδ1 hp
  have hlowδ := hlow δ L tL hδ hδ1 hδL hL1 htL htLL T hTE hright hsep
  -- chain the two bounds
  have hchain : ENNReal.ofReal (c * Real.sqrt (δ / L) ^ (d - 1)) *
      ENNReal.ofReal ((T.card : ℝ) * δ * L ^ (d - 1)) ^ (1 / q) ≤
      ENNReal.ofReal (C * (W * δ) ^ (1 / p)) := by
    refine le_trans hlowδ (le_trans hup ?_)
    have hstep : ENNReal.ofReal C *
        eLpNorm (brsAnnulusTest d tL δ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          ENNReal.ofReal ((2 * d * 3 ^ (d - 1) * δ * V) ^ (1 / p)) :=
      mul_le_mul' le_rfl hnorm
    refine le_trans hstep (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hC.le]
    congr 1
    congr 1
    rw [hW]
    ring
  -- pass to real numbers
  have hLHS : ENNReal.ofReal (c * Real.sqrt (δ / L) ^ (d - 1)) *
      ENNReal.ofReal ((T.card : ℝ) * δ * L ^ (d - 1)) ^ (1 / q) =
      ENNReal.ofReal (c * Real.sqrt (δ / L) ^ (d - 1) *
        ((T.card : ℝ) * δ * L ^ (d - 1)) ^ (1 / q)) := by
    have hn : (0 : ℝ) ≤ (T.card : ℝ) * δ * L ^ (d - 1) := by
      have h1 : (0 : ℝ) ≤ (T.card : ℝ) * δ := mul_nonneg hcard hδ.le
      exact mul_nonneg h1 (pow_nonneg hLpos.le _)
    have ha : (0 : ℝ) ≤ c * Real.sqrt (δ / L) ^ (d - 1) :=
      mul_nonneg hc.le (pow_nonneg (Real.sqrt_nonneg _) _)
    rw [ENNReal.ofReal_mul ha,
      ← ENNReal.ofReal_rpow_of_nonneg hn (by positivity : (0 : ℝ) ≤ 1 / q)]
  rw [hLHS] at hchain
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
  -- rewrite both sides in the `ℭ` form
  have hsqrt : Real.sqrt (δ / L) ^ (d - 1) =
      δ ^ (((d : ℝ) - 1) / 2) * L ^ (-((((d : ℝ) - 1) / 2))) := by
    rw [sqrt_pow_eq_rpow hd hδLpos.le, Real.div_rpow hδ.le hLpos.le,
      Real.rpow_neg hLpos.le, div_eq_mul_inv]
  have hprod : ((T.card : ℝ) * δ * L ^ (d - 1)) ^ (1 / q) =
      (T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) * L ^ ((((d : ℝ) - 1)) / q) := by
    have hLd : (L : ℝ) ^ (d - 1) = L ^ ((d : ℝ) - 1) := by
      rw [← Real.rpow_natCast L (d - 1)]
      congr 1
      have h1 : (1 : ℕ) ≤ d := hd
      push_cast [Nat.cast_sub h1]
      ring
    rw [hLd, Real.mul_rpow (mul_nonneg hcard hδ.le)
      (Real.rpow_nonneg hLpos.le _), Real.mul_rpow hcard hδ.le,
      ← Real.rpow_mul hLpos.le]
    congr 2
    ring
  have hcollect : c * (δ ^ (((d : ℝ) - 1) / 2) * L ^ (-((((d : ℝ) - 1) / 2)))) *
      ((T.card : ℝ) ^ (1 / q) * δ ^ (1 / q) * L ^ ((((d : ℝ) - 1)) / q)) =
      c * ((T.card : ℝ) ^ (1 / q) *
        L ^ (-(((d : ℝ) - 1) * (1 / 2 - 1 / q))) *
        δ ^ (((d : ℝ) - 1) / 2 + 1 / q)) := by
    rw [show -(((d : ℝ) - 1) * (1 / 2 - 1 / q)) =
        -((((d : ℝ) - 1) / 2)) + (((d : ℝ) - 1)) / q by ring,
      Real.rpow_add hLpos, Real.rpow_add hδ]
    ring
  rw [hsqrt, hprod, hcollect] at hreal
  -- divide by `δ^{1/p}`
  have hδp : (0 : ℝ) < δ ^ (1 / p) := Real.rpow_pos_of_pos hδ _
  have hsplit : (W * δ) ^ (1 / p) = W ^ (1 / p) * δ ^ (1 / p) :=
    Real.mul_rpow hWpos.le hδ.le
  rw [hsplit] at hreal
  rw [le_div_iff₀ hc]
  have hδsplit : δ ^ (((d : ℝ) - 1) / 2 + 1 / q - 1 / p) * δ ^ (1 / p) =
      δ ^ (((d : ℝ) - 1) / 2 + 1 / q) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  calc (T.card : ℝ) ^ (1 / q) * L ^ (-(((d : ℝ) - 1) * (1 / 2 - 1 / q))) *
        δ ^ (((d : ℝ) - 1) / 2 + 1 / q - 1 / p) * c
      = c * ((T.card : ℝ) ^ (1 / q) * L ^ (-(((d : ℝ) - 1) * (1 / 2 - 1 / q))) *
          δ ^ (((d : ℝ) - 1) / 2 + 1 / q)) / δ ^ (1 / p) := by
        rw [← hδsplit]
        field_simp
    _ ≤ (C * (W ^ (1 / p) * δ ^ (1 / p))) / δ ^ (1 / p) := by
        gcongr
    _ = C * W ^ (1 / p) := by
        field_simp

/-- Splitting a quotient power against a power of the denominator. -/
theorem div_rpow_mul_rpow {x y s e : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    (x / y) ^ s * y ^ e = x ^ s * y ^ (e - s) := by
  rw [Real.div_rpow hx hy.le, Real.rpow_sub hy, div_mul_eq_mul_div, mul_div_assoc]

/-- **The per-annulus contribution is monotone in the radius.**  For `q ≥ 2`
the product of the `q`-th power of the cap bound `(δ/a)^{(d-1)/2}` with the
annulus volume `a^{d-1} δ` is nonincreasing in `a`, so the smallest
contribution comes from the largest radius `a = |J|`.  This is what removes
any restriction to the right half of `J`. -/
theorem annulus_contribution_mono {d : ℕ} (hd : 0 < d) {q δ a L : ℝ}
    (hq2 : 2 ≤ q) (hδ : 0 < δ) (ha : 0 < a) (haL : a ≤ L) :
    (δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) ≤
      (δ / a) ^ (q * ((d : ℝ) - 1) / 2) * a ^ ((d : ℝ) - 1) := by
  have hLpos : 0 < L := lt_of_lt_of_le ha haL
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hes : ((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2 ≤ 0 := by
    nlinarith [hd1, hq2]
  rw [div_rpow_mul_rpow hδ.le hLpos, div_rpow_mul_rpow hδ.le ha]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hδ.le _)
  exact Real.rpow_le_rpow_of_nonpos ha haL hes

/-- The cap bound and the annulus volume, combined at a single radius. -/
theorem annulus_contribution_ge {d : ℕ} (hd : 0 < d) {q δ a L : ℝ}
    (hq2 : 2 ≤ q) (hδ : 0 < δ) (ha : 0 < a) (haL : a ≤ L) {c : ℝ} (hc : 0 ≤ c) :
    c * ((δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1)) ≤
      c * ((δ / a) ^ (q * ((d : ℝ) - 1) / 2) * a ^ ((d : ℝ) - 1)) :=
  mul_le_mul_of_nonneg_left (annulus_contribution_mono hd hq2 hδ ha haL) hc

/-- A natural power of a positive real, as a real power. -/
theorem pow_eq_rpow_natCast_sub_one {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    a ^ (d - 1) = a ^ ((d : ℝ) - 1) := by
  rw [← Real.rpow_natCast a (d - 1)]
  congr 1
  have h1 : (1 : ℕ) ≤ d := hd
  push_cast [Nat.cast_sub h1]
  ring

/-- **The per-annulus contribution to the `q`-th power of the norm.** -/
theorem le_setLIntegral_M_annulusTest {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {q : ℝ} (hq2 : 2 ≤ q) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hcap : ∀ tL δ t : ℝ, 0 < δ → δ ≤ 1 → 1 ≤ tL → tL ≤ 2 → 1 ≤ t → t ≤ 2 →
      ∀ x : Euclidean d, 4 * δ ≤ ‖x‖ * t → |t - ‖x‖ - tL| ≤ δ / 10 →
        ENNReal.ofReal (c₀ * Real.sqrt (δ / (‖x‖ * t)) ^ (d - 1)) ≤
          ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t
            (brsAnnulusTest d tL δ) x‖)
    {δ L tL : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : 10 * δ ≤ L) (hL1 : L ≤ 1)
    (htL : 1 ≤ tL) (htLL : tL + L ≤ 2) {t : ℝ} (htE : t ∈ E)
    (hta : tL + 5 * δ ≤ t) (htb : t ≤ tL + L) :
    ENNReal.ofReal (c₀ ^ q / 5 *
        (volume (Metric.ball (0 : Euclidean d) 1)).toReal *
        (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) *
        ((δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) * δ)) ≤
      ∫⁻ x in radialAnnulusIcc d (t - tL - δ / 10) (t - tL + δ / 10),
        ‖M E (brsAnnulusTest d tL δ) x‖ₑ ^ q := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hq2
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hde : (0 : ℝ) ≤ ((d : ℝ) - 1) / 2 := by linarith
  have hLpos : 0 < L := by linarith
  have htIcc : t ∈ Icc (1 : ℝ) 2 := hE htE
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one htIcc.1
  set a : ℝ := t - tL with ha
  have hapos : 5 * δ ≤ a := by
    rw [ha]
    linarith
  have haL : a ≤ L := by
    rw [ha]
    linarith
  have ha0 : 0 < a := by linarith
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  have hVeq : volume (Metric.ball (0 : Euclidean d) 1) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hVtop]
  -- the pointwise lower bound on the annulus
  have hpoint : ∀ x ∈ radialAnnulusIcc d (a - δ / 10) (a + δ / 10),
      ENNReal.ofReal (c₀ ^ q * (δ / (4 * a)) ^ (q * ((d : ℝ) - 1) / 2)) ≤
        ‖M E (brsAnnulusTest d tL δ) x‖ₑ ^ q := by
    intro x hx
    have hxmem : ‖x‖ ∈ Icc (a - δ / 10) (a + δ / 10) := hx
    have hxlow : a - δ / 10 ≤ ‖x‖ := hxmem.1
    have hxhigh : ‖x‖ ≤ a + δ / 10 := hxmem.2
    have hxpos : 0 < ‖x‖ := by linarith
    have hclose : |t - ‖x‖ - tL| ≤ δ / 10 := by
      rw [abs_le]
      constructor
      · rw [ha] at hxhigh
        linarith
      · rw [ha] at hxlow
        linarith
    have h4δ : 4 * δ ≤ ‖x‖ * t := by
      have h1 : 4 * δ ≤ ‖x‖ := by linarith
      nlinarith [htIcc.1, hxpos]
    have havg := hcap tL δ t hδ hδ1 htL (by linarith) htIcc.1 htIcc.2 x h4δ hclose
    -- the maximal function dominates the single average
    have hM : ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t
        (brsAnnulusTest d tL δ) x‖ ≤ M E (brsAnnulusTest d tL δ) x := by
      unfold M _root_.Spherical.restrictedSphericalMaximal
      exact le_iSup_of_le t (le_iSup_of_le ⟨htE, htpos⟩ le_rfl)
    have hxt : ‖x‖ * t ≤ 4 * a := by
      have h1 : ‖x‖ ≤ 2 * a := by linarith
      nlinarith [htIcc.2, hxpos, ha0]
    have hratio : δ / (4 * a) ≤ δ / (‖x‖ * t) := by
      refine div_le_div_of_nonneg_left hδ.le ?_ hxt
      nlinarith [h4δ, hδ]
    have hbase : ENNReal.ofReal (c₀ * (δ / (4 * a)) ^ (((d : ℝ) - 1) / 2)) ≤
        ‖M E (brsAnnulusTest d tL δ) x‖ₑ := by
      rw [enorm_eq_self]
      refine le_trans (le_trans (ENNReal.ofReal_le_ofReal ?_) havg) hM
      rw [sqrt_pow_eq_rpow hd (by positivity : (0:ℝ) ≤ δ / (‖x‖ * t))]
      refine mul_le_mul_of_nonneg_left ?_ hc₀.le
      exact Real.rpow_le_rpow (by positivity) hratio hde
    calc ENNReal.ofReal (c₀ ^ q * (δ / (4 * a)) ^ (q * ((d : ℝ) - 1) / 2))
        = (ENNReal.ofReal (c₀ * (δ / (4 * a)) ^ (((d : ℝ) - 1) / 2))) ^ q := by
          rw [ENNReal.ofReal_rpow_of_pos
            (mul_pos hc₀ (Real.rpow_pos_of_pos (by positivity) _))]
          congr 1
          rw [Real.mul_rpow hc₀.le (Real.rpow_nonneg (by positivity) _),
            ← Real.rpow_mul (by positivity)]
          congr 2
          ring
      _ ≤ ‖M E (brsAnnulusTest d tL δ) x‖ₑ ^ q :=
          ENNReal.rpow_le_rpow hbase hq0.le
  -- integrate the pointwise bound
  have hvol := volume_radialAnnulus_ge hd hδ (by linarith : δ / 10 ≤ a)
  calc ENNReal.ofReal (c₀ ^ q / 5 * V * (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) *
        ((δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) * δ))
      ≤ ENNReal.ofReal (c₀ ^ q * (δ / (4 * a)) ^ (q * ((d : ℝ) - 1) / 2)) *
          ENNReal.ofReal (δ / 5 * a ^ (d - 1)) * ENNReal.ofReal V := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hsplit : (δ / (4 * a)) ^ (q * ((d : ℝ) - 1) / 2) =
            (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) *
              (δ / a) ^ (q * ((d : ℝ) - 1) / 2) := by
          rw [show δ / (4 * a) = (1 / 4) * (δ / a) by ring,
            Real.mul_rpow (by norm_num) (by positivity)]
          congr 1
          rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num,
            ← Real.rpow_neg_one (4 : ℝ), ← Real.rpow_mul (by norm_num)]
          congr 1
          ring
        have hmono := annulus_contribution_mono hd hq2 hδ ha0 haL
        have hpowa : a ^ (d - 1) = a ^ ((d : ℝ) - 1) :=
          pow_eq_rpow_natCast_sub_one hd ha0
        rw [hsplit, hpowa]
        have hfac : (0 : ℝ) ≤ c₀ ^ q / 5 * V *
            (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) * δ := by positivity
        nlinarith [hmono, hfac, mul_le_mul_of_nonneg_left hmono hfac]
    _ = ENNReal.ofReal (c₀ ^ q * (δ / (4 * a)) ^ (q * ((d : ℝ) - 1) / 2)) *
          (ENNReal.ofReal (δ / 5 * a ^ (d - 1)) *
            volume (Metric.ball (0 : Euclidean d) 1)) := by
        rw [hVeq, mul_assoc]
    _ ≤ ENNReal.ofReal (c₀ ^ q * (δ / (4 * a)) ^ (q * ((d : ℝ) - 1) / 2)) *
          volume (radialAnnulusIcc d (a - δ / 10) (a + δ / 10)) :=
        mul_le_mul' le_rfl hvol
    _ = ∫⁻ _x in radialAnnulusIcc d (a - δ / 10) (a + δ / 10),
          ENNReal.ofReal (c₀ ^ q * (δ / (4 * a)) ^ (q * ((d : ℝ) - 1) / 2)) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in radialAnnulusIcc d (a - δ / 10) (a + δ / 10),
          ‖M E (brsAnnulusTest d tL δ) x‖ₑ ^ q :=
        setLIntegral_mono' (measurableSet_radialAnnulusIcc d _ _) hpoint

/-- **(3.3) of BRS, without the right-half restriction.**  Every `δ`-separated
family of dilations in `J`, away from the left endpoint, contributes to the
`q`-th power of the norm of the maximal function. -/
theorem le_eLpNorm_M_annulusTest_general {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {q : ℝ} (hq2 : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ L tL : ℝ, 0 < δ → δ ≤ 1 → 10 * δ ≤ L → L ≤ 1 →
      1 ≤ tL → tL + L ≤ 2 → ∀ T : Finset ℝ, (↑T : Set ℝ) ⊆ E →
        (∀ t ∈ T, tL + 5 * δ ≤ t ∧ t ≤ tL + L) →
        (∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s|) →
          ENNReal.ofReal (c * (T.card : ℝ) *
              ((δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) * δ)) ≤
            eLpNorm (M E (brsAnnulusTest d tL δ)) (ENNReal.ofReal q) volume ^ q := by
  classical
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hq2
  obtain ⟨c₀, hc₀, hcap⟩ := le_sphericalAverage_annulusTest hd
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  refine ⟨c₀ ^ q / 5 * V * (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)), ?_, ?_⟩
  · have h1 : (0 : ℝ) < c₀ ^ q := Real.rpow_pos_of_pos hc₀ _
    have h2 : (0 : ℝ) < (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    positivity
  intro δ L tL hδ hδ1 hδL hL1 htL htLL T hTE hrange hsep
  have hLpos : 0 < L := by linarith
  set F : Euclidean d → ENNReal := M E (brsAnnulusTest d tL δ) with hF
  set A : ℝ → Set (Euclidean d) :=
    fun t => radialAnnulusIcc d (t - tL - δ / 10) (t - tL + δ / 10) with hA
  have hmeas : ∀ t ∈ T, MeasurableSet (A t) :=
    fun t _ => measurableSet_radialAnnulusIcc d _ _
  have hdisj : (↑T : Set ℝ).PairwiseDisjoint A := by
    intro t ht s hs hts
    have hsepts : δ ≤ |t - s| := hsep t (by simpa using ht) s (by simpa using hs) hts
    have habs : |(t - tL) - (s - tL)| = |t - s| := by
      congr 1
      ring
    exact radialAnnulus_disjoint_of_separated (d := d) hδ (by rw [habs]; exact hsepts)
  -- the norm as an integral
  have hnorm : eLpNorm F (ENNReal.ofReal q) volume ^ q = ∫⁻ x, ‖F x‖ₑ ^ q := by
    have hq0' : ENNReal.ofReal q ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero]
      exact not_le.mpr hq0
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
  rw [hnorm]
  -- restrict to the union of the annuli
  have hunion : (∫⁻ x in ⋃ t ∈ T, A t, ‖F x‖ₑ ^ q) ≤ ∫⁻ x, ‖F x‖ₑ ^ q :=
    lintegral_mono' Measure.restrict_le_self fun _ => le_rfl
  refine le_trans ?_ hunion
  rw [lintegral_biUnion_finset hdisj hmeas]
  -- each annulus contributes the same amount
  have hterm : ∀ t ∈ T,
      ENNReal.ofReal (c₀ ^ q / 5 * V * (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) *
          ((δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) * δ)) ≤
        ∫⁻ x in A t, ‖F x‖ₑ ^ q := by
    intro t ht
    obtain ⟨hta, htb⟩ := hrange t ht
    exact le_setLIntegral_M_annulusTest hd hE hq2 hc₀ hcap hδ hδ1 hδL hL1 htL
      htLL (hTE (by simpa using ht)) hta htb
  calc ENNReal.ofReal (c₀ ^ q / 5 * V * (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) *
        (T.card : ℝ) * ((δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) * δ))
      = (T.card : ℕ) • ENNReal.ofReal (c₀ ^ q / 5 * V *
          (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) *
          ((δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) * δ)) := by
        rw [nsmul_eq_mul]
        rw [show c₀ ^ q / 5 * V * (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) *
              (T.card : ℝ) *
              ((δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) * δ) =
            (T.card : ℝ) * (c₀ ^ q / 5 * V *
              (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) *
              ((δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) * δ))
            by ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg (T.card)), ENNReal.ofReal_natCast]
    _ = ∑ _t ∈ T, ENNReal.ofReal (c₀ ^ q / 5 * V *
          (4 : ℝ) ^ (-(q * ((d : ℝ) - 1) / 2)) *
          ((δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) * δ)) := by
        rw [Finset.sum_const]
    _ ≤ ∑ t ∈ T, ∫⁻ x in A t, ‖F x‖ₑ ^ q := Finset.sum_le_sum hterm

/-- **Lemma 3.5 of BRS, in profile form.**  A radial `L^p → L^q` bound with
`q ≥ 2` bounds the Legendre profile `|J|^{-α} N(E ∩ J, δ)` with
`α = (d-1)(q/2-1)` by `M δ^{-B}`, `B = q(d-1)/2 + 1 - q/p`. -/
theorem profile_bound_of_hasRadialStrongType {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) {p q : ℝ} (hp : 0 < p) (hq2 : 2 ≤ q)
    (h : HasRadialStrongType d E (ENNReal.ofReal p) (ENNReal.ofReal q)) :
    ∃ M : ℝ, 0 < M ∧ ∀ δ L tL : ℝ, 0 < δ → δ ≤ 1 → 10 * δ ≤ L → L ≤ 1 →
      1 ≤ tL → tL + L ≤ 2 → ∀ T : Finset ℝ, (↑T : Set ℝ) ⊆ E →
        (∀ t ∈ T, tL + 5 * δ ≤ t ∧ t ≤ tL + L) →
        (∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s|) →
          L ^ (((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2) * (T.card : ℝ) ≤
            M * δ ^ (-(q * ((d : ℝ) - 1) / 2 + 1 - q / p)) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hq2
  obtain ⟨c, hc, hlow⟩ := le_eLpNorm_M_annulusTest_general hd hE hq2
  obtain ⟨C, hC, hbound⟩ := h
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hVtop : volume (Metric.ball (0 : Euclidean d) 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      measure_closedBall_lt_top).ne
  have hVpos : 0 < V :=
    ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_ball_pos volume (0 : Euclidean d) one_pos)) hVtop
  set W : ℝ := 2 * d * 3 ^ (d - 1) * V with hW
  have hWpos : 0 < W := by
    rw [hW]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  refine ⟨C ^ q * W ^ (q / p) / c, ?_, ?_⟩
  · have h1 : (0 : ℝ) < C ^ q := Real.rpow_pos_of_pos hC _
    have h2 : (0 : ℝ) < W ^ (q / p) := Real.rpow_pos_of_pos hWpos _
    positivity
  intro δ L tL hδ hδ1 hδL hL1 htL htLL T hTE hrange hsep
  have hLpos : 0 < L := by linarith
  have hcard : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  -- the upper bound from the operator
  have hmem := memLp_brsAnnulusTest hd htL (by linarith) hδ hδ1 hp
  have hrad := isNormRadial_brsAnnulusTest d tL δ
  have hup := (hbound _ hmem hrad).2
  have hnorm := eLpNorm_brsAnnulusTest_le hd htL (by linarith) hδ hδ1 hp
  have hupq : eLpNorm (M E (brsAnnulusTest d tL δ)) (ENNReal.ofReal q) volume ^ q ≤
      ENNReal.ofReal (C ^ q * (W * δ) ^ (q / p)) := by
    have hstep : eLpNorm (M E (brsAnnulusTest d tL δ)) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (C * (W * δ) ^ (1 / p)) := by
      refine le_trans hup ?_
      refine le_trans (mul_le_mul' le_rfl hnorm) (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul hC.le]
      congr 1
      rw [show W * δ = 2 * d * 3 ^ (d - 1) * δ * V by rw [hW]; ring]
    refine le_trans (ENNReal.rpow_le_rpow hstep hq0.le) (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_pos
      (mul_pos hC (Real.rpow_pos_of_pos (mul_pos hWpos hδ) _))]
    congr 1
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg (mul_pos hWpos hδ).le _),
      ← Real.rpow_mul (mul_pos hWpos hδ).le]
    congr 2
    field_simp
  -- combine with the lower bound
  have hlowδ := hlow δ L tL hδ hδ1 hδL hL1 htL htLL T hTE hrange hsep
  have hchain := le_trans hlowδ hupq
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
  -- unwind the exponents
  have hsplit : (δ / L) ^ (q * ((d : ℝ) - 1) / 2) * L ^ ((d : ℝ) - 1) =
      δ ^ (q * ((d : ℝ) - 1) / 2) *
        L ^ (((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2) :=
    div_rpow_mul_rpow hδ.le hLpos
  rw [hsplit] at hreal
  have hWsplit : (W * δ) ^ (q / p) = W ^ (q / p) * δ ^ (q / p) :=
    Real.mul_rpow hWpos.le hδ.le
  rw [hWsplit] at hreal
  -- solve for the profile quantity
  have hposδ : (0 : ℝ) < δ ^ (q * ((d : ℝ) - 1) / 2) * δ := by positivity
  have hpow : δ ^ (-(q * ((d : ℝ) - 1) / 2 + 1 - q / p)) *
      (δ ^ (q * ((d : ℝ) - 1) / 2) * δ) = δ ^ (q / p) := by
    rw [show δ ^ (q * ((d : ℝ) - 1) / 2) * δ =
        δ ^ (q * ((d : ℝ) - 1) / 2 + 1) by
      rw [Real.rpow_add hδ, Real.rpow_one], ← Real.rpow_add hδ]
    congr 1
    ring
  rw [show C ^ q * W ^ (q / p) / c *
        δ ^ (-(q * ((d : ℝ) - 1) / 2 + 1 - q / p)) =
      (C ^ q * W ^ (q / p) * δ ^ (-(q * ((d : ℝ) - 1) / 2 + 1 - q / p))) / c
      by ring, le_div_iff₀ hc]
  have hmul : L ^ (((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2) * (T.card : ℝ) * c *
      (δ ^ (q * ((d : ℝ) - 1) / 2) * δ) ≤ C ^ q * (W ^ (q / p) * δ ^ (q / p)) := by
    calc L ^ (((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2) * (T.card : ℝ) * c *
          (δ ^ (q * ((d : ℝ) - 1) / 2) * δ)
        = c * (T.card : ℝ) *
            (δ ^ (q * ((d : ℝ) - 1) / 2) *
              L ^ (((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2) * δ) := by ring
      _ ≤ C ^ q * (W ^ (q / p) * δ ^ (q / p)) := hreal
  have hgoal : L ^ (((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2) * (T.card : ℝ) * c ≤
      C ^ q * W ^ (q / p) * δ ^ (-(q * ((d : ℝ) - 1) / 2 + 1 - q / p)) := by
    rw [← mul_le_mul_iff_of_pos_right hposδ]
    calc L ^ (((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2) * (T.card : ℝ) * c *
          (δ ^ (q * ((d : ℝ) - 1) / 2) * δ)
        ≤ C ^ q * (W ^ (q / p) * δ ^ (q / p)) := hmul
      _ = C ^ q * W ^ (q / p) *
            (δ ^ (-(q * ((d : ℝ) - 1) / 2 + 1 - q / p)) *
              (δ ^ (q * ((d : ℝ) - 1) / 2) * δ)) := by
          rw [hpow]
          ring
      _ = C ^ q * W ^ (q / p) *
            δ ^ (-(q * ((d : ℝ) - 1) / 2 + 1 - q / p)) *
            (δ ^ (q * ((d : ℝ) - 1) / 2) * δ) := by ring
  exact hgoal

/-- **The Legendre profile term is bounded, for every interval.**  This is
Lemma 3.5 in the form needed by the Legendre--Assouad function: the count of a
`δ`-separated family inside an arbitrary interval `I`, weighted by
`|I|^{-α}` with `α = (d-1)(q/2-1)`, is `O(δ^{-B})`,
`B = q(d-1)/2 + 1 - q/p`. -/
theorem profile_term_bound_of_hasRadialStrongType {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p q : ℝ} (hp : 0 < p)
    (hq2 : 2 ≤ q) (h : HasRadialStrongType d E (ENNReal.ofReal p)
      (ENNReal.ofReal q)) :
    ∃ M : ℝ, 0 < M ∧ ∀ δ a R : ℝ, 0 < δ → δ ≤ 1 / 100 → 2 * δ ≤ R → R ≤ 1 →
      ∀ T : Finset ℝ, (↑T : Set ℝ) ⊆ E ∩ Icc a (a + R) →
        (∀ t ∈ T, ∀ s ∈ T, t ≠ s → δ ≤ |t - s|) →
          R ^ (((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2) * (T.card : ℝ) ≤
            M * δ ^ (-(q * ((d : ℝ) - 1) / 2 + 1 - q / p)) := by
  classical
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hq2
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hqpd : q ≤ p * d := le_mul_of_hasRadialStrongType hd hE hEne hp hq0 h
  set α : ℝ := ((d : ℝ) - 1) * (q / 2 - 1) with hα
  set B : ℝ := q * ((d : ℝ) - 1) / 2 + 1 - q / p with hB
  have hαnonneg : 0 ≤ α := by
    rw [hα]
    have h1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) ≤ q / 2 - 1 := by linarith
    exact mul_nonneg h1 h2
  have hαB : α ≤ B := by
    rw [hα, hB]
    have hqp : q / p ≤ (d : ℝ) := by
      rw [div_le_iff₀ hp]
      linarith [hqpd]
    nlinarith [hqp, hd1]
  have hexp : ((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2 = -α := by
    rw [hα]
    ring
  obtain ⟨M₀, hM₀, hprof⟩ := profile_bound_of_hasRadialStrongType hd hE hp hq2 h
  refine ⟨M₀ + 11, by linarith, ?_⟩
  intro δ a R hδ hδ1 hδR hR1 T hTsub hsep
  have hRpos : 0 < R := by linarith
  have hδle1 : δ ≤ 1 := by linarith
  have hTE : (↑T : Set ℝ) ⊆ E := fun t ht => (hTsub ht).1
  have hTI : ∀ t ∈ T, a ≤ t ∧ t ≤ a + R := by
    intro t ht
    have hmem := (hTsub (by simpa using ht)).2
    exact ⟨hmem.1, hmem.2⟩
  have hT12 : ∀ t ∈ T, (1 : ℝ) ≤ t ∧ t ≤ 2 := by
    intro t ht
    have hmem := hE (hTE (by simpa using ht))
    exact ⟨hmem.1, hmem.2⟩
  set u : ℝ := max a 1 with hu
  set v : ℝ := min (a + R) 2 with hv
  have hTu : ∀ t ∈ T, u ≤ t := by
    intro t ht
    rw [hu, max_le_iff]
    exact ⟨(hTI t ht).1, (hT12 t ht).1⟩
  have hTv : ∀ t ∈ T, t ≤ v := by
    intro t ht
    rw [hv, le_min_iff]
    exact ⟨(hTI t ht).2, (hT12 t ht).2⟩
  have hu1 : (1 : ℝ) ≤ u := le_max_right _ _
  have hv2 : v ≤ 2 := min_le_right _ _
  have hvu : v - u ≤ R := by
    have h1 : v ≤ a + R := min_le_left _ _
    have h2 : a ≤ u := le_max_left _ _
    linarith
  -- the two scale comparisons
  have hδα : δ ^ (-α) ≤ δ ^ (-B) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδle1 (by linarith)
  have hRα : R ^ (-α) ≤ δ ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hδ (by linarith) (by linarith)
  have hRB : R ^ (-α) ≤ δ ^ (-B) := le_trans hRα hδα
  have hRαpos : 0 < R ^ (-α) := Real.rpow_pos_of_pos hRpos _
  rw [hexp]
  by_cases hcase : v - u < 10 * δ
  · -- a short interval carries few separated points
    have hsub : ∀ t ∈ T, t ∈ Icc u (u + (10 : ℕ) * δ) := by
      intro t ht
      refine ⟨hTu t ht, ?_⟩
      have h1 := hTv t ht
      push_cast
      linarith
    have hcard := brrs_card_le_succ_of_separated_in_interval (S := T) (a := u)
      (len := δ) (n := 10) hδ hsub hsep
    have hcardR : (T.card : ℝ) ≤ 11 := by
      have : (T.card : ℝ) ≤ ((10 : ℕ) + 1 : ℕ) := by exact_mod_cast hcard
      push_cast at this
      linarith
    calc R ^ (-α) * (T.card : ℝ) ≤ R ^ (-α) * 11 :=
          mul_le_mul_of_nonneg_left hcardR hRαpos.le
      _ ≤ δ ^ (-B) * 11 := mul_le_mul_of_nonneg_right hRB (by norm_num)
      _ ≤ (M₀ + 11) * δ ^ (-B) := by
          have hδBpos : 0 < δ ^ (-B) := Real.rpow_pos_of_pos hδ _
          nlinarith [hδBpos, hM₀]
  · -- the main case
    push_neg at hcase
    set L : ℝ := v - u with hL
    have hL10 : 10 * δ ≤ L := by
      rw [hL]
      exact hcase
    have hLpos : 0 < L := by linarith
    have hL1 : L ≤ 1 := by
      rw [hL]
      linarith
    have huL : u + L ≤ 2 := by
      rw [hL]
      linarith
    set T₁ : Finset ℝ := T.filter (fun t => u + 5 * δ ≤ t) with hT₁
    set T₀ : Finset ℝ := T.filter (fun t => ¬ (u + 5 * δ ≤ t)) with hT₀
    have hsplit : T₁.card + T₀.card = T.card := by
      rw [hT₁, hT₀]
      exact Finset.card_filter_add_card_filter_not (p := fun t => u + 5 * δ ≤ t)
    have hcard₀ : (T₀.card : ℝ) ≤ 6 := by
      have hsub₀ : ∀ t ∈ T₀, t ∈ Icc u (u + (5 : ℕ) * δ) := by
        intro t ht
        rw [hT₀, Finset.mem_filter] at ht
        refine ⟨hTu t ht.1, ?_⟩
        have := ht.2
        push_cast
        linarith [not_le.mp this]
      have hsep₀ : ∀ t ∈ T₀, ∀ s ∈ T₀, t ≠ s → δ ≤ |t - s| := by
        intro t ht s hs hts
        rw [hT₀, Finset.mem_filter] at ht hs
        exact hsep t ht.1 s hs.1 hts
      have hc := brrs_card_le_succ_of_separated_in_interval (S := T₀) (a := u)
        (len := δ) (n := 5) hδ hsub₀ hsep₀
      have : (T₀.card : ℝ) ≤ ((5 : ℕ) + 1 : ℕ) := by exact_mod_cast hc
      push_cast at this
      linarith
    have hT₁E : (↑T₁ : Set ℝ) ⊆ E := by
      intro t ht
      simp only [hT₁, Finset.coe_filter, Set.mem_setOf_eq] at ht
      exact hTE (by simpa using ht.1)
    have hT₁range : ∀ t ∈ T₁, u + 5 * δ ≤ t ∧ t ≤ u + L := by
      intro t ht
      rw [hT₁, Finset.mem_filter] at ht
      refine ⟨ht.2, ?_⟩
      have := hTv t ht.1
      rw [hL]
      linarith
    have hT₁sep : ∀ t ∈ T₁, ∀ s ∈ T₁, t ≠ s → δ ≤ |t - s| := by
      intro t ht s hs hts
      rw [hT₁, Finset.mem_filter] at ht hs
      exact hsep t ht.1 s hs.1 hts
    have hprofT₁ := hprof δ L u hδ hδle1 hL10 hL1 hu1 huL T₁ hT₁E hT₁range hT₁sep
    rw [hexp] at hprofT₁
    -- compare the interval scales
    have hLR : R ^ (-α) ≤ L ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hLpos (by linarith) (by linarith)
    have hcardsplit : (T.card : ℝ) = (T₁.card : ℝ) + (T₀.card : ℝ) := by
      rw [← hsplit]
      push_cast
      ring
    have hδBpos : 0 < δ ^ (-B) := Real.rpow_pos_of_pos hδ _
    calc R ^ (-α) * (T.card : ℝ)
        = R ^ (-α) * (T₁.card : ℝ) + R ^ (-α) * (T₀.card : ℝ) := by
          rw [hcardsplit]
          ring
      _ ≤ L ^ (-α) * (T₁.card : ℝ) + R ^ (-α) * 6 := by
          have h1 : R ^ (-α) * (T₁.card : ℝ) ≤ L ^ (-α) * (T₁.card : ℝ) :=
            mul_le_mul_of_nonneg_right hLR (Nat.cast_nonneg _)
          have h2 : R ^ (-α) * (T₀.card : ℝ) ≤ R ^ (-α) * 6 :=
            mul_le_mul_of_nonneg_left hcard₀ hRαpos.le
          linarith
      _ ≤ M₀ * δ ^ (-B) + δ ^ (-B) * 6 := by
          have h2 : R ^ (-α) * 6 ≤ δ ^ (-B) * 6 :=
            mul_le_mul_of_nonneg_right hRB (by norm_num)
          linarith [hprofT₁]
      _ ≤ (M₀ + 11) * δ ^ (-B) := by nlinarith [hδBpos]

/-- **The Legendre--Assouad profile is bounded by a power of the scale.**  This
is Lemma 3.5 in exactly the shape consumed by
`brrsLegendreAssouadFunction_le_of_profile_power_bound`. -/
theorem brrsProfile_le_of_hasRadialStrongType {d : ℕ} (hd : 0 < d) {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p q : ℝ} (hp : 0 < p)
    (hq2 : 2 ≤ q) (h : HasRadialStrongType d E (ENNReal.ofReal p)
      (ENNReal.ofReal q)) :
    ∃ M : ℝ, 0 < M ∧ ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) ≤ 1 / 100 →
      _root_.Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E
          (((d : ℝ) - 1) * (q / 2 - 1)) δ ≤
        ENNReal.ofReal M *
          (δ : ℝ≥0∞) ^ (-(q * ((d : ℝ) - 1) / 2 + 1 - q / p)) := by
  classical
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hq2
  obtain ⟨M₀, hM₀, hterm⟩ :=
    profile_term_bound_of_hasRadialStrongType hd hE hEne hp hq2 h
  set α : ℝ := ((d : ℝ) - 1) * (q / 2 - 1) with hα
  set B : ℝ := q * ((d : ℝ) - 1) / 2 + 1 - q / p with hB
  have hexp : ((d : ℝ) - 1) - q * ((d : ℝ) - 1) / 2 = -α := by
    rw [hα]
    ring
  refine ⟨M₀ * (2 : ℝ) ^ B, ?_, ?_⟩
  · have h2 : (0 : ℝ) < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  intro δ hδpos hδ100
  have hδR : (0 : ℝ) < (δ : ℝ) := hδpos
  rw [_root_.Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile]
  refine iSup_le fun a => iSup_le fun R => ?_
  obtain ⟨hRδ, hR1⟩ := R.2
  have hRposR : (0 : ℝ) < (R.1 : ℝ) := lt_of_lt_of_le hδR (by exact_mod_cast hRδ)
  have hR1R : (R.1 : ℝ) ≤ 1 := by exact_mod_cast hR1
  -- a maximal separated subset of the local piece
  set I : Set ℝ := _root_.Auto.Spherical.LegendreAssouad.brrsInterval a (R.1 : ℝ)
    with hI
  have hEI : E ∩ I ⊆ Icc (1 : ℝ) 2 := fun t ht => hE ht.1
  obtain ⟨T, hT⟩ := exists_isMaximalSeparatedSubset hEI
    (by positivity : (0 : ℝ) < ((δ / 2 : ℝ≥0) : ℝ))
  have hhalf : (2 : ℝ≥0) * (δ / 2) = δ := by
    rw [mul_comm]
    field_simp
  have hentropy : _root_.Auto.Spherical.LegendreAssouad.brrsEntropyNumber
      (E ∩ I) δ ≤ (T.card : ℝ≥0∞) := by
    have := brrsEntropyNumber_le_card_of_isMaximalSeparatedSubset
      (E := E ∩ I) (δ := δ / 2) (by positivity) hT
    rwa [hhalf] at this
  -- the real bound
  have hδ2R : (0 : ℝ) < ((δ / 2 : ℝ≥0) : ℝ) := by positivity
  have hδ2val : ((δ / 2 : ℝ≥0) : ℝ) = (δ : ℝ) / 2 := by
    push_cast
    ring
  have hTsub : (↑T : Set ℝ) ⊆ E ∩ Icc a (a + (R.1 : ℝ)) := by
    intro t ht
    have := hT.1 ht
    exact ⟨this.1, this.2⟩
  have hTsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → ((δ : ℝ) / 2) ≤ |t - s| := by
    intro t ht s hs hts
    have := hT.2.1 (by simpa using ht) (by simpa using hs) hts
    rwa [hδ2val] at this
  have hbound := hterm ((δ : ℝ) / 2) a (R.1 : ℝ) (by positivity)
    (by linarith) (by linarith [hRδ, (by exact_mod_cast hRδ : (δ : ℝ) ≤ (R.1 : ℝ))])
    hR1R T hTsub hTsep
  rw [hexp] at hbound
  -- transfer to `ℝ≥0∞`
  have hcast : ((R.1 : ℝ≥0) : ℝ≥0∞) ^ (-α) *
      _root_.Auto.Spherical.LegendreAssouad.brrsEntropyNumber (E ∩ I) δ ≤
      ENNReal.ofReal ((R.1 : ℝ) ^ (-α) * (T.card : ℝ)) := by
    have h1 : ((R.1 : ℝ≥0) : ℝ≥0∞) ^ (-α) =
        ENNReal.ofReal ((R.1 : ℝ) ^ (-α)) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_rpow_of_pos hRposR]
    rw [h1, ENNReal.ofReal_mul (Real.rpow_nonneg hRposR.le _)]
    refine mul_le_mul' le_rfl ?_
    refine le_trans hentropy (le_of_eq ?_)
    rw [ENNReal.ofReal_natCast]
  refine le_trans hcast ?_
  -- the power of the half scale
  have hhalfpow : ((δ : ℝ) / 2) ^ (-B) = (2 : ℝ) ^ B * (δ : ℝ) ^ (-B) := by
    rw [Real.div_rpow hδR.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      div_eq_mul_inv, inv_inv]
    ring
  have hfinal : (R.1 : ℝ) ^ (-α) * (T.card : ℝ) ≤
      M₀ * (2 : ℝ) ^ B * (δ : ℝ) ^ (-B) := by
    refine le_trans hbound (le_of_eq ?_)
    rw [hhalfpow]
    ring
  refine le_trans (ENNReal.ofReal_le_ofReal hfinal) (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_rpow_of_pos hδR]

/-- **Lemma 3.5 of BRS.**  For `q ≥ 2` a radial `L^p → L^q` bound forces the
Legendre-Assouad function to satisfy
`(1/q) ν♯((d-1)(q/2-1)) + 1/p - 1/q ≤ (d-1)/2`. -/
theorem legendreAssouad_le_of_hasRadialStrongType {d : ℕ} (hd : 0 < d)
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p q : ℝ}
    (hp : 0 < p) (hq2 : 2 ≤ q)
    (h : HasRadialStrongType d E (ENNReal.ofReal p) (ENNReal.ofReal q)) :
    _root_.Auto.Spherical.LegendreAssouad.brrsLegendreAssouadFunction E
        (((d : ℝ) - 1) * (q / 2 - 1)) ≤
      q * ((d : ℝ) - 1) / 2 + 1 - q / p := by
  obtain ⟨M, hM, hprof⟩ :=
    brrsProfile_le_of_hasRadialStrongType hd hE hEne hp hq2 h
  refine _root_.Auto.Spherical.LegendreAssouad.brrsLegendreAssouadFunction_le_of_profile_power_bound
    hEne (M := M) ENNReal.ofReal_ne_top ?_
  have hmem : Set.Ioo (0 : ℝ≥0) (1 / 100) ∈ 𝓝[>] (0 : ℝ≥0) :=
    Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with δ hδ
  refine hprof δ hδ.1 ?_
  have h2 : (δ : ℝ) < ((1 / 100 : ℝ≥0) : ℝ) := by exact_mod_cast hδ.2
  push_cast at h2
  linarith

/-- The same conclusion in the normalized form printed in BRS. -/
theorem legendreAssouad_condition_of_hasRadialStrongType {d : ℕ} (hd : 0 < d)
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) {p q : ℝ}
    (hp : 0 < p) (hq2 : 2 ≤ q)
    (h : HasRadialStrongType d E (ENNReal.ofReal p) (ENNReal.ofReal q)) :
    (1 / q) * _root_.Auto.Spherical.LegendreAssouad.brrsLegendreAssouadFunction E
        (((d : ℝ) - 1) * (q / 2 - 1)) + 1 / p - 1 / q ≤ ((d : ℝ) - 1) / 2 := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hq2
  have hle := legendreAssouad_le_of_hasRadialStrongType hd hE hEne hp hq2 h
  have hmul : (1 / q) *
      _root_.Auto.Spherical.LegendreAssouad.brrsLegendreAssouadFunction E
        (((d : ℝ) - 1) * (q / 2 - 1)) ≤
      (1 / q) * (q * ((d : ℝ) - 1) / 2 + 1 - q / p) :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  have hsimp : (1 / q) * (q * ((d : ℝ) - 1) / 2 + 1 - q / p) =
      ((d : ℝ) - 1) / 2 + 1 / q - 1 / p := by
    field_simp
  rw [hsimp] at hmul
  linarith [hmul]

/-! ## The planar kernel, split at the two endpoint singularities

For `d = 2` the kernel `K_t(r,s) = s / (√((r+t)²-s²) √(s²-(r-t)²))` has an
inverse square-root singularity at each endpoint of the window.  On the half
of the window nearest `|r-t|` only the left singularity is active, and on the
other half only the right one; this is the source of the operators `𝔐_p^±` of
BRS Lemma 5.1. -/

/-- The distance from the window endpoints to its midpoint is `min r t`. -/
theorem window_half_width (r t : ℝ) : r + t - |r - t| = 2 * min r t := by
  rcases le_total r t with h | h
  · rw [abs_of_nonpos (by linarith), min_eq_left h]
    ring
  · rw [abs_of_nonneg (by linarith), min_eq_right h]
    ring

/-- **The planar kernel near the left endpoint.** -/
theorem brsKernelTwo_le_left {r t s : ℝ} (hr : 0 < r) (ht1 : r / 2 < t)
    (hs1 : |r - t| ≤ s) (hs2 : 2 * s ≤ |r - t| + (r + t)) :
    brsKernelTwo t r s ≤
      2 / (Real.sqrt 3 * r) * (Real.sqrt s / Real.sqrt (s - |r - t|)) := by
  have habs : (0 : ℝ) ≤ |r - t| := abs_nonneg _
  have hs0 : (0 : ℝ) ≤ s := le_trans habs hs1
  have htpos : 0 < t := by linarith
  have hmin : r / 2 ≤ min r t := by
    rcases le_total r t with h | h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      linarith
  have hleft : r / 2 ≤ r + t - s := by
    have hw := window_half_width r t
    have : 2 * s ≤ 2 * (r + t) - 2 * min r t := by
      rw [show 2 * (r + t) - 2 * min r t = (r + t) + (r + t - 2 * min r t) by ring,
        ← hw]
      linarith
    linarith [hmin]
  have hsum : 3 * r / 2 ≤ r + t + s := by linarith
  -- factor the two square roots
  have hA : (r + t) ^ 2 - s ^ 2 = (r + t - s) * (r + t + s) := by ring
  have hB : s ^ 2 - (r - t) ^ 2 = (s - |r - t|) * (s + |r - t|) := by
    rw [show (r - t) ^ 2 = |r - t| ^ 2 by rw [sq_abs]]
    ring
  have hfacA : Real.sqrt ((r + t) ^ 2 - s ^ 2) =
      Real.sqrt (r + t - s) * Real.sqrt (r + t + s) := by
    rw [hA, Real.sqrt_mul (by linarith)]
  have hfacB : Real.sqrt (s ^ 2 - (r - t) ^ 2) =
      Real.sqrt (s - |r - t|) * Real.sqrt (s + |r - t|) := by
    rw [hB, Real.sqrt_mul (by linarith)]
  -- lower bounds for the harmless factors
  have hrootA : Real.sqrt (r / 2) ≤ Real.sqrt (r + t - s) :=
    Real.sqrt_le_sqrt hleft
  have hrootB : Real.sqrt (3 * r / 2) ≤ Real.sqrt (r + t + s) :=
    Real.sqrt_le_sqrt hsum
  have hrootC : Real.sqrt s ≤ Real.sqrt (s + |r - t|) :=
    Real.sqrt_le_sqrt (by linarith)
  have hprod : Real.sqrt (r / 2) * Real.sqrt (3 * r / 2) = Real.sqrt 3 * r / 2 := by
    rw [← Real.sqrt_mul (by linarith)]
    rw [show r / 2 * (3 * r / 2) = 3 * (r / 2) ^ 2 by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith)]
    ring
  rcases eq_or_lt_of_le hs1 with hEq | hlt
  · -- at the left endpoint both sides vanish
    have hz : s - |r - t| = 0 := by linarith [hEq]
    rw [brsKernelTwo, hfacB, hz, Real.sqrt_zero]
    simp
  · have hpos : 0 < s - |r - t| := by linarith
    have hspos : 0 < s := lt_of_le_of_lt habs hlt
    have hrootpos : 0 < Real.sqrt (s - |r - t|) := Real.sqrt_pos.mpr hpos
    have hsrootpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    have hAB : Real.sqrt 3 * r / 2 * (Real.sqrt (s - |r - t|) * Real.sqrt s) ≤
        Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) := by
      rw [hfacA, hfacB, ← hprod]
      gcongr
    have hdenpos : 0 < Real.sqrt 3 * r / 2 *
        (Real.sqrt (s - |r - t|) * Real.sqrt s) := by
      have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      positivity
    have hDpos : 0 < Real.sqrt ((r + t) ^ 2 - s ^ 2) *
        Real.sqrt (s ^ 2 - (r - t) ^ 2) := lt_of_lt_of_le hdenpos hAB
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hrewrite : 2 / (Real.sqrt 3 * r) *
        (Real.sqrt s / Real.sqrt (s - |r - t|)) =
        (2 * Real.sqrt s) / (Real.sqrt 3 * r * Real.sqrt (s - |r - t|)) := by
      field_simp
    rw [brsKernelTwo, hrewrite, div_le_div_iff₀ hDpos (by positivity)]
    have hssqrt : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0
    calc s * (Real.sqrt 3 * r * Real.sqrt (s - |r - t|))
        = (Real.sqrt 3 * r / 2 * (Real.sqrt (s - |r - t|) * Real.sqrt s)) *
            (2 * Real.sqrt s) := by
          rw [show (Real.sqrt 3 * r / 2 *
              (Real.sqrt (s - |r - t|) * Real.sqrt s)) * (2 * Real.sqrt s) =
            Real.sqrt 3 * r * Real.sqrt (s - |r - t|) *
              (Real.sqrt s * Real.sqrt s) by ring, hssqrt]
          ring
      _ ≤ (Real.sqrt ((r + t) ^ 2 - s ^ 2) *
            Real.sqrt (s ^ 2 - (r - t) ^ 2)) * (2 * Real.sqrt s) := by
          refine mul_le_mul_of_nonneg_right hAB ?_
          positivity
      _ = 2 * Real.sqrt s * (Real.sqrt ((r + t) ^ 2 - s ^ 2) *
            Real.sqrt (s ^ 2 - (r - t) ^ 2)) := by ring

/-- **The planar kernel near the right endpoint.** -/
theorem brsKernelTwo_le_right {r t s : ℝ} (hr : 0 < r) (ht1 : r / 2 < t)
    (hs1 : |r - t| + (r + t) ≤ 2 * s) (hs2 : s ≤ r + t) :
    brsKernelTwo t r s ≤
      2 / (Real.sqrt 3 * r) * (Real.sqrt s / Real.sqrt (r + t - s)) := by
  have habs : (0 : ℝ) ≤ |r - t| := abs_nonneg _
  have htpos : 0 < t := by linarith
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hmin : r / 2 ≤ min r t := by
    rcases le_total r t with h | h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      linarith
  have hright : r / 2 ≤ s - |r - t| := by
    have hw := window_half_width r t
    have h2 : 2 * min r t ≤ 2 * s - 2 * |r - t| := by
      rw [← hw]
      linarith
    linarith [hmin]
  have hsum : 3 * r / 2 ≤ r + t + s := by
    have : (0 : ℝ) ≤ s := hs0
    linarith
  have hA : (r + t) ^ 2 - s ^ 2 = (r + t - s) * (r + t + s) := by ring
  have hB : s ^ 2 - (r - t) ^ 2 = (s - |r - t|) * (s + |r - t|) := by
    rw [show (r - t) ^ 2 = |r - t| ^ 2 by rw [sq_abs]]
    ring
  have hfacA : Real.sqrt ((r + t) ^ 2 - s ^ 2) =
      Real.sqrt (r + t - s) * Real.sqrt (r + t + s) := by
    rw [hA, Real.sqrt_mul (by linarith)]
  have hfacB : Real.sqrt (s ^ 2 - (r - t) ^ 2) =
      Real.sqrt (s - |r - t|) * Real.sqrt (s + |r - t|) := by
    rw [hB, Real.sqrt_mul (by linarith)]
  have hprod : Real.sqrt (3 * r / 2) * Real.sqrt (r / 2) = Real.sqrt 3 * r / 2 := by
    rw [← Real.sqrt_mul (by linarith)]
    rw [show 3 * r / 2 * (r / 2) = 3 * (r / 2) ^ 2 by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith)]
    ring
  rcases eq_or_lt_of_le hs2 with hEq | hlt
  · have hz : r + t - s = 0 := by linarith [hEq]
    rw [brsKernelTwo, hfacA, hz, Real.sqrt_zero]
    simp
  · have hpos : 0 < r + t - s := by linarith
    have hspos : 0 < s := by
      have : r / 2 ≤ s - |r - t| := hright
      linarith
    have hrootpos : 0 < Real.sqrt (r + t - s) := Real.sqrt_pos.mpr hpos
    have hAB : Real.sqrt 3 * r / 2 * (Real.sqrt (r + t - s) * Real.sqrt s) ≤
        Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) := by
      have hstep : Real.sqrt (r + t - s) * Real.sqrt (3 * r / 2) *
          (Real.sqrt (r / 2) * Real.sqrt s) ≤
          Real.sqrt (r + t - s) * Real.sqrt (r + t + s) *
            (Real.sqrt (s - |r - t|) * Real.sqrt (s + |r - t|)) := by
        gcongr
        linarith
      rw [hfacA, hfacB]
      refine le_trans (le_of_eq ?_) hstep
      rw [← hprod]
      ring
    have hdenpos : 0 < Real.sqrt 3 * r / 2 *
        (Real.sqrt (r + t - s) * Real.sqrt s) := by
      have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      have h4 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr hspos
      positivity
    have hDpos : 0 < Real.sqrt ((r + t) ^ 2 - s ^ 2) *
        Real.sqrt (s ^ 2 - (r - t) ^ 2) := lt_of_lt_of_le hdenpos hAB
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hrewrite : 2 / (Real.sqrt 3 * r) *
        (Real.sqrt s / Real.sqrt (r + t - s)) =
        (2 * Real.sqrt s) / (Real.sqrt 3 * r * Real.sqrt (r + t - s)) := by
      field_simp
    rw [brsKernelTwo, hrewrite, div_le_div_iff₀ hDpos (by positivity)]
    have hssqrt : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0
    calc s * (Real.sqrt 3 * r * Real.sqrt (r + t - s))
        = (Real.sqrt 3 * r / 2 * (Real.sqrt (r + t - s) * Real.sqrt s)) *
            (2 * Real.sqrt s) := by
          rw [show (Real.sqrt 3 * r / 2 *
              (Real.sqrt (r + t - s) * Real.sqrt s)) * (2 * Real.sqrt s) =
            Real.sqrt 3 * r * Real.sqrt (r + t - s) *
              (Real.sqrt s * Real.sqrt s) by ring, hssqrt]
          ring
      _ ≤ (Real.sqrt ((r + t) ^ 2 - s ^ 2) *
            Real.sqrt (s ^ 2 - (r - t) ^ 2)) * (2 * Real.sqrt s) := by
          refine mul_le_mul_of_nonneg_right hAB ?_
          positivity
      _ = 2 * Real.sqrt s * (Real.sqrt ((r + t) ^ 2 - s ^ 2) *
            Real.sqrt (s ^ 2 - (r - t) ^ 2)) := by ring

/-! ## The operators of BRS Lemma 5.1

In the plane the two endpoint singularities of the kernel are separated into
two maximal operators `𝔐_p^±`, and the dilations away from the radius give the
two remainders `R_1^±`, `R_2^±`. -/

/-- The main term `𝔐_p^-` of BRS (5.1): the left endpoint singularity. -/
def brsMainTwoLeft (E : Set ℝ) (p : ℝ) (g : ℝ → ℂ) (r : ℝ) : ENNReal :=
  ⨆ t ∈ E ∩ Ioo (r / 2) (3 * r / 2),
    ENNReal.ofReal (r⁻¹ * ‖∫ s in |r - t|..(r + t),
      ((s ^ (1 / 2 - 1 / p) * (s - |r - t|) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * g s‖)

/-- The main term `𝔐_p^+` of BRS (5.1): the right endpoint singularity. -/
def brsMainTwoRight (E : Set ℝ) (p : ℝ) (g : ℝ → ℂ) (r : ℝ) : ENNReal :=
  ⨆ t ∈ E ∩ Ioo (r / 2) (3 * r / 2),
    ENNReal.ofReal (r⁻¹ * ‖∫ s in |r - t|..(r + t),
      ((s ^ (1 / 2 - 1 / p) * (r + t - s) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * g s‖)

/-- The integrand of `𝔐_p^-` applied to the substituted profile is the planar
kernel weight `√s (s - |r-t|)^{-1/2}` against the profile itself. -/
theorem brsMainTwoLeft_integrand {p : ℝ} (hp : 0 < p) (f₀ : ℝ → ℂ) {r t s : ℝ}
    (hs : 0 < s) :
    ((s ^ (1 / 2 - 1 / p) * (s - |r - t|) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) *
        brsProfileSub 2 p f₀ s =
      ((s ^ (1 / 2 : ℝ) * (s - |r - t|) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * f₀ s := by
  rw [brsProfileSub]
  have hcast : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  rw [hcast]
  have hmul : (s ^ (1 / 2 - 1 / p) * (s - |r - t|) ^ (-(1 / 2) : ℝ)) *
      s ^ (1 / p) = s ^ (1 / 2 : ℝ) * (s - |r - t|) ^ (-(1 / 2) : ℝ) := by
    rw [show s ^ (1 / 2 - 1 / p) * (s - |r - t|) ^ (-(1 / 2) : ℝ) * s ^ (1 / p) =
        (s ^ (1 / 2 - 1 / p) * s ^ (1 / p)) *
          (s - |r - t|) ^ (-(1 / 2) : ℝ) by ring,
      ← Real.rpow_add hs]
    congr 2
    ring
  calc ((s ^ (1 / 2 - 1 / p) * (s - |r - t|) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) *
        (((s ^ (1 / p) : ℝ) : ℂ) * f₀ s)
      = ((s ^ (1 / 2 - 1 / p) * (s - |r - t|) ^ (-(1 / 2) : ℝ) *
          s ^ (1 / p) : ℝ) : ℂ) * f₀ s := by
        push_cast
        ring
    _ = ((s ^ (1 / 2 : ℝ) * (s - |r - t|) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * f₀ s := by
        rw [hmul]

/-- The same identity for the right endpoint. -/
theorem brsMainTwoRight_integrand {p : ℝ} (hp : 0 < p) (f₀ : ℝ → ℂ) {r t s : ℝ}
    (hs : 0 < s) :
    ((s ^ (1 / 2 - 1 / p) * (r + t - s) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) *
        brsProfileSub 2 p f₀ s =
      ((s ^ (1 / 2 : ℝ) * (r + t - s) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * f₀ s := by
  rw [brsProfileSub]
  have hcast : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  rw [hcast]
  have hmul : (s ^ (1 / 2 - 1 / p) * (r + t - s) ^ (-(1 / 2) : ℝ)) *
      s ^ (1 / p) = s ^ (1 / 2 : ℝ) * (r + t - s) ^ (-(1 / 2) : ℝ) := by
    rw [show s ^ (1 / 2 - 1 / p) * (r + t - s) ^ (-(1 / 2) : ℝ) * s ^ (1 / p) =
        (s ^ (1 / 2 - 1 / p) * s ^ (1 / p)) *
          (r + t - s) ^ (-(1 / 2) : ℝ) by ring,
      ← Real.rpow_add hs]
    congr 2
    ring
  calc ((s ^ (1 / 2 - 1 / p) * (r + t - s) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) *
        (((s ^ (1 / p) : ℝ) : ℂ) * f₀ s)
      = ((s ^ (1 / 2 - 1 / p) * (r + t - s) ^ (-(1 / 2) : ℝ) *
          s ^ (1 / p) : ℝ) : ℂ) * f₀ s := by
        push_cast
        ring
    _ = ((s ^ (1 / 2 : ℝ) * (r + t - s) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * f₀ s := by
        rw [hmul]

/-- The planar kernel is dominated by the two half-window weights. -/
theorem brsKernelTwo_le_sum {r t s : ℝ} (hr : 0 < r) (ht1 : r / 2 < t)
    (hs1 : |r - t| ≤ s) (hs2 : s ≤ r + t) :
    brsKernelTwo t r s ≤
      2 / (Real.sqrt 3 * r) *
        (s ^ (1 / 2 : ℝ) * (s - |r - t|) ^ (-(1 / 2) : ℝ) +
          s ^ (1 / 2 : ℝ) * (r + t - s) ^ (-(1 / 2) : ℝ)) := by
  have habs : (0 : ℝ) ≤ |r - t| := abs_nonneg _
  have hs0 : (0 : ℝ) ≤ s := le_trans habs hs1
  have hsqrt : Real.sqrt s = s ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow s
  have hleftw : Real.sqrt s / Real.sqrt (s - |r - t|) =
      s ^ (1 / 2 : ℝ) * (s - |r - t|) ^ (-(1 / 2) : ℝ) := by
    rw [hsqrt, Real.sqrt_eq_rpow, div_eq_mul_inv,
      ← Real.rpow_neg_one ((s - |r - t|) ^ (1 / 2 : ℝ)),
      ← Real.rpow_mul (by linarith : (0:ℝ) ≤ s - |r - t|)]
    congr 2
    ring
  have hrightw : Real.sqrt s / Real.sqrt (r + t - s) =
      s ^ (1 / 2 : ℝ) * (r + t - s) ^ (-(1 / 2) : ℝ) := by
    rw [hsqrt, Real.sqrt_eq_rpow, div_eq_mul_inv,
      ← Real.rpow_neg_one ((r + t - s) ^ (1 / 2 : ℝ)),
      ← Real.rpow_mul (by linarith : (0:ℝ) ≤ r + t - s)]
    congr 2
    ring
  have hconst : (0 : ℝ) < 2 / (Real.sqrt 3 * r) := by
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  rcases le_total (2 * s) (|r - t| + (r + t)) with hcase | hcase
  · refine le_trans (brsKernelTwo_le_left hr ht1 hs1 hcase) ?_
    rw [hleftw]
    refine mul_le_mul_of_nonneg_left ?_ hconst.le
    have hnn : (0 : ℝ) ≤ s ^ (1 / 2 : ℝ) * (r + t - s) ^ (-(1 / 2) : ℝ) := by
      have h1 : (0 : ℝ) ≤ s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs0 _
      have h2 : (0 : ℝ) ≤ (r + t - s) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_nonneg (by linarith) _
      exact mul_nonneg h1 h2
    linarith
  · refine le_trans (brsKernelTwo_le_right hr ht1 hcase hs2) ?_
    rw [hrightw]
    refine mul_le_mul_of_nonneg_left ?_ hconst.le
    have hnn : (0 : ℝ) ≤ s ^ (1 / 2 : ℝ) * (s - |r - t|) ^ (-(1 / 2) : ℝ) := by
      have h1 : (0 : ℝ) ≤ s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs0 _
      have h2 : (0 : ℝ) ≤ (s - |r - t|) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_nonneg (by linarith) _
      exact mul_nonneg h1 h2
    linarith

/-- **The planar kernel, with the two harmless factors bounded below.** -/
theorem brsKernelTwo_le_generic {r t s P Q : ℝ} (hs1 : |r - t| ≤ s)
    (hs2 : s ≤ r + t) (hP : 0 < P) (hQ : 0 < Q) (hPle : P ≤ r + t + s)
    (hQle : Q ≤ s + |r - t|) :
    brsKernelTwo t r s ≤
      s / (Real.sqrt P * Real.sqrt Q *
        (Real.sqrt (r + t - s) * Real.sqrt (s - |r - t|))) := by
  have habs : (0 : ℝ) ≤ |r - t| := abs_nonneg _
  have hs0 : (0 : ℝ) ≤ s := le_trans habs hs1
  have hA : (r + t) ^ 2 - s ^ 2 = (r + t - s) * (r + t + s) := by ring
  have hB : s ^ 2 - (r - t) ^ 2 = (s - |r - t|) * (s + |r - t|) := by
    rw [show (r - t) ^ 2 = |r - t| ^ 2 by rw [sq_abs]]
    ring
  have hfacA : Real.sqrt ((r + t) ^ 2 - s ^ 2) =
      Real.sqrt (r + t - s) * Real.sqrt (r + t + s) := by
    rw [hA, Real.sqrt_mul (by linarith)]
  have hfacB : Real.sqrt (s ^ 2 - (r - t) ^ 2) =
      Real.sqrt (s - |r - t|) * Real.sqrt (s + |r - t|) := by
    rw [hB, Real.sqrt_mul (by linarith)]
  have hrootP : Real.sqrt P ≤ Real.sqrt (r + t + s) := Real.sqrt_le_sqrt hPle
  have hrootQ : Real.sqrt Q ≤ Real.sqrt (s + |r - t|) := Real.sqrt_le_sqrt hQle
  have hPpos : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hQpos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  by_cases hdeg : Real.sqrt (r + t - s) * Real.sqrt (s - |r - t|) = 0
  · rcases mul_eq_zero.mp hdeg with h | h
    · rw [brsKernelTwo, hfacA, h]
      simp [hdeg]
    · rw [brsKernelTwo, hfacB, h]
      simp [hdeg]
  · have hpos : 0 < Real.sqrt (r + t - s) * Real.sqrt (s - |r - t|) := by
      rcases lt_or_eq_of_le (mul_nonneg (Real.sqrt_nonneg (r + t - s))
        (Real.sqrt_nonneg (s - |r - t|))) with h | h
      · exact h
      · exact absurd h.symm hdeg
    have hden : 0 < Real.sqrt P * Real.sqrt Q *
        (Real.sqrt (r + t - s) * Real.sqrt (s - |r - t|)) := by positivity
    have hcompare : Real.sqrt P * Real.sqrt Q *
        (Real.sqrt (r + t - s) * Real.sqrt (s - |r - t|)) ≤
        Real.sqrt ((r + t) ^ 2 - s ^ 2) * Real.sqrt (s ^ 2 - (r - t) ^ 2) := by
      rw [hfacA, hfacB]
      calc Real.sqrt P * Real.sqrt Q *
            (Real.sqrt (r + t - s) * Real.sqrt (s - |r - t|))
          = Real.sqrt (r + t - s) * Real.sqrt P *
              (Real.sqrt (s - |r - t|) * Real.sqrt Q) := by ring
        _ ≤ Real.sqrt (r + t - s) * Real.sqrt (r + t + s) *
              (Real.sqrt (s - |r - t|) * Real.sqrt (s + |r - t|)) := by gcongr
    rw [brsKernelTwo]
    exact div_le_div_of_nonneg_left hs0 hden hcompare

/-- Dividing out one of the two singular factors. -/
theorem kernel_div_step {K s c A D C : ℝ} (hK : K ≤ s / (c * (A * D)))
    (hc : 0 < c) (hApos : 0 < A) (hD : 0 ≤ D) (hs : s ≤ C * c) :
    K ≤ C * A⁻¹ * D⁻¹ := by
  by_cases hDz : D = 0
  · rw [hDz] at hK ⊢
    simpa using hK
  · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hDz)
    refine le_trans hK ?_
    rw [div_le_iff₀ (by positivity)]
    calc s ≤ C * c := hs
      _ = C * A⁻¹ * D⁻¹ * (c * (A * D)) := by
          field_simp

/-- Swapping one singular factor for a lower bound. -/
theorem kernel_swap_step {s c A A' D : ℝ} (hs0 : 0 ≤ s) (hc : 0 < c)
    (hApos : 0 < A) (hAA : A ≤ A') (hD : 0 ≤ D) :
    s / (c * (A' * D)) ≤ s / (c * (A * D)) := by
  by_cases hz : D = 0
  · rw [hz]
    simp
  · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hz)
    refine div_le_div_of_nonneg_left hs0 (by positivity) ?_
    have hmono : A * D ≤ A' * D := mul_le_mul_of_nonneg_right hAA hD
    exact mul_le_mul_of_nonneg_left hmono hc.le

/-- **The planar kernel for small dilations, left half.** -/
theorem brsKernelTwo_le_small_left {r t s : ℝ} (hr : 0 < r) (ht : 0 < t)
    (htr : t ≤ r / 2) (hs1 : r - t ≤ s) (hs2 : s ≤ r) :
    brsKernelTwo t r s ≤ 1 * (Real.sqrt t)⁻¹ * (Real.sqrt (s - (r - t)))⁻¹ := by
  have habs : |r - t| = r - t := abs_of_nonneg (by linarith)
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hgen := brsKernelTwo_le_generic (r := r) (t := t) (s := s)
    (P := r) (Q := r) (by rw [habs]; linarith) (by linarith) hr hr
    (by linarith) (by rw [habs]; linarith)
  rw [habs, Real.mul_self_sqrt hr.le] at hgen
  have hswap := kernel_swap_step (s := s) (c := r) (A := Real.sqrt t)
    (A' := Real.sqrt (r + t - s)) (D := Real.sqrt (s - (r - t))) hs0 hr
    (Real.sqrt_pos.mpr ht) (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
  refine kernel_div_step (c := r) (A := Real.sqrt t)
    (D := Real.sqrt (s - (r - t))) (C := 1) (le_trans hgen hswap) hr
    (Real.sqrt_pos.mpr ht) (Real.sqrt_nonneg _) (by linarith)

/-- **The planar kernel for small dilations, right half.** -/
theorem brsKernelTwo_le_small_right {r t s : ℝ} (hr : 0 < r) (ht : 0 < t)
    (htr : t ≤ r / 2) (hs1 : r ≤ s) (hs2 : s ≤ r + t) :
    brsKernelTwo t r s ≤ 2 * (Real.sqrt t)⁻¹ * (Real.sqrt (r + t - s))⁻¹ := by
  have habs : |r - t| = r - t := abs_of_nonneg (by linarith)
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hgen := brsKernelTwo_le_generic (r := r) (t := t) (s := s)
    (P := r) (Q := r) (by rw [habs]; linarith) (by linarith) hr hr
    (by linarith) (by rw [habs]; linarith)
  rw [habs, Real.mul_self_sqrt hr.le] at hgen
  -- reorder the two singular factors
  have hcomm : s / (r * (Real.sqrt (r + t - s) * Real.sqrt (s - (r - t)))) =
      s / (r * (Real.sqrt (s - (r - t)) * Real.sqrt (r + t - s))) := by
    rw [mul_comm (Real.sqrt (r + t - s)) (Real.sqrt (s - (r - t)))]
  rw [hcomm] at hgen
  have hswap := kernel_swap_step (s := s) (c := r) (A := Real.sqrt t)
    (A' := Real.sqrt (s - (r - t))) (D := Real.sqrt (r + t - s)) hs0 hr
    (Real.sqrt_pos.mpr ht) (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
  refine kernel_div_step (c := r) (A := Real.sqrt t)
    (D := Real.sqrt (r + t - s)) (C := 2) (le_trans hgen hswap) hr
    (Real.sqrt_pos.mpr ht) (Real.sqrt_nonneg _) (by linarith)

/-- **The planar kernel for large dilations, left half.** -/
theorem brsKernelTwo_le_large_left {r t s : ℝ} (hr : 0 < r) (htr : 3 * r / 2 ≤ t)
    (hs1 : t - r ≤ s) (hs2 : s ≤ t) :
    brsKernelTwo t r s ≤ 2 * (Real.sqrt r)⁻¹ * (Real.sqrt (s - (t - r)))⁻¹ := by
  have htpos : 0 < t := by linarith
  have habs : |r - t| = t - r := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hgen := brsKernelTwo_le_generic (r := r) (t := t) (s := s)
    (P := t) (Q := t / 4) (by rw [habs]; linarith) (by linarith) htpos
    (by linarith) (by linarith) (by rw [habs]; linarith)
  rw [habs] at hgen
  have hprod : Real.sqrt t * Real.sqrt (t / 4) = t / 2 := by
    rw [← Real.sqrt_mul htpos.le]
    rw [show t * (t / 4) = (t / 2) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  rw [hprod] at hgen
  have hswap := kernel_swap_step (s := s) (c := t / 2) (A := Real.sqrt r)
    (A' := Real.sqrt (r + t - s)) (D := Real.sqrt (s - (t - r))) hs0 (by linarith)
    (Real.sqrt_pos.mpr hr) (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
  refine kernel_div_step (c := t / 2) (A := Real.sqrt r)
    (D := Real.sqrt (s - (t - r))) (C := 2) (le_trans hgen hswap) (by linarith)
    (Real.sqrt_pos.mpr hr) (Real.sqrt_nonneg _) (by linarith)

/-- **The planar kernel for large dilations, right half.** -/
theorem brsKernelTwo_le_large_right {r t s : ℝ} (hr : 0 < r)
    (htr : 3 * r / 2 ≤ t) (hs1 : t ≤ s) (hs2 : s ≤ t + r) :
    brsKernelTwo t r s ≤ 4 * (Real.sqrt r)⁻¹ * (Real.sqrt (r + t - s))⁻¹ := by
  have htpos : 0 < t := by linarith
  have habs : |r - t| = t - r := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hgen := brsKernelTwo_le_generic (r := r) (t := t) (s := s)
    (P := t) (Q := t / 4) (by rw [habs]; linarith) (by linarith) htpos
    (by linarith) (by linarith) (by rw [habs]; linarith)
  rw [habs] at hgen
  have hprod : Real.sqrt t * Real.sqrt (t / 4) = t / 2 := by
    rw [← Real.sqrt_mul htpos.le]
    rw [show t * (t / 4) = (t / 2) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  rw [hprod] at hgen
  have hcomm : s / (t / 2 * (Real.sqrt (r + t - s) * Real.sqrt (s - (t - r)))) =
      s / (t / 2 * (Real.sqrt (s - (t - r)) * Real.sqrt (r + t - s))) := by
    rw [mul_comm (Real.sqrt (r + t - s)) (Real.sqrt (s - (t - r)))]
  rw [hcomm] at hgen
  have hswap := kernel_swap_step (s := s) (c := t / 2) (A := Real.sqrt r)
    (A' := Real.sqrt (s - (t - r))) (D := Real.sqrt (r + t - s)) hs0 (by linarith)
    (Real.sqrt_pos.mpr hr) (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
  refine kernel_div_step (c := t / 2) (A := Real.sqrt r)
    (D := Real.sqrt (r + t - s)) (C := 4) (le_trans hgen hswap) (by linarith)
    (Real.sqrt_pos.mpr hr) (Real.sqrt_nonneg _) (by linarith)

/-- The planar radial spherical average as a kernel integral over the window. -/
theorem sphericalAverage_two_eq_kernel_integral {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀)
    {x : Euclidean 2} (hx : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    _root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x =
      (((surfaceMass 2)⁻¹ * surfaceMass 1 : ℝ) : ℂ) *
        ∫ s in Ioo (|‖x‖ - t|) (‖x‖ + t),
          (2 * brsKernelTwo t ‖x‖ s) • f₀ s := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hangle := sphericalAverage_comp_norm_two f₀ hf₀ hx t
  rw [hangle]
  congr 1
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hset : (∫ φ in (0 : ℝ)..Real.pi,
      f₀ (Real.sqrt (‖x‖ ^ 2 + t ^ 2 + 2 * ‖x‖ * t * Real.cos φ))) =
      ∫ φ in Ioo (0 : ℝ) Real.pi, f₀ (cosineRadius ‖x‖ t φ) := by
    rw [intervalIntegral.integral_of_le hpi, ← integral_Ioc_eq_integral_Ioo]
    rfl
  rw [hset, ← integral_kernelTwo_eq_angle hr ht f₀]

/-- **The planar kernel bound for the spherical average.** -/
theorem ofReal_norm_sphericalAverage_two_le {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀)
    {x : Euclidean 2} (hx : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal ‖_root_.Spherical.sphericalAverage t (fun y => f₀ ‖y‖) x‖ ≤
      ENNReal.ofReal ((surfaceMass 2)⁻¹ * surfaceMass 1) *
        ∫⁻ s in Ioo (|‖x‖ - t|) (‖x‖ + t),
          ENNReal.ofReal (2 * brsKernelTwo t ‖x‖ s * ‖f₀ s‖) := by
  have hmass1 : 0 < surfaceMass 1 := surfaceMass_pos (by norm_num)
  have hmass2 : 0 < surfaceMass 2 := surfaceMass_pos (by norm_num)
  have hc : (0 : ℝ) ≤ (surfaceMass 2)⁻¹ * surfaceMass 1 := by positivity
  rw [sphericalAverage_two_eq_kernel_integral hf₀ hx ht, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hc,
    ENNReal.ofReal_mul hc]
  refine mul_le_mul' le_rfl ?_
  refine le_trans (le_of_eq (ofReal_norm _)) ?_
  refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  have hs0 : 0 ≤ s := le_trans (abs_nonneg _) (le_of_lt hs.1)
  have hker : 0 ≤ brsKernelTwo t ‖x‖ s := by
    rw [brsKernelTwo]
    exact div_nonneg hs0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [← ofReal_norm ((2 * brsKernelTwo t ‖x‖ s) • f₀ s), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * brsKernelTwo t ‖x‖ s)]

/-- The inverse square-root singularity at the left endpoint is integrable. -/
theorem intervalIntegrable_left_weight (a b : ℝ) :
    IntervalIntegrable (fun s => (s - a) ^ (-(1 / 2) : ℝ)) volume a b := by
  have hbase := intervalIntegral.intervalIntegrable_rpow'
    (a := a - a) (b := b - a) (r := (-(1 / 2) : ℝ)) (by norm_num)
  have hshift := hbase.comp_sub_right a
  simpa using hshift

/-- The inverse square-root singularity at the right endpoint is integrable. -/
theorem intervalIntegrable_right_weight (a b : ℝ) :
    IntervalIntegrable (fun s => (b - s) ^ (-(1 / 2) : ℝ)) volume a b := by
  have hbase := intervalIntegral.intervalIntegrable_rpow'
    (a := b - a) (b := b - b) (r := (-(1 / 2) : ℝ)) (by norm_num)
  have hrefl := hbase.comp_sub_left b
  simpa using hrefl

/-- The `𝔐_p^-` integrand is interval integrable. -/
theorem intervalIntegrable_weight_left_mul {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀)
    (a b : ℝ) :
    IntervalIntegrable
      (fun s => (s - a) ^ (-(1 / 2) : ℝ) * (s ^ (1 / 2 : ℝ) * ‖f₀ s‖))
      volume a b :=
  (intervalIntegrable_left_weight a b).mul_continuousOn
    (((continuous_rpow_const_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)).mul
      hf₀.norm).continuousOn)

/-- The `𝔐_p^+` integrand is interval integrable. -/
theorem intervalIntegrable_weight_right_mul {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀)
    (a b : ℝ) :
    IntervalIntegrable
      (fun s => (b - s) ^ (-(1 / 2) : ℝ) * (s ^ (1 / 2 : ℝ) * ‖f₀ s‖))
      volume a b :=
  (intervalIntegrable_right_weight a b).mul_continuousOn
    (((continuous_rpow_const_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)).mul
      hf₀.norm).continuousOn)

/-- The `R_1^±` and `R_2^±` integrands are interval integrable. -/
theorem intervalIntegrable_weight_left_profile {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀)
    (a b : ℝ) :
    IntervalIntegrable (fun s => (s - a) ^ (-(1 / 2) : ℝ) * ‖f₀ s‖) volume a b :=
  (intervalIntegrable_left_weight a b).mul_continuousOn hf₀.norm.continuousOn

theorem intervalIntegrable_weight_right_profile {f₀ : ℝ → ℂ} (hf₀ : Continuous f₀)
    (a b : ℝ) :
    IntervalIntegrable (fun s => (b - s) ^ (-(1 / 2) : ℝ) * ‖f₀ s‖) volume a b :=
  (intervalIntegrable_right_weight a b).mul_continuousOn hf₀.norm.continuousOn

/-- A nonnegative interval integral, as a lower Lebesgue integral over the open
window. -/
theorem lintegral_Ioo_eq_ofReal_intervalIntegral {F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hint : IntervalIntegrable F volume a b)
    (hnn : ∀ s ∈ Ioo a b, 0 ≤ F s) :
    (∫⁻ s in Ioo a b, ENNReal.ofReal (F s)) =
      ENNReal.ofReal (∫ s in a..b, F s) := by
  have hIoc : IntegrableOn F (Ioc a b) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hint
  have hIoo : IntegrableOn F (Ioo a b) volume :=
    hIoc.mono_set Ioo_subset_Ioc_self
  have hae : 0 ≤ᵐ[volume.restrict (Ioo a b)] F := by
    refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
    filter_upwards with s hs
    exact hnn s hs
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIoo hae]

/-- **The main range of BRS Lemma 5.1.**  For dilations comparable to the
radius the window integral is controlled by the two main terms. -/
theorem lintegral_window_le_mainTwo {p : ℝ} (hp : 0 < p) {E : Set ℝ} {f₀ : ℝ → ℂ}
    (hf₀ : Continuous f₀) {r t : ℝ} (hr : 0 < r) (htE : t ∈ E)
    (ht1 : r / 2 < t) (ht2 : t < 3 * r / 2) :
    (∫⁻ s in Ioo (|r - t|) (r + t),
        ENNReal.ofReal (2 * brsKernelTwo t r s * ‖f₀ s‖)) ≤
      ENNReal.ofReal (4 / Real.sqrt 3) *
        (brsMainTwoLeft E p (brsProfileSub 2 p (absProfile f₀)) r +
          brsMainTwoRight E p (brsProfileSub 2 p (absProfile f₀)) r) := by
  have habs : (0 : ℝ) ≤ |r - t| := abs_nonneg _
  have htpos : 0 < t := by linarith
  have hab : |r - t| ≤ r + t := by
    rw [abs_le]
    constructor <;> linarith
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  set c : ℝ := 4 / (Real.sqrt 3 * r) with hc
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  set W₁ : ℝ → ℝ := fun s => s ^ (1 / 2 : ℝ) * (s - |r - t|) ^ (-(1 / 2) : ℝ)
    with hW₁
  set W₂ : ℝ → ℝ := fun s => s ^ (1 / 2 : ℝ) * (r + t - s) ^ (-(1 / 2) : ℝ)
    with hW₂
  have hW₁nn : ∀ s ∈ Ioo (|r - t|) (r + t), 0 ≤ W₁ s := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := le_trans habs (le_of_lt hs.1)
    rw [hW₁]
    exact mul_nonneg (Real.rpow_nonneg hs0 _)
      (Real.rpow_nonneg (by linarith [hs.1]) _)
  have hW₂nn : ∀ s ∈ Ioo (|r - t|) (r + t), 0 ≤ W₂ s := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := le_trans habs (le_of_lt hs.1)
    rw [hW₂]
    exact mul_nonneg (Real.rpow_nonneg hs0 _)
      (Real.rpow_nonneg (by linarith [hs.2]) _)
  -- the pointwise kernel bound
  have hpoint : ∀ s ∈ Ioo (|r - t|) (r + t),
      ENNReal.ofReal (2 * brsKernelTwo t r s * ‖f₀ s‖) ≤
        ENNReal.ofReal (c * (W₁ s * ‖f₀ s‖)) +
          ENNReal.ofReal (c * (W₂ s * ‖f₀ s‖)) := by
    intro s hs
    have hker := brsKernelTwo_le_sum hr ht1 (le_of_lt hs.1) (le_of_lt hs.2)
    have hfn : (0 : ℝ) ≤ ‖f₀ s‖ := norm_nonneg _
    have h1nn : 0 ≤ W₁ s := hW₁nn s hs
    have h2nn : 0 ≤ W₂ s := hW₂nn s hs
    have h2K : 2 * brsKernelTwo t r s ≤ c * (W₁ s + W₂ s) := by
      have hmul := mul_le_mul_of_nonneg_left hker (by norm_num : (0:ℝ) ≤ 2)
      calc 2 * brsKernelTwo t r s
          ≤ 2 * (2 / (Real.sqrt 3 * r) *
              (s ^ (1 / 2 : ℝ) * (s - |r - t|) ^ (-(1 / 2) : ℝ) +
                s ^ (1 / 2 : ℝ) * (r + t - s) ^ (-(1 / 2) : ℝ))) := hmul
        _ = c * (W₁ s + W₂ s) := by
            rw [hc, hW₁, hW₂]
            ring
    have hstep : 2 * brsKernelTwo t r s * ‖f₀ s‖ ≤
        c * (W₁ s * ‖f₀ s‖) + c * (W₂ s * ‖f₀ s‖) := by
      calc 2 * brsKernelTwo t r s * ‖f₀ s‖ ≤ (c * (W₁ s + W₂ s)) * ‖f₀ s‖ :=
            mul_le_mul_of_nonneg_right h2K hfn
        _ = c * (W₁ s * ‖f₀ s‖) + c * (W₂ s * ‖f₀ s‖) := by ring
    refine le_trans (ENNReal.ofReal_le_ofReal hstep) (le_of_eq ?_)
    rw [ENNReal.ofReal_add (mul_nonneg hcpos.le (mul_nonneg h1nn hfn))
      (mul_nonneg hcpos.le (mul_nonneg h2nn hfn))]
  have hmono : (∫⁻ s in Ioo (|r - t|) (r + t),
      ENNReal.ofReal (2 * brsKernelTwo t r s * ‖f₀ s‖)) ≤
      ∫⁻ s in Ioo (|r - t|) (r + t),
        (ENNReal.ofReal (c * (W₁ s * ‖f₀ s‖)) +
          ENNReal.ofReal (c * (W₂ s * ‖f₀ s‖))) := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
    exact hpoint s hs
  refine le_trans hmono ?_
  -- split the two pieces
  have hmeas₁ : Measurable fun s : ℝ => ENNReal.ofReal (c * (W₁ s * ‖f₀ s‖)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    rw [hW₁]
    exact measurable_const.mul (((by fun_prop : Measurable fun s : ℝ =>
      s ^ (1 / 2 : ℝ)).mul
      (by fun_prop : Measurable fun s : ℝ =>
        (s - |r - t|) ^ (-(1 / 2) : ℝ))).mul hf₀.norm.measurable)
  rw [lintegral_add_left' hmeas₁.aemeasurable]
  -- each piece is an interval integral
  have hint₁ : IntervalIntegrable (fun s => c * (W₁ s * ‖f₀ s‖)) volume
      (|r - t|) (r + t) := by
    rw [hW₁]
    exact ((intervalIntegrable_weight_left_mul hf₀ (|r - t|) (r + t)).congr
      (fun s _ => by ring)).const_mul c
  have hint₂ : IntervalIntegrable (fun s => c * (W₂ s * ‖f₀ s‖)) volume
      (|r - t|) (r + t) := by
    rw [hW₂]
    exact ((intervalIntegrable_weight_right_mul hf₀ (|r - t|) (r + t)).congr
      (fun s _ => by ring)).const_mul c
  have hnn₁ : ∀ s ∈ Ioo (|r - t|) (r + t), 0 ≤ c * (W₁ s * ‖f₀ s‖) := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := le_trans habs (le_of_lt hs.1)
    rw [hW₁]
    have h1 : (0 : ℝ) ≤ s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs0 _
    have h2 : (0 : ℝ) ≤ (s - |r - t|) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_nonneg (by linarith [hs.1]) _
    have h3' : (0 : ℝ) ≤ ‖f₀ s‖ := norm_nonneg _
    positivity
  have hnn₂ : ∀ s ∈ Ioo (|r - t|) (r + t), 0 ≤ c * (W₂ s * ‖f₀ s‖) := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := le_trans habs (le_of_lt hs.1)
    rw [hW₂]
    have h1 : (0 : ℝ) ≤ s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs0 _
    have h2 : (0 : ℝ) ≤ (r + t - s) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_nonneg (by linarith [hs.2]) _
    have h3' : (0 : ℝ) ≤ ‖f₀ s‖ := norm_nonneg _
    positivity
  rw [lintegral_Ioo_eq_ofReal_intervalIntegral hab hint₁ hnn₁,
    lintegral_Ioo_eq_ofReal_intervalIntegral hab hint₂ hnn₂]
  -- compare with the two operators
  have hmemt : t ∈ E ∩ Ioo (r / 2) (3 * r / 2) := ⟨htE, ht1, ht2⟩
  have hcr : c * r = 4 / Real.sqrt 3 := by
    rw [hc]
    field_simp
  have hpiece : ∀ (W : ℝ → ℝ) (Wop : ℝ → ℝ)
      (hWeq : ∀ s : ℝ, 0 < s → ((Wop s : ℝ) : ℂ) *
        brsProfileSub 2 p (absProfile f₀) s = ((W s : ℝ) : ℂ) * absProfile f₀ s)
      (hWnn : ∀ s ∈ Icc (|r - t|) (r + t), 0 ≤ W s * ‖f₀ s‖)
      (Mop : ENNReal)
      (hMop : ENNReal.ofReal (r⁻¹ * ‖∫ s in |r - t|..(r + t),
        ((Wop s : ℝ) : ℂ) * brsProfileSub 2 p (absProfile f₀) s‖) ≤ Mop),
      ENNReal.ofReal (∫ s in |r - t|..(r + t), c * (W s * ‖f₀ s‖)) ≤
        ENNReal.ofReal (4 / Real.sqrt 3) * Mop := by
    intro W Wop hWeq hWnn Mop hMop
    have hcongr : (∫ s in |r - t|..(r + t),
        ((Wop s : ℝ) : ℂ) * brsProfileSub 2 p (absProfile f₀) s) =
        ((∫ s in |r - t|..(r + t), W s * ‖f₀ s‖ : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr_ae
        (Filter.Eventually.of_forall fun s hs => ?_)
      have hmin : (0 : ℝ) ≤ min (|r - t|) (r + t) := le_min habs (by linarith)
      have hs0 : 0 < s := lt_of_le_of_lt hmin (Set.mem_Ioc.mp hs).1
      rw [hWeq s hs0, absProfile]
      push_cast
      ring
    have hnorm : ‖∫ s in |r - t|..(r + t),
        ((Wop s : ℝ) : ℂ) * brsProfileSub 2 p (absProfile f₀) s‖ =
        ∫ s in |r - t|..(r + t), W s * ‖f₀ s‖ := by
      rw [hcongr, Complex.norm_real,
        Real.norm_of_nonneg (intervalIntegral.integral_nonneg hab hWnn)]
    rw [hnorm] at hMop
    have hconst : (∫ s in |r - t|..(r + t), c * (W s * ‖f₀ s‖)) =
        c * ∫ s in |r - t|..(r + t), W s * ‖f₀ s‖ := by
      rw [intervalIntegral.integral_const_mul]
    rw [hconst]
    have hsplit : c * ∫ s in |r - t|..(r + t), W s * ‖f₀ s‖ =
        (4 / Real.sqrt 3) * (r⁻¹ * ∫ s in |r - t|..(r + t), W s * ‖f₀ s‖) := by
      rw [← hcr]
      field_simp
    rw [hsplit, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' le_rfl hMop
  have hleft := hpiece W₁ (fun s => s ^ (1 / 2 - 1 / p) *
      (s - |r - t|) ^ (-(1 / 2) : ℝ))
    (fun s hs => brsMainTwoLeft_integrand hp (absProfile f₀) hs)
    (fun s hs => by
      have hs0 : (0 : ℝ) ≤ s := le_trans habs hs.1
      rw [hW₁]
      have h1 : (0 : ℝ) ≤ s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs0 _
      have h2 : (0 : ℝ) ≤ (s - |r - t|) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_nonneg (by linarith [hs.1]) _
      have h3' : (0 : ℝ) ≤ ‖f₀ s‖ := norm_nonneg _
      positivity)
    (brsMainTwoLeft E p (brsProfileSub 2 p (absProfile f₀)) r)
    (by
      rw [brsMainTwoLeft]
      exact le_iSup₂_of_le t hmemt le_rfl)
  have hright := hpiece W₂ (fun s => s ^ (1 / 2 - 1 / p) *
      (r + t - s) ^ (-(1 / 2) : ℝ))
    (fun s hs => brsMainTwoRight_integrand hp (absProfile f₀) hs)
    (fun s hs => by
      have hs0 : (0 : ℝ) ≤ s := le_trans habs hs.1
      rw [hW₂]
      have h1 : (0 : ℝ) ≤ s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs0 _
      have h2 : (0 : ℝ) ≤ (r + t - s) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_nonneg (by linarith [hs.2]) _
      have h3' : (0 : ℝ) ≤ ‖f₀ s‖ := norm_nonneg _
      positivity)
    (brsMainTwoRight E p (brsProfileSub 2 p (absProfile f₀)) r)
    (by
      rw [brsMainTwoRight]
      exact le_iSup₂_of_le t hmemt le_rfl)
  calc ENNReal.ofReal (∫ s in |r - t|..(r + t), c * (W₁ s * ‖f₀ s‖)) +
        ENNReal.ofReal (∫ s in |r - t|..(r + t), c * (W₂ s * ‖f₀ s‖))
      ≤ ENNReal.ofReal (4 / Real.sqrt 3) *
          brsMainTwoLeft E p (brsProfileSub 2 p (absProfile f₀)) r +
          ENNReal.ofReal (4 / Real.sqrt 3) *
            brsMainTwoRight E p (brsProfileSub 2 p (absProfile f₀)) r :=
        add_le_add hleft hright
    _ = ENNReal.ofReal (4 / Real.sqrt 3) *
          (brsMainTwoLeft E p (brsProfileSub 2 p (absProfile f₀)) r +
            brsMainTwoRight E p (brsProfileSub 2 p (absProfile f₀)) r) := by
        rw [mul_add]

end Prop46

end

end Auto.Spherical.FractalDilations.BRSRadial
