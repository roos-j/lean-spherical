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

end

end Auto.Spherical.FractalDilations.BRSRadial
