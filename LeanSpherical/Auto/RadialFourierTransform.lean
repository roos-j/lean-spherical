import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Radial Fourier transforms

This module contains the measure-theoretic polar-coordinate identity behind
Fourier transforms of norm-radial functions.  It deliberately depends only on
Mathlib.  Analytic estimates for the resulting sphere transform belong in the
components that prove them; the declarations here are exact identities and
integrability transports usable by any such component.

Mathlib uses the Fourier character `exp (-2 pi i <x, xi>)`; consequently its
inverse Fourier transform uses `Real.fourierChar <xi, x>`.
-/

namespace Auto.RadialFourierTransform

open Filter MeasureTheory Metric Set FourierTransform
open scoped FourierTransform Pointwise

noncomputable section

/-- The Euclidean space used by the radial Fourier API. -/
abbrev Euclidean (d : Nat) := EuclideanSpace Real (Fin d)

/-- The unnormalised Euclidean surface measure on the unit sphere. -/
def unitSurfaceMeasure (d : Nat) : Measure (sphere (0 : Euclidean d) 1) :=
  (volume : Measure (Euclidean d)).toSphere

instance (d : Nat) : IsFiniteMeasure (unitSurfaceMeasure d) := by
  unfold unitSurfaceMeasure
  infer_instance

/-- The angular Fourier factor which occurs after passing to polar
coordinates. -/
def sphereFourier (d : Nat) (xi : Euclidean d) : Complex :=
  ∫ omega : sphere (0 : Euclidean d) 1,
    (Real.fourierChar (inner Real (omega : Euclidean d) xi) : Complex)
      ∂unitSurfaceMeasure d

/-- The angular Fourier factor is bounded by the total unit-sphere mass.
Sharper stationary-phase decay is deliberately outside this Mathlib-only
module. -/
theorem norm_sphereFourier_le_surfaceMass (d : Nat) (xi : Euclidean d) :
    ‖sphereFourier d xi‖ ≤ (unitSurfaceMeasure d).real Set.univ := by
  unfold sphereFourier
  calc
    ‖∫ omega : sphere (0 : Euclidean d) 1,
        (Real.fourierChar (inner Real (omega : Euclidean d) xi) : Complex)
          ∂unitSurfaceMeasure d‖ ≤
        ∫ omega : sphere (0 : Euclidean d) 1,
          ‖(Real.fourierChar (inner Real (omega : Euclidean d) xi) : Complex)‖
            ∂unitSurfaceMeasure d := norm_integral_le_integral_norm _
    _ = ∫ _omega : sphere (0 : Euclidean d) 1, (1 : Real)
          ∂unitSurfaceMeasure d := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [Real.fourierChar_apply]
      exact Complex.norm_exp_ofReal_mul_I _
    _ = (unitSurfaceMeasure d).real Set.univ := by simp

/-- Orthogonal changes of coordinates preserve the concrete unit-sphere
surface measure. -/
theorem map_unitSurfaceMeasure_linearIsometry (d : Nat)
    (u : Euclidean d ≃ₗᵢ[Real] Euclidean d) :
    let uSphere : sphere (0 : Euclidean d) 1 ≃ₜ sphere (0 : Euclidean d) 1 :=
      u.toHomeomorph.subtype (fun x => by
        simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
        rw [u.norm_map])
    Measure.map uSphere (unitSurfaceMeasure d) = unitSurfaceMeasure d := by
  dsimp only
  let uSphere : sphere (0 : Euclidean d) 1 ≃ₜ sphere (0 : Euclidean d) 1 :=
    u.toHomeomorph.subtype (fun x => by
      simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
      rw [u.norm_map])
  have huSphere : Measure.map uSphere (unitSurfaceMeasure d) = unitSurfaceMeasure d := by
    apply Measure.ext
    intro s hs
    simp only [unitSurfaceMeasure]
    rw [Measure.map_apply uSphere.continuous.measurable hs,
      Measure.toSphere_apply' (volume : Measure (Euclidean d))
        (hs.preimage uSphere.continuous.measurable),
      Measure.toSphere_apply' (volume : Measure (Euclidean d)) hs]
    congr 1
    let A : Set (Euclidean d) :=
      Ioo (0 : Real) 1 • ((Subtype.val : sphere (0 : Euclidean d) 1 → Euclidean d) ''
        (uSphere ⁻¹' s))
    let B : Set (Euclidean d) :=
      Ioo (0 : Real) 1 • ((Subtype.val : sphere (0 : Euclidean d) 1 → Euclidean d) '' s)
    change (volume : Measure (Euclidean d)) A = (volume : Measure (Euclidean d)) B
    have himage : u '' A = B := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with ⟨r, hr, z', hz', rfl⟩
        rcases hz' with ⟨omega, homega, rfl⟩
        refine ⟨r, hr, uSphere omega, ?_, ?_⟩
        · exact ⟨uSphere omega, homega, rfl⟩
        · simp [uSphere]
      · rintro ⟨r, hr, z, hz, rfl⟩
        rcases hz with ⟨omega, homega, rfl⟩
        refine ⟨r • ((uSphere.symm omega : sphere (0 : Euclidean d) 1) : Euclidean d), ?_, ?_⟩
        · refine ⟨r, hr,
            ((uSphere.symm omega : sphere (0 : Euclidean d) 1) : Euclidean d), ?_, rfl⟩
          refine ⟨uSphere.symm omega, ?_, rfl⟩
          simpa using homega
        · simp [uSphere]
    calc
      (volume : Measure (Euclidean d)) A =
          (volume : Measure (Euclidean d)) (u ⁻¹' (u '' A)) := by
            congr 1
            ext x
            simp
      _ = Measure.map u volume (u '' A) := by
            simpa only [LinearIsometryEquiv.coe_toMeasurableEquiv] using
              (u.toMeasurableEquiv.map_apply (μ := volume) (u '' A)).symm
      _ = (volume : Measure (Euclidean d)) (u '' A) := by
            rw [u.measurePreserving.map_eq]
      _ = (volume : Measure (Euclidean d)) B := by rw [himage]
  simpa only [uSphere] using huSphere

/-- The angular Fourier factor is invariant under orthogonal changes of
frequency coordinates. -/
theorem sphereFourier_linearIsometry (d : Nat)
    (u : Euclidean d ≃ₗᵢ[Real] Euclidean d) (xi : Euclidean d) :
    sphereFourier d (u xi) = sphereFourier d xi := by
  let uSphere : sphere (0 : Euclidean d) 1 ≃ₜ sphere (0 : Euclidean d) 1 :=
    u.toHomeomorph.subtype (fun x => by
      simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph]
      rw [u.norm_map])
  have hmeasure : Measure.map uSphere (unitSurfaceMeasure d) = unitSurfaceMeasure d := by
    simpa only [uSphere] using map_unitSurfaceMeasure_linearIsometry d u
  have hpres : MeasurePreserving uSphere (unitSurfaceMeasure d) (unitSurfaceMeasure d) :=
    ⟨uSphere.continuous.measurable, hmeasure⟩
  have hintegral := hpres.integral_comp uSphere.measurableEmbedding
    (fun omega : sphere (0 : Euclidean d) 1 =>
      (Real.fourierChar (inner Real (omega : Euclidean d) (u xi)) : Complex))
  calc
    sphereFourier d (u xi) =
        ∫ omega : sphere (0 : Euclidean d) 1,
          (Real.fourierChar (inner Real (omega : Euclidean d) (u xi)) : Complex)
            ∂unitSurfaceMeasure d := rfl
    _ = ∫ omega : sphere (0 : Euclidean d) 1,
        (Real.fourierChar (inner Real ((uSphere omega : sphere (0 : Euclidean d) 1) :
          Euclidean d) (u xi)) : Complex) ∂unitSurfaceMeasure d := hintegral.symm
    _ = ∫ omega : sphere (0 : Euclidean d) 1,
        (Real.fourierChar (inner Real (omega : Euclidean d) xi) : Complex)
          ∂unitSurfaceMeasure d := by
      apply integral_congr_ae
      filter_upwards with omega
      have hinter : inner Real ((uSphere omega : sphere (0 : Euclidean d) 1) :
          Euclidean d) (u xi) = inner Real (omega : Euclidean d) xi := by
        change inner Real (u omega) (u xi) = inner Real (omega : Euclidean d) xi
        exact u.inner_map_map _ _
      rw [hinter]
    _ = sphereFourier d xi := rfl

/-- The angular Fourier factor is norm-radial. -/
theorem sphereFourier_eq_of_norm_eq (d : Nat) {xi eta : Euclidean d}
    (hxieta : ‖xi‖ = ‖eta‖) :
    sphereFourier d xi = sphereFourier d eta := by
  let u : Euclidean d ≃ₗᵢ[Real] Euclidean d :=
    Submodule.reflection (Real ∙ (xi - eta))ᗮ
  have hu : u xi = eta := Submodule.reflection_sub hxieta
  calc
    sphereFourier d xi = sphereFourier d (u xi) :=
      (sphereFourier_linearIsometry d u xi).symm
    _ = sphereFourier d eta := by rw [hu]

/-- Central symmetry of the sphere makes its angular Fourier factor even. -/
theorem sphereFourier_neg (d : Nat) (xi : Euclidean d) :
    sphereFourier d (-xi) = sphereFourier d xi := by
  apply sphereFourier_eq_of_norm_eq d
  simp

/-! ### Classical ordinary Bessel series

Mathlib does not currently provide the ordinary Bessel function `J`.  For the
positive radial arguments relevant to spherical Fourier transforms, its
classical power series is nevertheless available directly from Mathlib's real
Gamma function.  We record that series independently of `sphereFourier`: the
comparison between the two objects is a theorem still to be proved, not part
of this definition.

The definition is intended to be used at nonnegative arguments.  On positive
arguments it is the usual real-valued series
`sum (-1)^n (x / 2)^(2*n + nu) / (n! Gamma (n + nu + 1))`.
-/

/-- The `n`th coefficient of the classical ordinary Bessel-`J` power series.
For the intended nonnegative arguments, this is the usual real coefficient
of `J_ν(x)`. -/
noncomputable def ordinaryBesselJTerm (nu x : Real) (n : Nat) : Real :=
  ((-1 : Real) ^ n / (n.factorial : Real) /
      Real.Gamma ((n : Real) + nu + 1)) *
    Real.rpow (x / 2) (2 * (n : Real) + nu)

/-- The classical ordinary Bessel function `J_ν(x)`, defined by its power
series on the nonnegative real axis.  No relation to `sphereFourier` is built
into this definition. -/
noncomputable def ordinaryBesselJ (nu x : Real) : Real :=
  ∑' n : Nat, ordinaryBesselJTerm nu x n

/-- At order zero and argument zero, the ordinary Bessel series is normalized
by `J₀(0) = 1`. -/
theorem ordinaryBesselJ_zero_zero : ordinaryBesselJ 0 0 = 1 := by
  unfold ordinaryBesselJ
  rw [tsum_eq_single 0]
  · norm_num [ordinaryBesselJTerm, Real.Gamma_one]
  · intro n hn
    have hn_pos : 0 < (n : Real) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpow : Real.rpow (0 / 2) (2 * (n : Real) + 0) = 0 := by
      rw [zero_div]
      exact Real.zero_rpow (by positivity)
    calc
      ordinaryBesselJTerm 0 0 n =
          ((-1 : Real) ^ n / (n.factorial : Real) /
              Real.Gamma ((n : Real) + 0 + 1)) *
            Real.rpow (0 / 2) (2 * (n : Real) + 0) := rfl
      _ = 0 := by rw [hpow, mul_zero]

/-- Consecutive coefficients of the ordinary Bessel series satisfy the
classical recurrence.  This is the ratio estimate underlying convergence of
the series on the nonnegative real axis. -/
theorem ordinaryBesselJTerm_succ {nu x : Real} (hnu : 0 ≤ nu) (hx : 0 < x)
    (n : Nat) :
    ordinaryBesselJTerm nu x (n + 1) =
      -ordinaryBesselJTerm nu x n * (x / 2) ^ 2 /
        ((n + 1 : Real) * ((n : Real) + nu + 1)) := by
  have hbase : 0 < x / 2 := by positivity
  have harg : 0 < (n : Real) + nu + 1 := by positivity
  have hfactorial : (((n + 1).factorial : Nat) : Real) =
      (n + 1 : Real) * (n.factorial : Real) := by
    norm_num [Nat.factorial_succ]
  have hgamma : Real.Gamma ((n + 1 : Real) + nu + 1) =
      ((n : Real) + nu + 1) * Real.Gamma ((n : Real) + nu + 1) := by
    rw [show (n + 1 : Real) + nu + 1 = ((n : Real) + nu + 1) + 1 by ring]
    exact Real.Gamma_add_one harg.ne'
  have hpow : Real.rpow (x / 2) (2 * (n + 1 : Real) + nu) =
      Real.rpow (x / 2) (2 * (n : Real) + nu) * (x / 2) ^ 2 := by
    calc
      Real.rpow (x / 2) (2 * (n + 1 : Real) + nu) =
          Real.rpow (x / 2) ((2 * (n : Real) + nu) + 2) := by
            congr 1
            ring
      _ = Real.rpow (x / 2) (2 * (n : Real) + nu) * (x / 2) ^ 2 := by
            calc
              Real.rpow (x / 2) ((2 * (n : Real) + nu) + 2) =
                  Real.rpow (x / 2) (2 * (n : Real) + nu) *
                    (x / 2) ^ (2 : Real) :=
                Real.rpow_add hbase _ _
              _ = _ := by rw [Real.rpow_two]
  have hfactorial_ne : (n.factorial : Real) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hgamma_ne : Real.Gamma ((n : Real) + nu + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg).ne'
  have hn_one_ne : (n + 1 : Real) ≠ 0 := by positivity
  unfold ordinaryBesselJTerm
  rw [hfactorial]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hgamma, hpow, pow_succ]
  field_simp [hfactorial_ne, hgamma_ne, hn_one_ne]

/-- The absolute-value form of `ordinaryBesselJTerm_succ`. -/
theorem norm_ordinaryBesselJTerm_succ {nu x : Real} (hnu : 0 ≤ nu) (hx : 0 < x)
    (n : Nat) :
    ‖ordinaryBesselJTerm nu x (n + 1)‖ =
      ((x / 2) ^ 2 / ((n + 1 : Real) * ((n : Real) + nu + 1))) *
        ‖ordinaryBesselJTerm nu x n‖ := by
  have hleft : 0 < (n + 1 : Real) := by positivity
  have hright : 0 < (n : Real) + nu + 1 := by positivity
  have hden : 0 < (n + 1 : Real) * ((n : Real) + nu + 1) := mul_pos hleft hright
  rw [ordinaryBesselJTerm_succ hnu hx]
  rw [norm_div, norm_mul, norm_neg,
    Real.norm_of_nonneg (sq_nonneg (x / 2)), Real.norm_of_nonneg hden.le]
  ring

/-- The ordinary Bessel series is summable at every positive argument and
nonnegative order.  The proof uses the exact coefficient recurrence and the
geometric ratio test. -/
theorem summable_ordinaryBesselJTerm_of_nonneg_of_pos {nu x : Real}
    (hnu : 0 ≤ nu) (hx : 0 < x) :
    Summable (ordinaryBesselJTerm nu x) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (x / 2) ^ 2 + 1)
  refine summable_of_ratio_norm_eventually_le (by norm_num : (1 / 2 : Real) < 1) ?_
  rw [eventually_atTop]
  refine ⟨N, ?_⟩
  intro n hn
  rw [norm_ordinaryBesselJTerm_succ hnu hx]
  have hNn : 2 * (x / 2) ^ 2 + 1 ≤ (n : Real) :=
    hN.trans (by exact_mod_cast hn)
  have hleft : 0 < (n + 1 : Real) := by positivity
  have hright : 1 ≤ (n : Real) + nu + 1 := by
    nlinarith [(Nat.cast_nonneg n : (0 : Real) ≤ (n : Real))]
  have hden : 0 < (n + 1 : Real) * ((n : Real) + nu + 1) :=
    mul_pos hleft (by linarith)
  have hproduct_ge_first : (n + 1 : Real) * 1 ≤
      (n + 1 : Real) * ((n : Real) + nu + 1) :=
    mul_le_mul_of_nonneg_left hright hleft.le
  have hden_lower : 2 * (x / 2) ^ 2 ≤
      (n + 1 : Real) * ((n : Real) + nu + 1) := by
    linarith
  have hratio : (x / 2) ^ 2 /
      ((n + 1 : Real) * ((n : Real) + nu + 1)) ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    nlinarith
  exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

/-- At zero argument, every positive-index Bessel coefficient of
nonnegative order vanishes. -/
theorem ordinaryBesselJTerm_zero_of_ne_zero {nu : Real} (hnu : 0 ≤ nu)
    {n : Nat} (hn : n ≠ 0) : ordinaryBesselJTerm nu 0 n = 0 := by
  have hn_pos : 0 < (n : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hexponent : 0 < 2 * (n : Real) + nu := by nlinarith
  unfold ordinaryBesselJTerm
  have hpow : Real.rpow (0 / 2) (2 * (n : Real) + nu) = 0 := by
    rw [zero_div]
    exact Real.zero_rpow hexponent.ne'
  rw [hpow, mul_zero]

/-- The classical ordinary Bessel series is summable for every nonnegative
order and nonnegative argument. -/
theorem summable_ordinaryBesselJTerm_of_nonneg {nu x : Real}
    (hnu : 0 ≤ nu) (hx : 0 ≤ x) : Summable (ordinaryBesselJTerm nu x) := by
  rcases hx.eq_or_lt with rfl | hx
  · refine summable_of_ne_finset_zero (s := {0}) ?_
    intro n hn
    apply ordinaryBesselJTerm_zero_of_ne_zero hnu
    simpa using hn
  · exact summable_ordinaryBesselJTerm_of_nonneg_of_pos hnu hx

/-- The real Beta kernel is interval-integrable when both endpoint exponents
are greater than `-1`.  This is obtained from Mathlib's complex Beta-integral
convergence theorem, with the real/complex power conversion made explicit. -/
theorem intervalIntegrable_real_betaKernel {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u : Real => u ^ (a - 1) * (1 - u) ^ (b - 1)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : Real) ≤ 1)]
  have hcomplex := Complex.betaIntegral_convergent (u := (a : Complex)) (v := (b : Complex))
    (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : Real) ≤ 1)] at hcomplex
  refine hcomplex.re.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 ≤ u := hu.1.le
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  norm_cast
  rw [← Complex.ofReal_cpow hu0 (a - 1),
    ← Complex.ofReal_cpow hu1 (b - 1),
    RCLike.re_to_complex, Complex.re_mul_ofReal, Complex.ofReal_re]

/-- The real Beta integral, expressed in Gamma factors.  This is the
one-dimensional integral identity used to turn the cosine series in the
Poisson--Beta representation of `ordinaryBesselJ` into its defining series. -/
theorem real_betaIntegral_eq_gamma_mul_div {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    (∫ u in (0 : Real)..1, u ^ (a - 1) * (1 - u) ^ (b - 1)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  calc
    (∫ u in (0 : Real)..1, u ^ (a - 1) * (1 - u) ^ (b - 1)) =
        (Complex.betaIntegral (a : Complex) (b : Complex)).re := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      conv_rhs =>
        rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num)]
      rw [← RCLike.re_to_complex, ← integral_re]
      · refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
        have hu0 : 0 ≤ u := hu.1.le
        have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
        norm_cast
        rw [← Complex.ofReal_cpow hu0 (a - 1),
          ← Complex.ofReal_cpow hu1 (b - 1),
          RCLike.re_to_complex, Complex.re_mul_ofReal, Complex.ofReal_re]
      · convert! Complex.betaIntegral_convergent (u := (a : Complex)) (v := (b : Complex))
          (by simpa) (by simpa)
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num), IntegrableOn]
    _ = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div]
      · simp_rw [← Complex.ofReal_add a b, Complex.Gamma_ofReal]
        norm_cast
      all_goals simpa

/-- The even cosine moment of the Beta kernel appearing in the Bessel
representation. -/
theorem ordinaryBessel_beta_moment {nu : Real} (hnu : 0 ≤ nu) (n : Nat) :
    (∫ u in (0 : Real)..1,
      u ^ ((n : Real) - 1 / 2) * (1 - u) ^ (nu - 1 / 2)) =
      Real.Gamma ((n : Real) + 1 / 2) * Real.Gamma (nu + 1 / 2) /
        Real.Gamma ((n : Real) + nu + 1) := by
  have ha : 0 < (n : Real) + 1 / 2 := by positivity
  have hb : 0 < nu + 1 / 2 := by linarith
  convert real_betaIntegral_eq_gamma_mul_div ha hb using 1 <;> ring_nf

/-- The Poisson--Beta kernel for a nonnegative Bessel order is integrable on
the unit interval. -/
theorem intervalIntegrable_ordinaryBessel_betaKernel {nu : Real} (hnu : 0 ≤ nu) :
    IntervalIntegrable
      (fun u : Real => Real.rpow u (-1 / 2) * Real.rpow (1 - u) (nu - 1 / 2))
      volume 0 1 := by
  convert intervalIntegrable_real_betaKernel (a := (1 : Real) / 2)
      (b := nu + 1 / 2) (by positivity) (by linarith) using 1
  simp only [Real.rpow_eq_pow]
  ring

/-- The half-integer Gamma normalization which converts a Beta moment into
the factorial coefficient in the ordinary Bessel series. -/
theorem ordinaryBessel_gamma_half_factorial_identity (n : Nat) :
    Real.Gamma ((n : Real) + 1 / 2) * (n.factorial : Real) * (4 : Real) ^ n =
      Real.sqrt Real.pi * ((2 * n).factorial : Real) := by
  induction n with
  | zero => norm_num [Real.Gamma_one_half_eq]
  | succ n ih =>
    have hgamma_arg : (n : Real) + 1 / 2 ≠ 0 := by positivity
    have hfactorial : ((2 * (n + 1)).factorial : Real) =
        (2 * (n : Real) + 2) * (2 * (n : Real) + 1) * ((2 * n).factorial : Real) := by
      norm_num [show 2 * (n + 1) = 2 * n + 2 by omega, Nat.factorial_succ]
      ring
    rw [show ((n + 1 : Nat) : Real) + 1 / 2 = ((n : Real) + 1 / 2) + 1 by
          norm_num; ring,
      Real.Gamma_add_one hgamma_arg, Nat.factorial_succ, pow_succ, hfactorial]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      _ = (2 * (n : Real) + 2) * (2 * (n : Real) + 1) *
          (Real.Gamma ((n : Real) + 1 / 2) * (n.factorial : Real) * (4 : Real) ^ n) := by
            ring
      _ = _ := by rw [ih]; ring

/-- The exact coefficient conversion from the cosine--Beta expansion to the
classical ordinary Bessel series. -/
theorem ordinaryBessel_beta_coefficient {nu x : Real} (hnu : 0 ≤ nu) (hx : 0 < x)
    (n : Nat) :
    (Real.rpow (x / 2) nu / (Real.sqrt Real.pi * Real.Gamma (nu + 1 / 2))) *
        (((-1 : Real) ^ n * x ^ (2 * n) / ((2 * n).factorial : Real)) *
          (Real.Gamma ((n : Real) + 1 / 2) * Real.Gamma (nu + 1 / 2) /
            Real.Gamma ((n : Real) + nu + 1))) =
      ordinaryBesselJTerm nu x n := by
  have hbase : 0 < x / 2 := by positivity
  have hgammaNu_pos : 0 < Real.Gamma (nu + 1 / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hgammaN_pos : 0 < Real.Gamma ((n : Real) + nu + 1) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hsqrtpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hfactorial_pos : 0 < ((n.factorial : Nat) : Real) := by positivity
  have hdouble_factorial_pos : 0 < (((2 * n).factorial : Nat) : Real) := by positivity
  have hfour_pos : 0 < (4 : Real) ^ n := by positivity
  have hpow : Real.rpow (x / 2) (2 * (n : Real) + nu) =
      Real.rpow (x / 2) nu * (x ^ (2 * n) / (4 : Real) ^ n) := by
    calc
      Real.rpow (x / 2) (2 * (n : Real) + nu) =
          Real.rpow (x / 2) (nu + 2 * (n : Real)) := by ring_nf
      _ = Real.rpow (x / 2) nu * Real.rpow (x / 2) (2 * (n : Real)) :=
          Real.rpow_add hbase _ _
      _ = Real.rpow (x / 2) nu * (x ^ (2 * n) / (4 : Real) ^ n) := by
        rw [show 2 * (n : Real) = ((2 * n : Nat) : Real) by norm_num]
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_natCast]
        rw [div_pow, show (2 : Real) ^ (2 * n) = (4 : Real) ^ n by
          rw [show 2 * n = n * 2 by omega]
          rw [pow_mul' (2 : Real) n 2]
          norm_num]
  unfold ordinaryBesselJTerm
  rw [hpow]
  have hnormal := ordinaryBessel_gamma_half_factorial_identity n
  have hnormal' : Real.Gamma ((2 * (n : Real) + 1) / 2) * (n.factorial : Real) *
      (4 : Real) ^ n = Real.sqrt Real.pi * ((2 * n).factorial : Real) := by
    convert hnormal using 1
    ring
  field_simp [hgammaNu_pos.ne', hgammaN_pos.ne', hsqrtpi_pos.ne',
    hfactorial_pos.ne', hdouble_factorial_pos.ne', hfour_pos.ne']
  calc
    _ = Real.rpow (x / 2) nu *
        (Real.Gamma ((2 * (n : Real) + 1) / 2) * (n.factorial : Real) *
          (4 : Real) ^ n) := by ring
    _ = _ := by rw [hnormal']; ring

/-! ### Repository-normalized radial Bessel factor

Mathlib currently has no Bessel-`J` special-function API.  The local
`ordinaryBesselJ` series above is independent of the sphere transform, and no
comparison theorem between it and `sphereFourier` has yet been proved.  The
exact object which occurs in the radial Fourier formula is therefore also
recorded directly as the restriction of `sphereFourier` to a unit ray.  Since
`sphereFourier` uses `Real.fourierChar`, this fixes the convention
`exp (-2 pi i <x, xi>)` once and for all.
-/

/-- The scalar spherical-Bessel factor in Mathlib's Fourier normalization.
A unit vector merely selects a ray. -/
noncomputable def brrsRadialBesselFactor
    (d : Nat) (v : Euclidean d) (u : Real) : Complex :=
  sphereFourier d (u • v)

/-- The radial Bessel factor is independent of the selected unit ray. -/
theorem brrsRadialBesselFactor_eq_of_unit
    {d : Nat} {v w : Euclidean d} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (u : Real) :
    brrsRadialBesselFactor d v u = brrsRadialBesselFactor d w u := by
  unfold brrsRadialBesselFactor
  apply sphereFourier_eq_of_norm_eq d
  simp [norm_smul, hv, hw]

/-- Central symmetry makes the radial Bessel factor even in its scalar
argument. -/
theorem brrsRadialBesselFactor_neg
    (d : Nat) (v : Euclidean d) (u : Real) :
    brrsRadialBesselFactor d v (-u) = brrsRadialBesselFactor d v u := by
  unfold brrsRadialBesselFactor
  rw [show (-u) • v = -(u • v) by module, sphereFourier_neg]

/-- After choosing any unit direction, the angular Fourier factor reduces to
the radial frequency on that direction. -/
theorem sphereFourier_eq_norm_smul_unit (d : Nat) (xi v : Euclidean d)
    (hv : ‖v‖ = 1) :
    sphereFourier d xi = sphereFourier d (‖xi‖ • v) := by
  apply sphereFourier_eq_of_norm_eq d
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hv, mul_one]

/-- Orthogonal invariance, the Fourier-stable formulation of radiality. -/
def IsOrthogonallyInvariant {V E : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (f : V → E) : Prop :=
  ∀ A : V ≃ₗᵢ[Real] V, f ∘ A = f

/-- Norm-radiality in a form that immediately supplies orthogonal invariance. -/
def IsNormRadial {V E : Type*} [SeminormedAddCommGroup V] (f : V → E) : Prop :=
  ∀ x y : V, ‖x‖ = ‖y‖ → f x = f y

/-- A norm-radial function is invariant under every orthogonal linear map. -/
theorem IsNormRadial.orthogonallyInvariant
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    {f : V → E} (hf : IsNormRadial f) : IsOrthogonallyInvariant f := by
  unfold IsOrthogonallyInvariant
  intro A
  funext x
  apply hf
  exact A.norm_map x

/-- Every scalar norm profile is norm-radial. -/
theorem isNormRadial_normProfile {V E : Type*} [SeminormedAddCommGroup V]
    (F : Real → E) : IsNormRadial (fun x : V => F ‖x‖) := by
  intro x y hxy
  simpa only using congrArg F hxy

namespace IsOrthogonallyInvariant

/-- Fourier transform preserves orthogonal invariance. -/
theorem fourier {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]
    [NormedAddCommGroup E] [NormedSpace Complex E]
    {f : V → E} (hf : IsOrthogonallyInvariant f) :
    IsOrthogonallyInvariant (𝓕 f) := by
  unfold IsOrthogonallyInvariant at hf ⊢
  intro A
  funext x
  change 𝓕 f (A x) = 𝓕 f x
  rw [← Real.fourier_comp_linearIsometry A f x, hf A]

/-- Inverse Fourier transform preserves orthogonal invariance. -/
theorem fourierInv {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]
    [NormedAddCommGroup E] [NormedSpace Complex E]
    {f : V → E} (hf : IsOrthogonallyInvariant f) :
    IsOrthogonallyInvariant (𝓕⁻ f) := by
  unfold IsOrthogonallyInvariant at hf ⊢
  intro A
  funext x
  change 𝓕⁻ f (A x) = 𝓕⁻ f x
  rw [← Real.fourierInv_comp_linearIsometry A f x, hf A]

end IsOrthogonallyInvariant

/-- Fourier transform preserves the radial symmetry supplied by a norm
profile.  The conclusion is stated as orthogonal invariance, which is the
Fourier-stable formulation and does not require choosing a radial profile for
the transformed function. -/
theorem IsNormRadial.fourier_orthogonallyInvariant
    {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]
    [NormedAddCommGroup E] [NormedSpace Complex E]
    {f : V → E} (hf : IsNormRadial f) :
    IsOrthogonallyInvariant (𝓕 f) :=
  hf.orthogonallyInvariant.fourier

/-- Inverse Fourier transform preserves the radial symmetry supplied by a
norm profile. -/
theorem IsNormRadial.fourierInv_orthogonallyInvariant
    {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]
    [NormedAddCommGroup E] [NormedSpace Complex E]
    {f : V → E} (hf : IsNormRadial f) :
    IsOrthogonallyInvariant (𝓕⁻ f) :=
  hf.orthogonallyInvariant.fourierInv

/-- The polar-coordinate decomposition of Lebesgue integration in a positive
Euclidean dimension. -/
theorem integral_polar_unitSurfaceMeasure {d : Nat} (hd : 0 < d)
    (H : Euclidean d → Complex) :
    (∫ x : Euclidean d, H x) =
      ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real),
        H (p.2.1 • (p.1 : Euclidean d))
          ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
  let i : Fin d := ⟨0, hd⟩
  letI : Nonempty (Fin d) := ⟨i⟩
  calc
    (∫ x : Euclidean d, H x) =
        ∫ x : ({0}ᶜ : Set (Euclidean d)), H x.1 ∂
          ((volume : Measure (Euclidean d)).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl H,
        restrict_compl_singleton]
    _ = ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real),
        (H ∘ Subtype.val ∘ (homeomorphUnitSphereProd (Euclidean d)).symm) p ∂
          (((volume : Measure (Euclidean d)).toSphere).prod
            (Measure.volumeIoiPow (Module.finrank Real (Euclidean d) - 1))) := by
      simpa using
        (volume : Measure (Euclidean d)).measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _)
          (H ∘ Subtype.val ∘ (homeomorphUnitSphereProd (Euclidean d)).symm)
    _ = ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real),
        H (p.2.1 • (p.1 : Euclidean d))
          ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
      simp [unitSurfaceMeasure]

/-- The inverse Fourier transform of a norm-radial function in polar
coordinates.  No integrability assumption is required, since both sides use
the same Bochner integral. -/
theorem fourierInv_radial_eq_polar {d : Nat} (hd : 0 < d)
    (F : Real → Complex) (x : Euclidean d) :
    𝓕⁻ (fun xi : Euclidean d => F ‖xi‖) x =
      ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real),
        Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) • F p.2.1
          ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
  rw [Real.fourierInv_eq, integral_polar_unitSurfaceMeasure hd]
  apply integral_congr_ae
  filter_upwards with p
  have hp : ‖(p.1 : Euclidean d)‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using p.1.property
  have hpos : 0 < (p.2 : Real) := p.2.property
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, hp, mul_one]

/-- The elementary polar majorant for the inverse transform of a norm-radial
function.  It is intentionally only the triangle-inequality bound; all
oscillatory improvements belong to later analytic components. -/
theorem norm_fourierInv_radial_le_integral_norm_polar {d : Nat} (hd : 0 < d)
    (F : Real → Complex) (x : Euclidean d) :
    ‖𝓕⁻ (fun xi : Euclidean d => F ‖xi‖) x‖ ≤
      ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real), ‖F p.2.1‖
        ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
  rw [fourierInv_radial_eq_polar hd F x]
  calc
    ‖∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real),
        Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) • F p.2.1
          ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1)))‖ ≤
        ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real),
          ‖Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) • F p.2.1‖
            ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) :=
      norm_integral_le_integral_norm _
    _ = ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real), ‖F p.2.1‖
          ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
      apply integral_congr_ae
      filter_upwards with p
      change ‖(Real.fourierChar
        (inner Real (p.2.1 • (p.1 : Euclidean d)) x) : Complex) * F p.2.1‖ = ‖F p.2.1‖
      rw [norm_mul, Real.fourierChar_apply, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The forward Fourier transform of a norm-radial function in polar
coordinates.  This is the forward-transform companion to
`fourierInv_radial_eq_polar`; the only difference is the negated output
frequency dictated by Mathlib's Fourier convention. -/
theorem fourier_radial_eq_polar {d : Nat} (hd : 0 < d)
    (F : Real → Complex) (x : Euclidean d) :
    𝓕 (fun xi : Euclidean d => F ‖xi‖) x =
      ∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real),
        Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) (-x)) • F p.2.1
          ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
  have h := fourierInv_radial_eq_polar hd F (-x)
  rw [Real.fourierInv_eq_fourier_neg] at h
  simpa using h

/-- The angular factor in the polar formula is `sphereFourier`. -/
theorem polar_angular_fourierChar_eq_sphereFourier (rho : Real) (x : Euclidean d) :
    (∫ omega : sphere (0 : Euclidean d) 1,
        (Real.fourierChar (inner Real (rho • (omega : Euclidean d)) x) : Complex)
          ∂unitSurfaceMeasure d) =
      sphereFourier d (rho • x) := by
  unfold sphereFourier
  apply integral_congr_ae
  filter_upwards with omega
  simp only [Real.fourierChar_apply, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]

/-- For an integrable radial profile, Fubini turns the inverse Fourier
transform into a one-dimensional radial integral against `sphereFourier`. -/
theorem fourierInv_radial_eq_sphereFourier_integral
    {d : Nat} (hd : 0 < d) (F : Real → Complex) (x : Euclidean d)
    (hInt : Integrable (fun p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) =>
      Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) • F p.2.1)
      ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1)))) :
    𝓕⁻ (fun xi : Euclidean d => F ‖xi‖) x =
      ∫ rho : Ioi (0 : Real), sphereFourier d (rho.1 • x) * F rho.1
        ∂Measure.volumeIoiPow (d - 1) := by
  rw [fourierInv_radial_eq_polar hd F x]
  calc
    (∫ p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real),
        Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) • F p.2.1
          ∂((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1)))) =
        ∫ rho : Ioi (0 : Real),
          ∫ omega : sphere (0 : Euclidean d) 1,
            Real.fourierChar (inner Real (rho.1 • (omega : Euclidean d)) x) • F rho.1
              ∂unitSurfaceMeasure d ∂Measure.volumeIoiPow (d - 1) :=
      integral_prod_symm _ hInt
    _ = ∫ rho : Ioi (0 : Real),
          (∫ omega : sphere (0 : Euclidean d) 1,
            (Real.fourierChar (inner Real (rho.1 • (omega : Euclidean d)) x) : Complex)
              ∂unitSurfaceMeasure d) * F rho.1
            ∂Measure.volumeIoiPow (d - 1) := by
      apply integral_congr_ae
      filter_upwards with rho
      change (∫ omega : sphere (0 : Euclidean d) 1,
          (Real.fourierChar (inner Real (rho.1 • (omega : Euclidean d)) x) : Complex) *
            F rho.1 ∂unitSurfaceMeasure d) = _
      rw [integral_mul_const]
    _ = ∫ rho : Ioi (0 : Real), sphereFourier d (rho.1 • x) * F rho.1
          ∂Measure.volumeIoiPow (d - 1) := by
      apply integral_congr_ae
      filter_upwards with rho
      rw [polar_angular_fourierChar_eq_sphereFourier]

/-- For an integrable radial profile, the forward Fourier transform has the
same one-dimensional angular reduction.  This is the forward companion of
`fourierInv_radial_eq_sphereFourier_integral`; the negated output direction is
the only change forced by Mathlib's Fourier convention. -/
theorem fourier_radial_eq_sphereFourier_integral
    {d : Nat} (hd : 0 < d) (F : Real → Complex) (x : Euclidean d)
    (hInt : Integrable (fun p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) =>
      Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) (-x)) • F p.2.1)
      ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1)))) :
    𝓕 (fun xi : Euclidean d => F ‖xi‖) x =
      ∫ rho : Ioi (0 : Real), sphereFourier d (rho.1 • (-x)) * F rho.1
        ∂Measure.volumeIoiPow (d - 1) := by
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using
    (fourierInv_radial_eq_sphereFourier_integral hd F (-x) hInt)

/-- A Schwartz radial multiplier supplies the integrability premise in the
polar/Fubini formula.  This is a literal transport through the polar
homeomorphism: the Fourier character has norm one. -/
theorem integrable_polar_fourierChar_mul_of_schwartz_radial
    {d : Nat} (m : SchwartzMap (Euclidean d) Complex) (F : Real → Complex)
    (hmrad : ∀ xi : Euclidean d, m xi = F ‖xi‖) (x : Euclidean d) :
    Integrable (fun p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) =>
      Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) • F p.2.1)
      ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
  let U : Set (Euclidean d) := {0}ᶜ
  let h : U ≃ₜ (sphere (0 : Euclidean d) 1 × Ioi (0 : Real)) :=
    homeomorphUnitSphereProd (Euclidean d)
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact (measurableSet_singleton _).compl
  have hmU : Integrable (fun z : U => m (z : Euclidean d))
      ((volume : Measure (Euclidean d)).comap (fun z : U => (z : Euclidean d))) := by
    change Integrable ((m : Euclidean d → Complex) ∘ (fun z : U => (z : Euclidean d)))
      ((volume : Measure (Euclidean d)).comap (fun z : U => (z : Euclidean d)))
    rw [← integrableOn_iff_comap_subtypeVal hUmeas]
    exact m.integrable.integrableOn
  let G : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) → Complex :=
    (m : Euclidean d → Complex) ∘ Subtype.val ∘ h.symm
  have hG : Integrable G ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
    have htransport :=
      MeasurePreserving.integrable_comp_emb (g := G)
        ((volume : Measure (Euclidean d)).measurePreserving_homeomorphUnitSphereProd)
        (Homeomorph.measurableEmbedding h)
    have hcomp : Integrable (G ∘ h)
        ((volume : Measure (Euclidean d)).comap (fun z : U => (z : Euclidean d))) := by
      refine hmU.congr (Filter.Eventually.of_forall ?_)
      intro z
      dsimp [G, Function.comp_def]
      rw [Homeomorph.symm_apply_apply]
    simpa [unitSurfaceMeasure] using htransport.mp hcomp
  have hGpolar : Integrable (fun p : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) =>
      m (p.2.1 • (p.1 : Euclidean d)))
      ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
    refine hG.congr (Filter.Eventually.of_forall ?_)
    intro p
    change m (((h.symm p : U) : Euclidean d)) = m (p.2.1 • (p.1 : Euclidean d))
    change m (((homeomorphUnitSphereProd (Euclidean d)).symm p :
      ({0}ᶜ : Set (Euclidean d))) : Euclidean d) = m (p.2.1 • (p.1 : Euclidean d))
    rfl
  let H : sphere (0 : Euclidean d) 1 × Ioi (0 : Real) → Complex := fun p =>
    (Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) : Complex) *
      m (p.2.1 • (p.1 : Euclidean d))
  have hHcont : Continuous H := by
    dsimp [H]
    fun_prop
  have hH : Integrable H ((unitSurfaceMeasure d).prod (Measure.volumeIoiPow (d - 1))) := by
    refine hGpolar.mono hHcont.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro p
    have hchar : ‖(Real.fourierChar
        (inner Real (p.2.1 • (p.1 : Euclidean d)) x) : Complex)‖ = 1 := by
      rw [Real.fourierChar_apply]
      exact Complex.norm_exp_ofReal_mul_I _
    simpa only [H, norm_mul, hchar, one_mul] using
      (le_refl ‖m (p.2.1 • (p.1 : Euclidean d))‖)
  refine hH.congr (Filter.Eventually.of_forall ?_)
  intro p
  have hp : ‖(p.1 : Euclidean d)‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using p.1.property
  have hnorm : ‖p.2.1 • (p.1 : Euclidean d)‖ = p.2.1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.2, hp, mul_one]
  dsimp [H]
  change (Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) : Complex) *
      m (p.2.1 • (p.1 : Euclidean d)) =
    (Real.fourierChar (inner Real (p.2.1 • (p.1 : Euclidean d)) x) : Complex) * F p.2.1
  rw [hmrad (p.2.1 • (p.1 : Euclidean d)), hnorm]

end

end Auto.RadialFourierTransform
