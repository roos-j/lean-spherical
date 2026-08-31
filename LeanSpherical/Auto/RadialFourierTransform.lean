import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Constructions.HaarToSphere
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
