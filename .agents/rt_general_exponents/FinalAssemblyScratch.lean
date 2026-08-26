import LeanSpherical.Auto.Spherical.RieszThorin

noncomputable section

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace Auto.Spherical.RieszThorin.Scratch

/-- Direct endpoint-only diagonal Riesz--Thorin assembly: the homogeneous
finite-simple core is completed through the finite-exponent `Lp` density
extension.  This is intentionally stated for a raw simple-function operator,
because the conclusion constructs its canonical bounded `Lp` extension. -/
theorem diagonal_rieszThorin_extension
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace Complex E]
    {μ : Measure α} {ν : Measure β}
    {P₀ P₁ P₀star P₁star : ENNReal}
    [ENNReal.HolderConjugate P₀ P₀star]
    [ENNReal.HolderConjugate P₁ P₁star]
    (T : (SimpleFunc α E) →ₗ[Complex] (β → Complex))
    {A₀ A₁ : ENNReal} (hA₀ : A₀ < ⊤) (hA₁ : A₁ < ⊤)
    (hTmeas : ∀ u, AEStronglyMeasurable (T u) ν)
    (hT₀ : ∀ u, eLpNorm (T u) P₀ ν ≤ A₀ * eLpNorm (u : α → E) P₀ μ)
    (hT₁ : ∀ u, eLpNorm (T u) P₁ ν ≤ A₁ * eLpNorm (u : α → E) P₁ μ)
    {p θ : Real} (hp : 1 < p) (hθ : θ ∈ Set.Ioo (0 : Real) 1)
    (hmidInput : p * recipBlend θ (P₀⁻¹).toReal (P₁⁻¹).toReal = 1)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ S : Lp E (ENNReal.ofReal p) μ →L[Complex] Lp Complex (ENNReal.ofReal p) ν,
      ‖S‖ ≤ (A₀ ^ (1 - θ) * A₁ ^ θ).toReal ∧
      ∀ (f : SimpleFunc α E) (hf : MemLp (f : α → E) (ENNReal.ofReal p) μ),
        MemLp (T f) (ENNReal.ofReal p) ν ∧ S (hf.toLp f) =ᵐ[ν] T f := by
  let C : ENNReal := A₀ ^ (1 - θ) * A₁ ^ θ
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hpenn0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ.2.le) hA₀.ne)
      (ENNReal.rpow_lt_top_of_nonneg hθ.1.le hA₁.ne)
  apply exists_rawLpExtension_of_midpoint T hpenn0 ENNReal.ofReal_ne_top hC hTmeas
  intro f hf
  simpa only [C] using
    finiteSimpleRieszThorin_diagonal_eLpNorm_homogeneous
      (P₀ := P₀) (P₁ := P₁) (P₀star := P₀star) (P₁star := P₁star)
      T hA₀ hA₁ hTmeas hT₀ hT₁ hp hθ hmidInput f hf

end Auto.Spherical.RieszThorin.Scratch
