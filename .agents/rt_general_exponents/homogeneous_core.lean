import LeanSpherical.Codex.Spherical.RieszThorin
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace ScratchHomogeneous

open MeasureTheory ENNReal
open scoped ENNReal
open Codex.Spherical.RieszThorin

theorem finiteSimpleRieszThorin_diagonal_eLpNorm_homogeneous
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
    (f : SimpleFunc α E) (hf : MemLp (f : α → E) (ENNReal.ofReal p) μ) :
    eLpNorm (T f) (ENNReal.ofReal p) ν ≤
      (A₀ ^ (1 - θ) * A₁ ^ θ) * eLpNorm (f : α → E) (ENNReal.ofReal p) μ := by
  let N : ENNReal := eLpNorm (f : α → E) (ENNReal.ofReal p) μ
  let K : ENNReal := A₀ ^ (1 - θ) * A₁ ^ θ
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hpenn0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hNtop : N ≠ ⊤ := by
    exact hf.eLpNorm_ne_top
  change eLpNorm (T f) (ENNReal.ofReal p) ν ≤ K * N
  by_cases hNzero : N = 0
  · have hfae : (f : α → E) =ᵐ[μ] 0 :=
      (eLpNorm_eq_zero_iff hf.1 hpenn0).mp hNzero
    have hfP₀zero : eLpNorm (f : α → E) P₀ μ = 0 := by
      rw [eLpNorm_congr_ae hfae]
      exact eLpNorm_zero
    have hTfP₀zero : eLpNorm (T f) P₀ ν = 0 := by
      apply le_zero_iff.mp
      simpa [hfP₀zero] using hT₀ f
    have hTfae : T f =ᵐ[ν] 0 :=
      (eLpNorm_eq_zero_iff (hTmeas f)
        (ENNReal.HolderConjugate.ne_zero P₀ P₀star)).mp hTfP₀zero
    have hTfzero : eLpNorm (T f) (ENNReal.ofReal p) ν = 0 := by
      rw [eLpNorm_congr_ae hTfae]
      exact eLpNorm_zero
    rw [hTfzero, hNzero, mul_zero]
  · have hNpos : 0 < N := pos_iff_ne_zero.mpr hNzero
    have hNrealpos : 0 < N.toReal := ENNReal.toReal_pos hNzero hNtop
    let c : Complex := ((N.toReal)⁻¹ : Real)
    have hcnorm : ‖c‖ₑ = N⁻¹ := by
      dsimp [c]
      rw [← ofReal_norm, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg),
        ENNReal.ofReal_inv_of_pos hNrealpos,
        ENNReal.ofReal_toReal hNtop]
    have hfc : MemLp ((c • f : SimpleFunc α E) : α → E) (ENNReal.ofReal p) μ := by
      simpa only [SimpleFunc.coe_smul] using hf.const_smul c
    have hfcunit : eLpNorm ((c • f : SimpleFunc α E) : α → E)
        (ENNReal.ofReal p) μ ≤ 1 := by
      rw [SimpleFunc.coe_smul, eLpNorm_const_smul, hcnorm]
      exact le_of_eq (ENNReal.inv_mul_cancel hNzero hNtop)
    have hscaled := finiteSimpleRieszThorin_diagonal_eLpNorm
      (P₀ := P₀) (P₁ := P₁) (P₀star := P₀star) (P₁star := P₁star)
      T hA₀ hA₁ hTmeas hT₀ hT₁ hp hθ hmidInput (c • f) hfc hfcunit
    have hscaled' : N⁻¹ * eLpNorm (T f) (ENNReal.ofReal p) ν ≤ K := by
      simpa only [K, T.map_smul, eLpNorm_const_smul, hcnorm] using hscaled
    calc
      eLpNorm (T f) (ENNReal.ofReal p) ν =
          N * (N⁻¹ * eLpNorm (T f) (ENNReal.ofReal p) ν) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hNzero hNtop, one_mul]
      _ ≤ N * K := mul_le_mul_right hscaled' N
      _ = K * N := mul_comm _ _

end ScratchHomogeneous
