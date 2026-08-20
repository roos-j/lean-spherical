import LeanSpherical.Codex.Spherical.RieszThorin
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace ScratchInterpolation

open MeasureTheory ENNReal
open scoped ENNReal

theorem memLp_of_power_interpolation
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {P₀ P₁ P : ENNReal} {θ : Real} {y : α → E}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hrecip : (P₀ / ENNReal.ofReal (1 - θ))⁻¹ +
        (P₁ / ENNReal.ofReal θ)⁻¹ = P⁻¹)
    (hy₀ : MemLp y P₀ μ) (hy₁ : MemLp y P₁ μ) :
    MemLp y P μ := by
  let q₀ : ENNReal := P₀ / ENNReal.ofReal (1 - θ)
  let q₁ : ENNReal := P₁ / ENNReal.ofReal θ
  have hθnonneg : 0 ≤ θ := hθ0.le
  have hone_sub_nonneg : 0 ≤ 1 - θ := by linarith
  have hu : MemLp (fun x => ‖y x‖ ^ (1 - θ)) q₀ μ := by
    simpa only [q₀, ENNReal.toReal_ofReal hone_sub_nonneg] using
      hy₀.norm_rpow_div (ENNReal.ofReal (1 - θ))
  have hv : MemLp (fun x => ‖y x‖ ^ θ) q₁ μ := by
    simpa only [q₁, ENNReal.toReal_ofReal hθnonneg] using
      hy₁.norm_rpow_div (ENNReal.ofReal θ)
  let r : ENNReal := (q₀⁻¹ + q₁⁻¹)⁻¹
  letI : ENNReal.HolderTriple q₀ q₁ r := ENNReal.HolderTriple.of q₀ q₁
  have huv : MemLp (fun x => ‖y x‖ ^ (1 - θ) * ‖y x‖ ^ θ) r μ :=
    hv.mul' hu
  have hpow : MemLp (fun x => ‖y x‖) r μ := by
    apply huv.ae_eq
    filter_upwards with x
    by_cases hx : ‖y x‖ = 0
    · rw [hx]
      simp [Real.zero_rpow (sub_pos.mpr hθ1).ne', Real.zero_rpow hθ0.ne']
    · have hxpos : 0 < ‖y x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      calc
        ‖y x‖ ^ (1 - θ) * ‖y x‖ ^ θ = ‖y x‖ ^ ((1 - θ) + θ) :=
          (Real.rpow_add hxpos _ _).symm
        _ = ‖y x‖ := by simp
  have hrP : r = P := by
    apply inv_injective
    simpa only [r, inv_inv, q₀, q₁] using hrecip
  rw [hrP] at hpow
  exact (memLp_norm_iff hy₀.1).mp hpow

end ScratchInterpolation

namespace ScratchInterpolation

open MeasureTheory ENNReal
open scoped ENNReal
open Codex.Spherical.RieszThorin

theorem reciprocal_power_interpolation_identity
    {P₀ P₁ P₀star P₁star : ENNReal}
    [ENNReal.HolderConjugate P₀ P₀star]
    [ENNReal.HolderConjugate P₁ P₁star]
    {p θ : Real} (hp : 0 < p) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hmid : p * recipBlend θ (P₀⁻¹).toReal (P₁⁻¹).toReal = 1) :
    (P₀ / ENNReal.ofReal (1 - θ))⁻¹ +
        (P₁ / ENNReal.ofReal θ)⁻¹ = (ENNReal.ofReal p)⁻¹ := by
  have hP₀ : P₀ ≠ 0 := ENNReal.HolderConjugate.ne_zero P₀ P₀star
  have hP₁ : P₁ ≠ 0 := ENNReal.HolderConjugate.ne_zero P₁ P₁star
  have honeθ : 0 < 1 - θ := sub_pos.mpr hθ1
  rw [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top)
      (Or.inl (ENNReal.ofReal_pos.mpr honeθ).ne'),
    ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top)
      (Or.inl (ENNReal.ofReal_pos.mpr hθ0).ne'),
    ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hP₀),
    ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hP₁),
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_add]
  · rw [← ENNReal.ofReal_inv_of_pos hp]
    congr 1
    have hblend : recipBlend θ (P₀⁻¹).toReal (P₁⁻¹).toReal = p⁻¹ := by
      calc
        recipBlend θ (P₀⁻¹).toReal (P₁⁻¹).toReal = 1 / p :=
          (eq_div_iff hp.ne').mpr (by simpa [mul_comm] using hmid)
        _ = p⁻¹ := one_div _
    calc
      (P₀⁻¹).toReal * (1 - θ) + (P₁⁻¹).toReal * θ =
          recipBlend θ (P₀⁻¹).toReal (P₁⁻¹).toReal := by
            simp only [recipBlend]
            ring
      _ = p⁻¹ := hblend
  · exact mul_nonneg ENNReal.toReal_nonneg honeθ.le
  · exact mul_nonneg ENNReal.toReal_nonneg hθ0.le

end ScratchInterpolation
