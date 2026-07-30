/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4FullProductMaximalBridge
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The finite-interval Minkowski step for the literal derivative correction

The active-cell sampling argument leaves an integral over one dyadic cell.
This file contains the measure-theoretic part of the paper's argument: a
uniform fixed-offset `L^q` estimate for a jointly measurable nonnegative
family gives the corresponding `L^q` estimate for its interval integral.

The first theorem is deliberately stated with product integrability exposed.
The second discharges that condition from fibrewise integrability and the
uniform root-moment bound.  Thus the derivative application need not posit a
variation estimate: it supplies the actual finite family at each offset and
uses Tonelli together with Hölder on the interval.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set ENNReal

noncomputable section

private theorem q4_integral_rpow_le_of_root_le
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (F : X -> Real) {q A : Real}
    (hFnonneg : forall x, 0 <= F x) (hq : 0 < q)
    (hroot : (integral fun x => F x ^ q ∂mu) ^ (1 / q) <= A) :
    (integral fun x => F x ^ q ∂mu) <= A ^ q := by
  have hnonneg : 0 <= integral (fun x => F x ^ q) ∂mu := by
    apply integral_nonneg
    intro x
    exact Real.rpow_nonneg (hFnonneg x) q
  calc
    (integral fun x => F x ^ q ∂mu) =
        ((integral fun x => F x ^ q ∂mu) ^ (1 / q)) ^ q := by
      rw [show 1 / q = q⁻¹ by ring]
      exact (Real.rpow_inv_rpow hnonneg hq.ne').symm
    _ <= A ^ q := Real.rpow_le_rpow (Real.rpow_nonneg _ _) hroot hq.le

private theorem q4_holder_power_identity
    {q r delta F : Real} (hq : 0 < q)
    (hqr : q.HolderConjugate r) (hdelta : 0 <= delta) (hF : 0 <= F) :
    (F ^ (1 / q) * delta ^ (1 / r)) ^ q = delta ^ (q - 1) * F := by
  rw [Real.mul_rpow (Real.rpow_nonneg F _) (Real.rpow_nonneg delta _)]
  have hFpow : (F ^ (1 / q)) ^ q = F := by
    rw [show 1 / q = q⁻¹ by ring]
    exact Real.rpow_inv_rpow hF hq.ne'
  rw [hFpow]
  have hdeltapow : (delta ^ (1 / r)) ^ q = delta ^ (q - 1) := by
    rw [← Real.rpow_mul hdelta (1 / r) q]
    congr 1
    calc
      (1 / r) * q = q / r := by ring
      _ = q - 1 := hqr.div_conj_eq_sub_one
  rw [hdeltapow]
  ring

private theorem q4_delta_power_identity
    {q delta A : Real} (hq : 0 < q) (hdelta : 0 < delta) :
    delta ^ (q - 1) * (delta * A ^ q) = delta ^ q * A ^ q := by
  calc
    delta ^ (q - 1) * (delta * A ^ q) =
        (delta ^ (q - 1) * delta) * A ^ q := by ring
    _ = delta ^ ((q - 1) + 1) * A ^ q := by
      rw [Real.rpow_add hdelta (q - 1) 1, Real.rpow_one]
    _ = delta ^ q * A ^ q := by ring

private theorem q4_delta_A_root_identity
    {q delta A : Real} (hq : 0 < q) (hdelta : 0 <= delta) (hA : 0 <= A) :
    (delta ^ q * A ^ q) ^ (1 / q) = delta * A := by
  rw [Real.mul_rpow (Real.rpow_nonneg delta q) (Real.rpow_nonneg A q)]
  rw [show 1 / q = q⁻¹ by ring]
  rw [Real.rpow_inv_rpow hdelta hq.ne', Real.rpow_inv_rpow hA hq.ne']

/-- Fibrewise `L^q` integrability and a uniform root-moment estimate give
integrability of the literal `q`-power on the interval/product measure.  The
finite interval is important here: it is exactly what makes the constant
majorant integrable after Tonelli. -/
theorem integrable_uncurry_rpow_of_uniform_interval_root_bound
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (delta : Real) {q A : Real} (H : Real -> X -> Real)
    (hdelta : 0 < delta) (hq : 1 < q) (hA : 0 <= A)
    (hHmeas : Measurable (Function.uncurry H))
    (hHnonneg : forall u x, 0 <= H u x)
    (hfibint : forall u, u ∈ Ioc (0 : Real) delta ->
      Integrable (fun x => H u x ^ q) mu)
    (hroot : forall u, u ∈ Ioc (0 : Real) delta ->
      (integral fun x => H u x ^ q ∂mu) ^ (1 / q) <= A) :
    Integrable (fun z : Real × X => H z.1 z.2 ^ q)
      ((volume.restrict (Ioc (0 : Real) delta)).prod mu) := by
  let nu : Measure Real := volume.restrict (Ioc (0 : Real) delta)
  let F : Real × X -> Real := fun z => H z.1 z.2 ^ q
  have hFmeas : Measurable F := by
    exact (continuous_id.rpow_const (fun _ => Or.inr hq.le)).measurable.comp hHmeas
  have hFae : AEStronglyMeasurable F (nu.prod mu) :=
    hFmeas.aestronglyMeasurable
  have hFnormIntMeas : AEStronglyMeasurable
      (fun u => integral (fun x => ‖F (u, x)‖) ∂mu) nu := by
    simpa only using hFae.norm.integral_prod_right'
  have hnuReal : nu.real univ = delta := by
    dsimp only [nu]
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hdelta.le]
  have hfibae : ∀ᵐ u ∂nu, Integrable (fun x => F (u, x)) mu := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simpa only [F] using hfibint u hu
  have hnormIntBound : ∀ᵐ u ∂nu,
      integral (fun x => ‖F (u, x)‖) ∂mu <= A ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hbound := q4_integral_rpow_le_of_root_le mu (fun x => H u x)
      (fun x => hHnonneg u x) (lt_trans zero_lt_one hq) (hroot u hu)
    calc
      integral (fun x => ‖F (u, x)‖) ∂mu =
          integral (fun x => H u x ^ q) ∂mu := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (hHnonneg u x) q)]
      _ <= A ^ q := hbound
  have hFnormInt : Integrable
      (fun u => integral (fun x => ‖F (u, x)‖) ∂mu) nu := by
    apply Integrable.mono' (integrable_const (A ^ q))
    · exact hFnormIntMeas
    · filter_upwards [hnormIntBound] with u hu
      rw [Real.norm_of_nonneg
        (integral_nonneg fun x => norm_nonneg (F (u, x))),
        Real.norm_of_nonneg (Real.rpow_nonneg hA q)]
      exact hu
  have hprod : Integrable F (nu.prod mu) :=
    (integrable_prod_iff hFae).mpr ⟨hfibae, hFnormInt⟩
  simpa only [nu, F] using hprod

/-- The literal finite-interval Minkowski estimate used after active-cell
sampling.  It has no variation hypothesis: the only analytic input is the
fixed-offset root bound for the jointly measurable family. -/
theorem intervalIntegral_eLpNorm_le_of_uniform_root_bound
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (delta : Real) {q A : Real} (H : Real -> X -> Real)
    (hdelta : 0 < delta) (hq : 1 < q) (hA : 0 <= A)
    (hHmeas : Measurable (Function.uncurry H))
    (hHnonneg : forall u x, 0 <= H u x)
    (hprod : Integrable (fun z : Real × X => H z.1 z.2 ^ q)
      ((volume.restrict (Ioc (0 : Real) delta)).prod mu))
    (hroot : forall u, u ∈ Ioc (0 : Real) delta ->
      (integral fun x => H u x ^ q ∂mu) ^ (1 / q) <= A) :
    MemLp (fun x => ∫ u in (0 : Real)..delta, H u x)
      (ENNReal.ofReal q) mu /\
      eLpNorm (fun x => ∫ u in (0 : Real)..delta, H u x)
        (ENNReal.ofReal q) mu <= ENNReal.ofReal (delta * A) := by
  let nu : Measure Real := volume.restrict (Ioc (0 : Real) delta)
  let V : X -> Real := fun x => ∫ u in (0 : Real)..delta, H u x
  let F : Real × X -> Real := fun z => H z.1 z.2 ^ q
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hFmeas : Measurable F := by
    exact (continuous_id.rpow_const (fun _ => Or.inr hq.le)).measurable.comp hHmeas
  have hHae : AEStronglyMeasurable (Function.uncurry H) (nu.prod mu) :=
    hHmeas.aestronglyMeasurable
  have hHswap : AEStronglyMeasurable
      (fun z : X × Real => H z.2 z.1) (mu.prod nu) := by
    simpa only [Function.comp_apply] using hHae.prod_swap
  have hVmeas : AEStronglyMeasurable V mu := by
    simpa only [V, nu, intervalIntegral.integral_of_le hdelta.le] using
      hHswap.integral_prod_right'
  have hVpowmeas : AEStronglyMeasurable (fun x => V x ^ q) mu :=
    (continuous_id.rpow_const (fun _ => Or.inr hq.le)).comp_aestronglyMeasurable hVmeas
  have hprod' : Integrable F (nu.prod mu) := by
    simpa only [nu, F] using hprod
  have hFint : Integrable (fun x => integral (fun u => H u x ^ q) ∂nu) mu := by
    simpa only [F] using hprod'.integral_prod_right
  have hFslice : ∀ᵐ x ∂mu, Integrable (fun u => H u x ^ q) nu := by
    simpa only [F] using hprod'.prod_left_ae
  have hFnonneg (x : X) : 0 <= integral (fun u => H u x ^ q) ∂nu := by
    apply integral_nonneg
    intro u
    exact Real.rpow_nonneg (hHnonneg u x) q
  have hVnonneg (x : X) : 0 <= V x := by
    dsimp only [V]
    rw [intervalIntegral.integral_of_le hdelta.le]
    exact integral_nonneg (fun u => hHnonneg u x)
  let r : Real := Real.conjExponent q
  have hqr : q.HolderConjugate r := Real.HolderConjugate.conjExponent hq
  have hnuReal : nu.real univ = delta := by
    dsimp only [nu]
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hdelta.le]
  have hpoint : ∀ᵐ x ∂mu, V x ^ q <=
      delta ^ (q - 1) * integral (fun u => H u x ^ q) ∂nu := by
    filter_upwards [hFslice] with x hx
    have hsliceMeas : Measurable (fun u => H u x) :=
      hHmeas.comp (measurable_id.prodMk measurable_const)
    have hsliceLp : MemLp (fun u => H u x) (ENNReal.ofReal q) nu := by
      apply (integrable_norm_rpow_iff hsliceMeas.aestronglyMeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr hqpos) ENNReal.ofReal_ne_top).mp
      refine hx.congr ?_
      filter_upwards with u
      rw [Real.norm_of_nonneg (hHnonneg u x)]
    have honeLp : MemLp (fun _ : Real => (1 : Real)) (ENNReal.ofReal r) nu :=
      memLp_const 1
    have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hqr
      (Eventually.of_forall fun u => hHnonneg u x)
      (Eventually.of_forall fun _ : Real => zero_le_one) hsliceLp honeLp
    have hholder' : integral (fun u => H u x) ∂nu <=
        (integral (fun u => H u x ^ q) ∂nu) ^ (1 / q) * delta ^ (1 / r) := by
      simpa [hnuReal] using hholder
    have hpow := Real.rpow_le_rpow (hVnonneg x) hholder' hq.le
    have hVeq : V x = integral (fun u => H u x) ∂nu := by
      simp only [V, nu, intervalIntegral.integral_of_le hdelta.le]
    calc
      V x ^ q = (integral (fun u => H u x) ∂nu) ^ q := by rw [hVeq]
      _ <= ((integral (fun u => H u x ^ q) ∂nu) ^ (1 / q) *
          delta ^ (1 / r)) ^ q := hpow
      _ = delta ^ (q - 1) * integral (fun u => H u x ^ q) ∂nu :=
        q4_holder_power_identity hqpos hqr hdelta.le (hFnonneg x)
  have hVpowint : Integrable (fun x => V x ^ q) mu := by
    apply Integrable.mono' (hFint.const_mul (delta ^ (q - 1)))
    · exact hVpowmeas
    · filter_upwards [hpoint] with x hx
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hVnonneg x) q),
        Real.norm_of_nonneg
          (mul_nonneg (Real.rpow_nonneg hdelta.le (q - 1)) (hFnonneg x))]
      exact hx
  have hVmem : MemLp V (ENNReal.ofReal q) mu := by
    apply (integrable_norm_rpow_iff hVmeas
      (ENNReal.ofReal_ne_zero_iff.mpr hqpos) ENNReal.ofReal_ne_top).mp
    refine hVpowint.congr ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (hVnonneg x)]
  have hFouterInt : Integrable (fun u => integral (fun x => H u x ^ q) ∂mu) nu := by
    simpa only [F] using hprod'.integral_prod_left
  have hFouterBound : ∀ᵐ u ∂nu,
      integral (fun x => H u x ^ q) ∂mu <= A ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact q4_integral_rpow_le_of_root_le mu (fun x => H u x)
      (fun x => hHnonneg u x) hqpos (hroot u hu)
  have hnuConst : integral (fun _ : Real => A ^ q) ∂nu = delta * A ^ q := by
    rw [integral_const]
    simpa only [hnuReal, smul_eq_mul, mul_one]
  have houter : integral (fun u => integral (fun x => H u x ^ q) ∂mu) ∂nu <=
      delta * A ^ q := by
    calc
      integral (fun u => integral (fun x => H u x ^ q) ∂mu) ∂nu <=
          integral (fun _ : Real => A ^ q) ∂nu :=
        integral_mono_ae hFouterInt (integrable_const _) hFouterBound
      _ = delta * A ^ q := hnuConst
  have hVmoment : integral (fun x => V x ^ q) ∂mu <= delta ^ q * A ^ q := by
    calc
      integral (fun x => V x ^ q) ∂mu <=
          integral (fun x => delta ^ (q - 1) *
            integral (fun u => H u x ^ q) ∂nu) ∂mu :=
        integral_mono_ae hVpowint (hFint.const_mul _) hpoint
      _ = delta ^ (q - 1) *
          integral (fun x => integral (fun u => H u x ^ q) ∂nu) ∂mu := by
        rw [integral_const_mul]
      _ = delta ^ (q - 1) *
          integral (fun u => integral (fun x => H u x ^ q) ∂mu) ∂nu := by
        rw [← integral_integral_swap hprod']
      _ <= delta ^ (q - 1) * (delta * A ^ q) :=
        mul_le_mul_of_nonneg_left houter (Real.rpow_nonneg hdelta.le _)
      _ = delta ^ q * A ^ q := q4_delta_power_identity hqpos hdelta
  have hVroot : (integral (fun x => V x ^ q) ∂mu) ^ (1 / q) <= delta * A := by
    have hpow := Real.rpow_le_rpow
      (integral_nonneg fun x => Real.rpow_nonneg (hVnonneg x) q)
      hVmoment (one_div_nonneg.mpr hq.le)
    calc
      (integral (fun x => V x ^ q) ∂mu) ^ (1 / q) <=
          (delta ^ q * A ^ q) ^ (1 / q) := hpow
      _ = delta * A := q4_delta_A_root_identity hqpos hdelta.le hA
  refine ⟨hVmem, ?_⟩
  simpa only [V] using
    eLpNorm_le_of_rpow_root_moment mu V hqpos hVmem hVroot

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
