/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.ParameterInterior
import LeanSpherical.HarmonicAnalysis.PowerWeights.TypeSet

/-!
# Passing from strict weighted estimates to finite boundary parameters

The analytic upper estimate is naturally strict.  This file contains the
small parameter limit which places every finite non-strict admissible point
in the closure of the strong-type set once that strict estimate is available.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter Set Topology

noncomputable section

/-- A strict implicit estimate at every nearby parameter puts a finite
admissible point in the closure of the weighted type set. -/
theorem finite_admissible_mem_closure_of_strict
    {d : Nat} (hd : 2 ≤ d) (E : Set ℝ) {p α : ℝ}
    (hp : 1 ≤ p) (hcondition : powerWeightEntropyImplicitCondition d E p α)
    (hstrict : ∀ ⦃q a : ℝ⦄, 1 < q →
      max ((a : EReal) + multiplicativeMinkowskiExponent E)
        (multiplicativeLegendreAssouadExponent E
          (((d : ℝ) - 1) * (q - 2) - a)) <
        (↑(((d : ℝ) - 1) * (q - 1)) : EReal) →
      HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType d E q a) :
    (p⁻¹, α / p) ∈
      closure (restrictedNormalizedSphericalMaximalPowerWeightTypeSet d E) := by
  let ε : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  let m : ℝ := (d : ℝ) - 1
  let q : ℕ → ℝ × ℝ := fun n =>
    ((p + ε n)⁻¹, (α + (m / 2) * ε n) / (p + ε n))
  have hε : Tendsto ε atTop (𝓝 0) := by
    dsimp only [ε]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp only [ε]
    positivity
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hpplus : Tendsto (fun n => p + ε n) atTop (𝓝 p) := by
    simpa only [add_zero] using tendsto_const_nhds.add hε
  have hfirst : Tendsto (fun n => (p + ε n)⁻¹) atTop (𝓝 p⁻¹) :=
    hpplus.inv₀ hp_ne
  have hsecond_num : Tendsto (fun n => α + (m / 2) * ε n) atTop (𝓝 α) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hε))
  have hsecond : Tendsto (fun n =>
      (α + (m / 2) * ε n) / (p + ε n)) atTop (𝓝 (α / p)) :=
    hsecond_num.div hpplus hp_ne
  have hq : Tendsto q atTop (𝓝 (p⁻¹, α / p)) := by
    simpa only [q] using hfirst.prodMk_nhds hsecond
  have hq_mem (n : ℕ) : q n ∈
      restrictedNormalizedSphericalMaximalPowerWeightTypeSet d E := by
    have hq_one : 1 < p + ε n := by linarith [hεpos n]
    have hstrict_condition :=
      powerWeightEntropyImplicitCondition_strict_add_half_dim hd E p α (ε n)
        (hεpos n) hcondition
    exact mem_restrictedNormalizedSphericalMaximalPowerWeightTypeSet_iff.mpr
      ⟨p + ε n, α + (m / 2) * ε n, hq_one.le, rfl, rfl,
        hstrict hq_one (by simpa only [m] using hstrict_condition)⟩
  exact mem_closure_of_tendsto hq
    (Filter.Eventually.of_forall hq_mem)

end

end LeanSpherical.HarmonicAnalysis
