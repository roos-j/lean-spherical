/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.RadialWaveKernel

/-!
# Removing the polar radial power measure in every dimension

The polar-coordinate formula uses `Measure.volumeIoiPow n`.  For the wave
kernel argument it is important to expose its literal Lebesgue density before
performing radial integration by parts.  The existing dimension-three result
is the case `n = 2`; this file gives the same exact Bochner-integral identity
for every natural power.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set

noncomputable section

/-- On positive radii, `volumeIoiPow n` is Lebesgue measure with complex
density `rho ^ n`. -/
theorem integral_volumeIoiPow_eq_setIntegral
    (n : Nat) (G : Real -> Complex) :
    (∫ rho : Ioi (0 : Real), G rho.1 ∂Measure.volumeIoiPow n) =
      ∫ rho in Ioi (0 : Real), ((rho ^ n : Real) : Complex) * G rho := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    (measurable_subtype_coe.pow_const _).real_toNNReal]
  calc
    (∫ rho : Ioi (0 : Real), (rho.1 ^ n).toNNReal • G rho.1
        ∂Measure.comap Subtype.val volume) =
        ∫ rho in Ioi (0 : Real), (rho ^ n).toNNReal • G rho := by
          simpa using
            (integral_subtype_comap measurableSet_Ioi
              (fun rho : Real => (rho ^ n).toNNReal • G rho))
    _ = ∫ rho in Ioi (0 : Real), ((rho ^ n : Real) : Complex) * G rho := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro rho hrho
          change (((rho ^ n).toNNReal : Complex) * G rho) =
            ((rho ^ n : Real) : Complex) * G rho
          rw [Real.coe_toNNReal _ (pow_nonneg hrho.le _)]

/-- A positive-radius Lebesgue integral may be restricted to a compact
annulus when the integrand vanishes away from that annulus. -/
theorem setIntegral_Ioi_eq_setIntegral_Icc_of_eq_zero_outside_general
    {a b : Real} (ha : 0 < a) (F : Real -> Complex)
    (hzero : ∀ rho, rho ∈ Ioi (0 : Real) -> rho ∉ Icc a b -> F rho = 0) :
    (∫ rho in Ioi (0 : Real), F rho) = ∫ rho in Icc a b, F rho := by
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with rho
  by_cases hrho : rho ∈ Icc a b
  · have hpos : rho ∈ Ioi (0 : Real) := mem_Ioi.mpr (lt_of_lt_of_le ha hrho.1)
    rw [Set.indicator_of_mem hpos, Set.indicator_of_mem hrho]
  · rw [Set.indicator_of_notMem hrho]
    by_cases hpos : rho ∈ Ioi (0 : Real)
    · rw [Set.indicator_of_mem hpos, hzero rho hpos hrho]
    · rw [Set.indicator_of_notMem hpos]

/-- The preceding annular restriction in interval-integral notation. -/
theorem setIntegral_Ioi_eq_intervalIntegral_of_eq_zero_outside_general
    {a b : Real} (ha : 0 < a) (hab : a ≤ b) (F : Real -> Complex)
    (hzero : ∀ rho, rho ∈ Ioi (0 : Real) -> rho ∉ Icc a b -> F rho = 0) :
    (∫ rho in Ioi (0 : Real), F rho) = ∫ rho in a..b, F rho := by
  calc
    (∫ rho in Ioi (0 : Real), F rho) = ∫ rho in Icc a b, F rho :=
      setIntegral_Ioi_eq_setIntegral_Icc_of_eq_zero_outside_general ha F hzero
    _ = ∫ rho in Ioc a b, F rho := integral_Icc_eq_integral_Ioc
    _ = ∫ rho in a..b, F rho := (intervalIntegral.integral_of_le hab).symm

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
