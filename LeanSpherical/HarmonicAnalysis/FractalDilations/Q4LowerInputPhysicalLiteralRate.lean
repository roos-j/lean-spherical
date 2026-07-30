/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4LowerInputLiteralRate
import LeanSpherical.HarmonicAnalysis.FractalDilations.AbsoluteDyadicPhysicalEndpoint

/-!
# Physical lower-input Q4 source at a fixed cutoff

For the lower-input part of the Q4 argument the relevant `L¹ → L∞` input is
the physical shell estimate of size `2^j`, not the much larger Fourier-ball
bound.  This file inserts that literal endpoint into the fixed-cutoff lower
Q4 interpolation layer.  Thus the only remaining frequency calculation in
an application is a scalar comparison of the displayed coefficient with a
geometric sequence.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Set ENNReal

noncomputable section

/-- Insert the actual physical `L¹ → L∞` endpoint into the lower-input Q4
calculation.  The cutoff is supplied by the caller and is shared with both
Q4 `L²` estimates. -/
theorem exists_q4_lower_activeDyadic_strong_of_fixed_ltwo_rates_of_physical
    {d : Nat} {E : Set Real} {p r0 r1 q : Real}
    (hd : 0 < d) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hp1 : 1 < p) (hp2 : p < 2) (hr0 : 0 < r0) (hr1 : 0 < r1)
    (hq0q : q4LowerWeakOutputExponent p r0 < q)
    (hqq1 : q < q4LowerWeakOutputExponent p r1)
    {CT0 rho0 CT1 rho1 : ENNReal}
    (hCT0 : CT0 < ⊤) (hCT1 : CT1 < ⊤)
    (hrho0 : rho0 < 1) (hrho1 : rho1 < 1)
    (hrate0 : ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean d) Complex,
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal r0) volume ≤
        CT0 * rho0 ^ j * ENNReal.ofReal
          (Real.sqrt (∫ x, ‖(f : Euclidean d → Complex) x‖ ^ (2 : Nat))))
    (hrate1 : ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean d) Complex,
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal r1) volume ≤
        CT1 * rho1 ^ j * ENNReal.ofReal
          (Real.sqrt (∫ x, ‖(f : Euclidean d → Complex) x‖ ^ (2 : Nat)))) :
    ∃ D : Real, 0 < D ∧
      ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean d) Complex,
        ∀ I : Real, I = ∫ x, ‖(f : Euclidean d → Complex) x‖ ^ p → 0 < I →
        eLpNorm (fractalDyadicBandpassMaximal d E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal q) volume ≤
          q4LowerStrongCoefficient (D * (2 : Real) ^ j)
            ((CT0 * rho0 ^ j).toReal) ((CT1 * rho1 ^ j).toReal)
            p r0 r1 q * ENNReal.ofReal (q4LowerInputScale I p) := by
  obtain ⟨D, hD, hphysical⟩ :=
    exists_absoluteDyadicBandpass_lone_linf_endpoint hd E hE phi hphiOne hphiZero
  refine ⟨D, hD, ?_⟩
  apply q4_lower_activeDyadic_strong_of_fixed_ltwo_rates
    hd hE phi hphiOne hphiZero (fun j => D * (2 : Real) ^ j)
  · intro j
    exact mul_pos hD (pow_pos (by norm_num) j)
  · intro j _hj g x
    exact hphysical j g x
  · exact hp1
  · exact hp2
  · exact hr0
  · exact hr1
  · exact hq0q
  · exact hqq1
  · exact hCT0
  · exact hCT1
  · exact hrho0
  · exact hrho1
  · exact hrate0
  · exact hrate1

/-- The finite-norm version of the physical lower-input source.  Its scalar
premise contains only the explicit physical factor `D * 2^j` and the two
literal Q4 `L²` rates. -/
theorem exists_q4_lower_activeDyadic_memLp_and_eLpNorm_of_fixed_ltwo_rates_of_physical
    {d : Nat} {E : Set Real} {p r0 r1 q : Real}
    (hd : 0 < d) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hp1 : 1 < p) (hp2 : p < 2) (hr0 : 0 < r0) (hr1 : 0 < r1)
    (hq0q : q4LowerWeakOutputExponent p r0 < q)
    (hqq1 : q < q4LowerWeakOutputExponent p r1)
    {CT0 rho0 CT1 rho1 : ENNReal}
    (hCT0 : CT0 < ⊤) (hCT1 : CT1 < ⊤)
    (hrho0 : rho0 < 1) (hrho1 : rho1 < 1)
    (hrate0 : ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean d) Complex,
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal r0) volume ≤
        CT0 * rho0 ^ j * ENNReal.ofReal
          (Real.sqrt (∫ x, ‖(f : Euclidean d → Complex) x‖ ^ (2 : Nat))))
    (hrate1 : ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean d) Complex,
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal r1) volume ≤
        CT1 * rho1 ^ j * ENNReal.ofReal
          (Real.sqrt (∫ x, ‖(f : Euclidean d → Complex) x‖ ^ (2 : Nat))))
    {C rho : ENNReal} (hCtop : C < ⊤) (hrho : rho < 1)
    (hcoefficient : ∀ D : Real, 0 < D → ∀ j : Nat, 1 ≤ j →
      q4LowerStrongCoefficient (D * (2 : Real) ^ j)
        ((CT0 * rho0 ^ j).toReal) ((CT1 * rho1 ^ j).toReal)
        p r0 r1 q ≤ C * rho ^ j) :
    ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean d) Complex,
      MemLp (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal q) volume ≤
        (C * rho ^ j) *
          eLpNorm (f : Euclidean d → Complex) (ENNReal.ofReal p) volume := by
  obtain ⟨D, hD, hphysical⟩ :=
    exists_absoluteDyadicBandpass_lone_linf_endpoint hd E hE phi hphiOne hphiZero
  apply q4_lower_activeDyadic_memLp_and_eLpNorm_of_fixed_ltwo_rates
    hd hE phi hphiOne hphiZero (fun j => D * (2 : Real) ^ j)
  · intro j
    exact mul_pos hD (pow_pos (by norm_num) j)
  · intro j _hj g x
    exact hphysical j g x
  · exact hp1
  · exact hp2
  · exact hr0
  · exact hr1
  · exact hq0q
  · exact hqq1
  · exact hCT0
  · exact hCT1
  · exact hrho0
  · exact hrho1
  · exact hrate0
  · exact hrate1
  · exact hCtop
  · exact hrho
  · exact hcoefficient D hD

/-- A summable lower-input `Q4` rate for one fixed cutoff.  The only scalar
input left after the physical `L¹ → L∞` and the two strict `L² → Lʳ` estimates
is the displayed decay of their literal layer-cake coefficient. -/
theorem exists_q4_lower_activeDyadic_strict_dyadic_rate_of_physical
    {d : Nat} {E : Set Real} {p r0 r1 q : Real}
    (hd : 0 < d) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hp1 : 1 < p) (hp2 : p < 2) (hr0 : 0 < r0) (hr1 : 0 < r1)
    (hq0q : q4LowerWeakOutputExponent p r0 < q)
    (hqq1 : q < q4LowerWeakOutputExponent p r1)
    {CT0 rho0 CT1 rho1 : ENNReal}
    (hCT0 : CT0 < ⊤) (hCT1 : CT1 < ⊤)
    (hrho0 : rho0 < 1) (hrho1 : rho1 < 1)
    (hrate0 : ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean d) Complex,
      MemLp (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal r0) volume ∧
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal r0) volume ≤
        CT0 * rho0 ^ j * ENNReal.ofReal
          (Real.sqrt (∫ x, ‖(f : Euclidean d → Complex) x‖ ^ (2 : Nat))))
    (hrate1 : ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean d) Complex,
      MemLp (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal r1) volume ∧
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal r1) volume ≤
        CT1 * rho1 ^ j * ENNReal.ofReal
          (Real.sqrt (∫ x, ‖(f : Euclidean d → Complex) x‖ ^ (2 : Nat))))
    (hcoefficient : ∃ C rho : ENNReal, C < ⊤ ∧ rho < 1 ∧
      ∀ D : Real, 0 < D → ∀ j : Nat, 1 ≤ j →
        q4LowerStrongCoefficient (D * (2 : Real) ^ j)
          ((CT0 * rho0 ^ j).toReal) ((CT1 * rho1 ^ j).toReal)
          p r0 r1 q ≤ C * rho ^ j) :
    ∃ C rho : ENNReal, C < ⊤ ∧ rho < 1 ∧
      ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean d) Complex,
        MemLp (fractalDyadicBandpassMaximal d E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal q) volume ∧
        eLpNorm (fractalDyadicBandpassMaximal d E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal q) volume ≤
          (C * rho ^ j) *
            eLpNorm (f : Euclidean d → Complex) (ENNReal.ofReal p) volume := by
  obtain ⟨C, rho, hCtop, hrho, hcoefficient⟩ := hcoefficient
  refine ⟨C, rho, hCtop, hrho, ?_⟩
  exact exists_q4_lower_activeDyadic_memLp_and_eLpNorm_of_fixed_ltwo_rates_of_physical
    (C := C) (rho := rho) hd hE phi hphiOne hphiZero hp1 hp2 hr0 hr1 hq0q hqq1
    hCT0 hCT1 hrho0 hrho1
    (fun j hj f => (hrate0 j hj f).2)
    (fun j hj f => (hrate1 j hj f).2)
    hCtop hrho (fun D hD j hj => hcoefficient D hD j hj)

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
