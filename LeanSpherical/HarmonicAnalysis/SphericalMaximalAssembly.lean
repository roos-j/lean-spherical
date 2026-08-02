/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.HardyLittlewoodMaximal
import LeanSpherical.HarmonicAnalysis.RelativeDyadicMovingL2
import LeanSpherical.HarmonicAnalysis.SphericalAverages
import LeanSpherical.HarmonicAnalysis.SmoothDyadicPhysical
import LeanSpherical.HarmonicAnalysis.SchwartzData
import LeanSpherical.HarmonicAnalysis.RationalTails
import LeanSpherical.HarmonicAnalysis.InterpolationTail
import LeanSpherical.HarmonicAnalysis.SurfaceCore

/-!
# Relative-frequency spherical maximal reassembly
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory FourierTransform Set Filter
open scoped Convolution FourierTransform Topology

noncomputable section

/-- Measurability of a literal relative annular maximal function.  Compact
support turns the moving surface multiplier into a scaled Schwartz multiplier. -/
private theorem relative_dyadic_bandpass_measurable
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
    AEStronglyMeasurable (relativeBandpassMaximal d φ j f) volume := by
  obtain ⟨ψ, hψ, hψcompact, _⟩ :=
    exists_compactlySupported_schwartzMap_smooth_dyadic_bandpass φ hφone hφzero j
  obtain ⟨χ, hχ⟩ :=
    exists_schwartz_compactSupport_mul_surfaceFourier ψ hψcompact 1
  have hχ' (ξ : Euclidean d) :
      χ ξ = ψ ξ * surfaceFourier d (-ξ) := by
    simpa using hχ ξ
  have hrewrite : relativeBandpassMaximal d φ j f = fun x : Euclidean d =>
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
        χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal := by
    funext x
    dsimp only [relativeBandpassMaximal]
    congr 1
    apply iSup_congr
    intro r
    congr 2
    apply congrArg (fun g : Euclidean d → ℂ => 𝓕⁻ g x)
    funext ξ
    rw [hχ' (r.1 • ξ), hψ]
    rw [show (-(r.1) : ℝ) • ξ = -(r.1 • ξ) by rw [neg_smul]]
    ring
  rw [hrewrite]
  apply (ENNReal.measurable_toReal.comp ?_).aestronglyMeasurable
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_iSup
  intro r
  have hrinv : 0 < r.1⁻¹ := inv_pos.mpr r.2
  have hcont : Continuous (fun x : Euclidean d =>
      𝓕⁻ (fun ξ : Euclidean d => χ (r.1 • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x) := by
    simpa [inv_inv] using
      (continuous_fourierInv_scaled_schwartz_multiplier χ f hrinv)
  exact (ENNReal.continuous_ofReal.comp hcont.norm).lowerSemicontinuous

/-- The literal relative annular maximum is nonnegative. -/
private theorem relative_dyadic_bandpass_nonneg
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ) (j : ℕ)
    (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    0 ≤ relativeBandpassMaximal d φ j f x := by
  exact ENNReal.toReal_nonneg

/-- Express a literal annular maximum through one fixed dyadic multiplier. -/
private theorem relative_dyadic_bandpass_eq_scaled
    {d : ℕ} (φ ψ : SchwartzMap (Euclidean d) ℂ)
    (hψ : ∀ η, ψ η =
      φ (((2 : ℝ) ^ (0 + 1))⁻¹ • η) - φ (((2 : ℝ) ^ 0)⁻¹ • η))
    (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    relativeBandpassMaximal d φ j f x =
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) *
          ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal := by
  dsimp only [relativeBandpassMaximal]
  congr 1
  apply iSup_congr
  intro r
  congr 2
  apply congrArg (fun q : Euclidean d → ℂ => 𝓕⁻ q x)
  funext ξ
  have hscalar : (2 : ℝ)⁻¹ * ((2 : ℝ) ^ j)⁻¹ = ((2 : ℝ) ^ (j + 1))⁻¹ := by
    rw [pow_succ, mul_inv_rev]
  have hfirst : (2 : ℝ)⁻¹ • (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) =
      ((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ) := by
    calc
      (2 : ℝ)⁻¹ • (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) =
          ((2 : ℝ)⁻¹ * ((2 : ℝ) ^ j)⁻¹) • (r.1 • ξ) := smul_smul _ _ _
      _ = _ := by rw [hscalar]
  rw [hψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))]
  simp only [zero_add, pow_one, pow_zero, inv_one, one_smul]
  rw [hfirst]

/-- The weak one endpoint for a literal dyadic annulus. -/
private theorem relative_dyadic_bandpass_weak_one
    {d : ℕ} (hd : 3 ≤ d) (φ : SchwartzMap (Euclidean d) ℂ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
      {a : ℝ}, 0 ≤ a → (∀ x, ‖f x‖ ≤ a) → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * volume {x | s < relativeBandpassMaximal d φ j f x} ≤
        (ENNReal.ofReal
          (D * (2 : ℝ) ^ j *
            (volume (Metric.ball (0 : Euclidean d) 1)).toReal) *
          (ENNReal.ofReal (4 : ℝ)) ^ d) *
          ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  obtain ⟨ψ, hψ⟩ := exists_schwartzMap_smooth_dyadic_bandpass φ 0
  obtain ⟨D, hD, hweak⟩ :=
    exists_iSup_relative_surface_scaled_schwartz_multiplier_weak_one
      (d := d) (by omega) ψ
  refine ⟨D, hD, ?_⟩
  intro j f a ha hfa s hs
  have hset :
      {x | s < relativeBandpassMaximal d φ j f x} =
        {x | s <
          (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) *
              ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [relative_dyadic_bandpass_eq_scaled φ ψ hψ j f x]
  rw [hset]
  exact hweak j f ha hfa hs

/-- The moving-radius square-function endpoint for a literal dyadic annulus. -/
private theorem relative_dyadic_bandpass_strong_two
    {d : ℕ} (hd : 3 ≤ d) (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (hφnorm : ∀ ξ, ‖φ ξ‖ ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      MemLp (relativeBandpassMaximal d φ j f) 2 volume ∧
      (∫ x : Euclidean d, (relativeBandpassMaximal d φ j f x) ^ (2 : ℕ)) ≤
        D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
          ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ) := by
  obtain ⟨D, hD, hglobal⟩ :=
    exists_memLp_two_iSup_relative_dyadic_moving_bandpass_global_exponential
      (n := d) hd φ hφone hφzero hφnorm
  refine ⟨D, hD, ?_⟩
  intro j f
  rcases hglobal j f with ⟨hmem, hbound⟩
  refine ⟨?_, ?_⟩
  · exact hmem
  · calc
      (∫ x : Euclidean d, (relativeBandpassMaximal d φ j f x) ^ (2 : ℕ)) =
          ∫ x : Euclidean d, ‖relativeBandpassMaximal d φ j f x‖ ^ (2 : ℕ) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Real.norm_of_nonneg (relative_dyadic_bandpass_nonneg φ j f x)]
      _ ≤ D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
          ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ) := by
            have hexp : -((d : ℝ) - 2) * (j : ℝ) =
                -(((d : ℝ) - 2) * (j : ℝ)) := by ring
            simpa only [relativeBandpassMaximal, hexp] using hbound

/-- Chebyshev in the precise form used to turn a square estimate into weak type. -/
private theorem weak_two_of_strong_two_for_schwartz
    {d : ℕ} (T : SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ)
    (hTmeas : ∀ f, AEStronglyMeasurable (T f) volume)
    {K : ℝ} (hK : 0 ≤ K)
    (hmem : ∀ f, MemLp (T f) 2 volume)
    (hstrong : ∀ f, (∫ x : Euclidean d, (T f x) ^ (2 : ℕ)) ≤
      K * ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ))
    (f : SchwartzMap (Euclidean d) ℂ) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T f x} ≤
      ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) := by
  have hTint : Integrable (fun x : Euclidean d => (T f x) ^ (2 : ℕ)) volume :=
    (memLp_two_iff_integrable_sq (hTmeas f)).1 (hmem f)
  have hCheb :
      ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T f x} ≤
        ENNReal.ofReal
          (K * ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ)) := by
    calc
      ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T f x} ≤
          ENNReal.ofReal (s ^ (2 : ℕ)) *
            volume {x | ENNReal.ofReal (s ^ (2 : ℕ)) ≤
              ENNReal.ofReal ((T f x) ^ (2 : ℕ))} := by
          apply mul_le_mul_right
          apply measure_mono
          intro x hx
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hs.le hx.le 2)
      _ ≤ ∫⁻ x, ENNReal.ofReal ((T f x) ^ (2 : ℕ)) :=
        mul_meas_ge_le_lintegral₀
          ((hTmeas f).aemeasurable.pow_const 2).ennreal_ofReal
          (ENNReal.ofReal (s ^ (2 : ℕ)))
      _ = ENNReal.ofReal (∫ x : Euclidean d, (T f x) ^ (2 : ℕ)) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hTint
          (Filter.Eventually.of_forall fun x => sq_nonneg (T f x))
      _ ≤ ENNReal.ofReal
          (K * ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ)) :=
        ENNReal.ofReal_le_ofReal (hstrong f)
  have hfMem : MemLp (f : Euclidean d → ℂ) 2 volume := f.memLp 2 volume
  have hfInt : Integrable (fun x : Euclidean d => ‖f x‖ ^ (2 : ℕ)) volume :=
    (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).1 hfMem
  have hInput :
      (∫⁻ x : Euclidean d, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) =
        ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ)) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal hfInt
      (Filter.Eventually.of_forall fun x => sq_nonneg (‖f x‖))
  calc
    ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T f x} ≤
        ENNReal.ofReal
          (K * ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ)) := hCheb
    _ = (ENNReal.ofReal K) *
          (ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ))) := by
      rw [ENNReal.ofReal_mul hK]
    _ = (ENNReal.ofReal K) *
          ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) := by rw [hInput]

/-- The weak square endpoint obtained from the moving-radius square estimate. -/
private theorem relative_dyadic_bandpass_weak_two
    {d : ℕ} (hd : 3 ≤ d) (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (hφnorm : ∀ ξ, ‖φ ξ‖ ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
      {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) *
          volume {x | s < relativeBandpassMaximal d φ j f x} ≤
        ENNReal.ofReal
          (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) *
          ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) := by
  obtain ⟨D, hD, hstrong⟩ :=
    relative_dyadic_bandpass_strong_two hd φ hφone hφzero hφnorm
  refine ⟨D, hD, ?_⟩
  intro j f s hs
  let K : ℝ := D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  simpa only [K] using
    weak_two_of_strong_two_for_schwartz
      (relativeBandpassMaximal d φ j)
      (fun g => relative_dyadic_bandpass_measurable φ hφone hφzero j g)
      hK (fun g => (hstrong j g).1) (fun g => (hstrong j g).2) f hs

/-- The square-endpoint contribution at the dyadic balancing scale. -/
private theorem relative_dyadic_balance_two_power
    {d j : ℕ} {p : ℝ} (hd : 1 ≤ d) :
    ENNReal.ofReal ((2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
        (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) =
      (ENNReal.ofReal (2 : ℝ)) ^
        (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) := by
  have hpow (n : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ n) =
      (ENNReal.ofReal (2 : ℝ)) ^ (n : ℝ) := by
    rw [← Real.rpow_natCast]
    exact (ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).symm
  have hrpow (a : ℝ) : ENNReal.ofReal ((2 : ℝ) ^ a) =
      (ENNReal.ofReal (2 : ℝ)) ^ a :=
    (ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).symm
  have htwo0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
  have htwoT : ENNReal.ofReal (2 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    ENNReal.ofReal ((2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
        (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) =
        (ENNReal.ofReal (2 : ℝ)) ^ (-((d : ℝ) - 2) * (j : ℝ)) *
          ((ENNReal.ofReal (2 : ℝ)) ^ (((d - 1) * j : ℕ) : ℝ)) ^ (2 - p) := by
            rw [hrpow, hpow]
    _ = (ENNReal.ofReal (2 : ℝ)) ^
          (-((d : ℝ) - 2) * (j : ℝ) + (((d - 1) * j : ℕ) : ℝ) * (2 - p)) := by
            rw [← ENNReal.rpow_mul]
            rw [← ENNReal.rpow_add _ _ htwo0 htwoT]
    _ = (ENNReal.ofReal (2 : ℝ)) ^
          (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) := by
            congr 1
            rw [Nat.cast_mul, Nat.cast_sub hd]
            push_cast
            ring

/-- The weak-one contribution at the same dyadic balancing scale. -/
private theorem relative_dyadic_balance_one_power
    {d j : ℕ} {p : ℝ} (hd : 1 ≤ d) :
    ENNReal.ofReal ((2 : ℝ) ^ (j : ℝ)) *
        (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) =
      (ENNReal.ofReal (2 : ℝ)) ^
        (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) := by
  have hpow (n : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ n) =
      (ENNReal.ofReal (2 : ℝ)) ^ (n : ℝ) := by
    rw [← Real.rpow_natCast]
    exact (ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).symm
  have hrpow (a : ℝ) : ENNReal.ofReal ((2 : ℝ) ^ a) =
      (ENNReal.ofReal (2 : ℝ)) ^ a :=
    (ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).symm
  have htwo0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
  have htwoT : ENNReal.ofReal (2 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    ENNReal.ofReal ((2 : ℝ) ^ (j : ℝ)) *
        (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) =
        (ENNReal.ofReal (2 : ℝ)) ^ (j : ℝ) *
          ((ENNReal.ofReal (2 : ℝ)) ^ (((d - 1) * j : ℕ) : ℝ)) ^ (1 - p) := by
            rw [hrpow, hpow]
    _ = (ENNReal.ofReal (2 : ℝ)) ^
          ((j : ℝ) + (((d - 1) * j : ℕ) : ℝ) * (1 - p)) := by
            rw [← ENNReal.rpow_mul]
            rw [← ENNReal.rpow_add _ _ htwo0 htwoT]
    _ = (ENNReal.ofReal (2 : ℝ)) ^
          (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) := by
            congr 1
            rw [Nat.cast_mul, Nat.cast_sub hd]
            push_cast
            ring

/-- Algebraic collection of the two Marcinkiewicz endpoint contributions. -/
private theorem relative_dyadic_balance_one_two
    {d j : ℕ} {p c1 c2 a1 a2 : ℝ} (hd : 1 ≤ d) (hp0 : 0 < p)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (I : ENNReal) :
    ENNReal.ofReal p *
      (4 * ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
          ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) *
            (ENNReal.ofReal a2 * I)) +
        2 * ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
          ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) *
            (ENNReal.ofReal a1 * I))) =
      ENNReal.ofReal (p * (4 * c2 * a2 + 2 * c1 * a1)) *
        (ENNReal.ofReal (2 : ℝ)) ^
          (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I := by
  have hbal2 := relative_dyadic_balance_two_power (j := j) (p := p) hd
  have hbal1 := relative_dyadic_balance_one_power (j := j) (p := p) hd
  have hterm2 :
      4 * ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
          ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) *
            (ENNReal.ofReal a2 * I)) =
        (4 * ENNReal.ofReal c2 * ENNReal.ofReal a2) *
          (ENNReal.ofReal (2 : ℝ)) ^
            (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I := by
    rw [ENNReal.ofReal_mul hc2]
    calc
      4 * (ENNReal.ofReal c2 *
          ENNReal.ofReal ((2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ)))) *
          ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) *
            (ENNReal.ofReal a2 * I)) =
          (4 * ENNReal.ofReal c2 * ENNReal.ofReal a2) *
            (ENNReal.ofReal ((2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
              (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p)) * I := by ring
      _ = _ := by rw [hbal2]
  have hterm1 :
      2 * ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
          ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) *
            (ENNReal.ofReal a1 * I)) =
        (2 * ENNReal.ofReal c1 * ENNReal.ofReal a1) *
          (ENNReal.ofReal (2 : ℝ)) ^
            (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I := by
    rw [ENNReal.ofReal_mul hc1]
    calc
      2 * (ENNReal.ofReal c1 * ENNReal.ofReal ((2 : ℝ) ^ (j : ℝ))) *
          ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) *
            (ENNReal.ofReal a1 * I)) =
          (2 * ENNReal.ofReal c1 * ENNReal.ofReal a1) *
            (ENNReal.ofReal ((2 : ℝ) ^ (j : ℝ)) *
              (ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p)) * I := by ring
      _ = _ := by rw [hbal1]
  have hconst2 : 4 * ENNReal.ofReal c2 * ENNReal.ofReal a2 =
      ENNReal.ofReal (4 * c2 * a2) := by
    calc
      4 * ENNReal.ofReal c2 * ENNReal.ofReal a2 =
          ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal c2 * ENNReal.ofReal a2 := by norm_num
      _ = ENNReal.ofReal ((4 : ℝ) * c2) * ENNReal.ofReal a2 := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = ENNReal.ofReal ((4 : ℝ) * c2 * a2) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hc2)]
  have hconst1 : 2 * ENNReal.ofReal c1 * ENNReal.ofReal a1 =
      ENNReal.ofReal (2 * c1 * a1) := by
    calc
      2 * ENNReal.ofReal c1 * ENNReal.ofReal a1 =
          ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal c1 * ENNReal.ofReal a1 := by norm_num
      _ = ENNReal.ofReal ((2 : ℝ) * c1) * ENNReal.ofReal a1 := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ENNReal.ofReal ((2 : ℝ) * c1 * a1) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hc1)]
  have hcoeff : ENNReal.ofReal p *
      (4 * ENNReal.ofReal c2 * ENNReal.ofReal a2 +
        2 * ENNReal.ofReal c1 * ENNReal.ofReal a1) =
      ENNReal.ofReal (p * (4 * c2 * a2 + 2 * c1 * a1)) := by
    rw [hconst2, hconst1]
    rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg (by norm_num) hc2) ha2)
      (mul_nonneg (mul_nonneg (by norm_num) hc1) ha1)]
    rw [← ENNReal.ofReal_mul hp0.le]
  rw [hterm2, hterm1]
  calc
    ENNReal.ofReal p *
        ((4 * ENNReal.ofReal c2 * ENNReal.ofReal a2) *
            (ENNReal.ofReal (2 : ℝ)) ^
              (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I +
          (2 * ENNReal.ofReal c1 * ENNReal.ofReal a1) *
            (ENNReal.ofReal (2 : ℝ)) ^
              (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I) =
        (ENNReal.ofReal p *
          (4 * ENNReal.ofReal c2 * ENNReal.ofReal a2 +
            2 * ENNReal.ofReal c1 * ENNReal.ofReal a1)) *
          (ENNReal.ofReal (2 : ℝ)) ^
            (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I := by ring
    _ = _ := by rw [hcoeff]

/-- A Schwartz input has the expected real/extended-real rpow integral identity. -/
private theorem schwartz_lintegral_rpow_eq_ofReal_integral
    {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ) {p : ℝ} (hp0 : 0 < p) :
    (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p) =
      ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ p) := by
  have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfMem : MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume :=
    f.memLp (ENNReal.ofReal p) volume
  have hfPowInt : Integrable (fun x : Euclidean d => ‖f x‖ ^ p) volume := by
    have h := hfMem.integrable_norm_rpow hpEN0 hpENT
    simpa only [ENNReal.toReal_ofReal hp0.le] using h
  calc
    (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p) =
        ∫⁻ x : Euclidean d, ENNReal.ofReal (‖f x‖ ^ p) := by
          apply lintegral_congr
          intro x
          exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
    _ = ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ p) :=
      (ofReal_integral_eq_lintegral_ofReal hfPowInt
        (Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (norm_nonneg _) p)).symm

/-- Convert a finite extended-real rpow estimate into the real strong-type form. -/
private theorem memLp_and_integral_of_lintegral_rpow_bound
    {d : ℕ} {p C J : ℝ} (g : Euclidean d → ℝ)
    (hgmeas : AEStronglyMeasurable g volume) (hgnonneg : ∀ x, 0 ≤ g x)
    (hp0 : 0 < p)
    (hbound : (∫⁻ x : Euclidean d, ENNReal.ofReal (g x ^ p)) ≤
      ENNReal.ofReal (C * J))
    (hCJ : 0 ≤ C * J) :
    MemLp g (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, g x ^ p) ≤ C * J := by
  have hleft : (∫⁻ x : Euclidean d, ENNReal.ofReal (g x ^ p)) < ⊤ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  have hMem : MemLp g (ENNReal.ofReal p) volume :=
    memLp_of_lintegral_ofReal_rpow_lt_top g hgmeas.aemeasurable hgnonneg hp0 hleft
  refine ⟨hMem, ?_⟩
  have hpEN0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpENT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgPowInt : Integrable (fun x : Euclidean d => g x ^ p) volume := by
    have h := hMem.integrable_norm_rpow hpEN0 hpENT
    convert h using 1
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hgnonneg x), ENNReal.toReal_ofReal hp0.le]
  have hleft_eq :
      (∫ x : Euclidean d, g x ^ p) =
        (∫⁻ x : Euclidean d, ENNReal.ofReal (g x ^ p)).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hgnonneg x) p)
      hgPowInt.aestronglyMeasurable
  rw [hleft_eq]
  calc
    (∫⁻ x : Euclidean d, ENNReal.ofReal (g x ^ p)).toReal ≤
        (ENNReal.ofReal (C * J)).toReal :=
      (ENNReal.toReal_le_toReal hleft.ne ENNReal.ofReal_ne_top).mpr hbound
    _ = C * J := ENNReal.toReal_ofReal hCJ

/-- Apply the weak one/two interpolation theorem after the rational height split. -/
private theorem relative_dyadic_one_two_interpolation_bound
    {d : ℕ} {p : ℝ}
    (T : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ)
    (hTmeas : ∀ j f, AEStronglyMeasurable (T j f) volume)
    (hTnonneg : ∀ j f x, 0 ≤ T j f x)
    (hT_subadd : ∀ j f g x, T j (f + g) x ≤ T j f x + T j g x)
    (hd : 2 ≤ d) (hp1 : 1 < p) (hp_lt : p < 2) (hp0 : 0 < p)
    {c1 c2 a1 a2 : ℝ}
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hweak1norm : ∀ j (g : SchwartzMap (Euclidean d) ℂ) {s : ℝ}, 0 < s →
      ENNReal.ofReal s * volume {x | s < T j g x} ≤
        ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
          ∫⁻ x, ENNReal.ofReal ‖g x‖)
    (hweak2norm : ∀ j (g : SchwartzMap (Euclidean d) ℂ) {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j g x} ≤
        ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)))
    (hA1 : (ENNReal.ofReal (p - 1))⁻¹ + (ENNReal.ofReal (3 - p))⁻¹ =
      ENNReal.ofReal a1)
    (hA2 : ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹ +
      (ENNReal.ofReal (2 - p))⁻¹ = ENNReal.ofReal a2)
    (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
    (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
      ENNReal.ofReal (p * (4 * c2 * a2 + 2 * c1 * a1)) *
        (ENNReal.ofReal (2 : ℝ)) ^
          (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p := by
  obtain ⟨low, high, hlow, hhigh, hsplit⟩ :=
    exists_schwartz_rational_low_high_family f
  have hprofiles :=
    measurable_rational_low_high_profile_lintegrals f low high hlow hhigh (μ := volume)
  let I : ENNReal := ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p
  have htail2raw :=
    rational_schwartz_low_weighted_tail f low high hlow hhigh hp1 hp_lt
  have htail1raw :=
    rational_schwartz_high_weighted_tail f low high hlow hhigh hp1 hp_lt
  have htail2 :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖low t x‖ ^ (2 : ℕ))) *
          (ENNReal.ofReal t) ^ (p - 3)) ≤ ENNReal.ofReal a2 * I := by
    simpa only [I, hA2] using htail2raw
  have htail1 :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖high t x‖) *
          (ENNReal.ofReal t) ^ (p - 2)) ≤ ENNReal.ofReal a1 * I := by
    simpa only [I, hA1] using htail1raw
  let s : ℝ := (2 : ℝ) ^ ((d - 1) * j)
  have hs : 0 < s := by
    dsimp only [s]
    positivity
  have hinterp := marcinkiewicz_weak_one_two_on_additive_split_scaled
    (Set.univ : Set (SchwartzMap (Euclidean d) ℂ))
    (fun g : SchwartzMap (Euclidean d) ℂ => (g : Euclidean d → ℂ))
    (T j) (fun g x => hTnonneg j g x)
    (by
      intro g h _ _
      filter_upwards with x
      exact hT_subadd j g h x)
    (ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)))
    (ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))))
    (by
      intro g _ s hs
      exact hweak1norm j g hs)
    (by
      intro g _ s hs
      exact hweak2norm j g hs)
    hp1 hp_lt f (hTmeas j f).aemeasurable low high
    (by intro t; simp) (by intro t; simp) (by
      intro t
      ext x
      exact hsplit t x) hprofiles.1 hprofiles.2
    (ENNReal.ofReal a2 * I) (ENNReal.ofReal a1 * I)
    htail2 htail1 s hs
  calc
    (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
        ENNReal.ofReal p *
          (4 * ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
              ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (2 - p) *
                (ENNReal.ofReal a2 * I)) +
            2 * ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
              ((ENNReal.ofReal ((2 : ℝ) ^ ((d - 1) * j))) ^ (1 - p) *
                (ENNReal.ofReal a1 * I))) := by
          simpa only [s] using hinterp
    _ = ENNReal.ofReal (p * (4 * c2 * a2 + 2 * c1 * a1)) *
        (ENNReal.ofReal (2 : ℝ)) ^
          (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) * I :=
      relative_dyadic_balance_one_two (by omega) hp0 hc1 hc2 ha1 ha2 I

/-- Convert the balanced extended-real interpolation estimate to a strong bound. -/
private theorem relative_dyadic_one_two_fixed
    {d : ℕ} {p : ℝ}
    (T : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ)
    (hTmeas : ∀ j f, AEStronglyMeasurable (T j f) volume)
    (hTnonneg : ∀ j f x, 0 ≤ T j f x)
    (hT_subadd : ∀ j f g x, T j (f + g) x ≤ T j f x + T j g x)
    (hd : 2 ≤ d) (hp1 : 1 < p) (hp_lt : p < 2) (hp0 : 0 < p)
    {c1 c2 a1 a2 : ℝ}
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc2pos : 0 < c2)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha2pos : 0 < a2)
    (hweak1norm : ∀ j (g : SchwartzMap (Euclidean d) ℂ) {s : ℝ}, 0 < s →
      ENNReal.ofReal s * volume {x | s < T j g x} ≤
        ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
          ∫⁻ x, ENNReal.ofReal ‖g x‖)
    (hweak2norm : ∀ j (g : SchwartzMap (Euclidean d) ℂ) {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j g x} ≤
        ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)))
    (hA1 : (ENNReal.ofReal (p - 1))⁻¹ + (ENNReal.ofReal (3 - p))⁻¹ =
      ENNReal.ofReal a1)
    (hA2 : ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹ +
      (ENNReal.ofReal (2 - p))⁻¹ = ENNReal.ofReal a2)
    (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
    MemLp (T j f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (T j f x) ^ p) ≤
        p * (4 * c2 * a2 + 2 * c1 * a1) *
          (2 : ℝ) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) *
          ∫ x : Euclidean d, ‖f x‖ ^ p := by
  have hbalanced := relative_dyadic_one_two_interpolation_bound
    T hTmeas hTnonneg hT_subadd hd hp1 hp_lt hp0 hc1 hc2 ha1 ha2
    hweak1norm hweak2norm hA1 hA2 j f
  have hqpos : 0 < p * (4 * c2 * a2 + 2 * c1 * a1) := by
    have hfirst : 0 < 4 * c2 * a2 :=
      mul_pos (mul_pos (by norm_num) hc2pos) ha2pos
    have hbracket : 0 < 4 * c2 * a2 + 2 * c1 * a1 :=
      hfirst.trans_le (le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (by norm_num) hc1) ha1))
    exact mul_pos hp0 hbracket
  let J : ℝ := ∫ x : Euclidean d, ‖f x‖ ^ p
  let C : ℝ := p * (4 * c2 * a2 + 2 * c1 * a1) *
    (2 : ℝ) ^ (-(((d : ℝ) - 1) * p - d) * (j : ℝ))
  have hI :
      (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p) = ENNReal.ofReal J := by
    dsimp only [J]
    exact schwartz_lintegral_rpow_eq_ofReal_integral f hp0
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^
      (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hcoeff :
      ENNReal.ofReal (p * (4 * c2 * a2 + 2 * c1 * a1)) *
          (ENNReal.ofReal (2 : ℝ)) ^
            (-(((d : ℝ) - 1) * p - d) * (j : ℝ)) *
          ∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p =
        ENNReal.ofReal (C * J) := by
    dsimp only [C]
    rw [hI]
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [← ENNReal.ofReal_mul hqpos.le]
    rw [← ENNReal.ofReal_mul (mul_nonneg hqpos.le hpow_nonneg)]
  have hbound :
      (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
        ENNReal.ofReal (C * J) := by
    rw [← hcoeff]
    exact hbalanced
  have hCJ : 0 ≤ C * J := by
    dsimp only [C, J]
    exact mul_nonneg (mul_nonneg hqpos.le hpow_nonneg)
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p)
  simpa only [C, J] using
    memLp_and_integral_of_lintegral_rpow_bound (T j f)
      (hTmeas j f) (hTnonneg j f) hp0 hbound hCJ

/-- Normalize the geometric constants in the weak-one annular endpoint. -/
private theorem relative_dyadic_normalize_weak_one
    {d : ℕ} (T : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ)
    {D V c1 : ℝ} (hD : 0 < D) (hV : 0 ≤ V)
    (hc1 : c1 = D * V * (4 : ℝ) ^ d)
    (hweak : ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
      {a : ℝ}, 0 ≤ a → (∀ x, ‖f x‖ ≤ a) → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * volume {x | s < T j f x} ≤
        (ENNReal.ofReal (D * (2 : ℝ) ^ j * V) *
          (ENNReal.ofReal (4 : ℝ)) ^ d) *
          ∫⁻ x, ENNReal.ofReal ‖f x‖) :
    ∀ j (g : SchwartzMap (Euclidean d) ℂ) {s : ℝ}, 0 < s →
      ENNReal.ofReal s * volume {x | s < T j g x} ≤
        ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
          ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
  intro j g s hs
  have hbound : ∀ x : Euclidean d, ‖g x‖ ≤ ‖g.toBoundedContinuousFunction‖ := by
    intro x
    change ‖g.toBoundedContinuousFunction x‖ ≤ ‖g.toBoundedContinuousFunction‖
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  have h := hweak j g (norm_nonneg _) hbound hs
  have hcoeff :
      ENNReal.ofReal (D * (2 : ℝ) ^ j * V) * (ENNReal.ofReal (4 : ℝ)) ^ d =
        ENNReal.ofReal (c1 * (2 : ℝ) ^ j) := by
    rw [hc1]
    rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4)]
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (mul_nonneg hD.le (pow_nonneg (by norm_num) _)) hV)]
    congr 1
    ring
  rw [Real.rpow_natCast]
  simpa only [hcoeff] using h

/-- The interpolation regime strictly between the weak one and square endpoints. -/
private theorem relative_dyadic_strong_type_one_two
    {d : ℕ} (hd : 3 ≤ d) {p : ℝ}
    (hp : (d : ℝ) / ((d : ℝ) - 1) < p) (hp_lt : p < 2)
    (T : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ)
    (hTmeas : ∀ j f, AEStronglyMeasurable (T j f) volume)
    (hTnonneg : ∀ j f x, 0 ≤ T j f x)
    (hT_subadd : ∀ j f g x, T j (f + g) x ≤ T j f x + T j g x)
    (hT_weak_one :
      ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
        {a : ℝ}, 0 ≤ a → (∀ x, ‖f x‖ ≤ a) → ∀ {s : ℝ}, 0 < s →
        ENNReal.ofReal s * volume {x | s < T j f x} ≤
          (ENNReal.ofReal
            (D * (2 : ℝ) ^ j *
              (volume (Metric.ball (0 : Euclidean d) 1)).toReal) *
            (ENNReal.ofReal (4 : ℝ)) ^ d) *
            ∫⁻ x, ENNReal.ofReal ‖f x‖)
    (hT_weak_two :
      ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
        {s : ℝ}, 0 < s →
        ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j f x} ≤
          ENNReal.ofReal
            (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) *
            ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) :
    ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧
      ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
        MemLp (T j f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (T j f x) ^ p) ≤
          A * (2 : ℝ) ^ (-ε * j) * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  have hd2 : 2 ≤ d := by omega
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hp1 : 1 < p := by
    have hone : 1 < (d : ℝ) / ((d : ℝ) - 1) := by
      apply (lt_div_iff₀ hd1).2
      linarith
    exact hone.trans hp
  have hp0 : 0 < p := by linarith
  have heps : 0 < ((d : ℝ) - 1) * p - d := by
    have hmul : (d : ℝ) < p * ((d : ℝ) - 1) :=
      (div_lt_iff₀ hd1).mp hp
    nlinarith
  obtain ⟨D1, hD1, hweak1⟩ := hT_weak_one
  obtain ⟨D2, hD2, hweak2⟩ := hT_weak_two
  let V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal
  let c1 : ℝ := D1 * V * (4 : ℝ) ^ d
  let c2 : ℝ := D2
  let a1 : ℝ := (p - 1)⁻¹ + (3 - p)⁻¹
  let a2 : ℝ := ((1 : ℝ) / 4) * p⁻¹ + (2 - p)⁻¹
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hc1 : 0 ≤ c1 := by
    dsimp only [c1]
    positivity
  have hc2 : 0 ≤ c2 := hD2.le
  have hc2pos : 0 < c2 := hD2
  have ha1 : 0 ≤ a1 := by
    dsimp only [a1]
    exact add_nonneg (inv_nonneg.mpr (by linarith))
      (inv_nonneg.mpr (by linarith))
  have ha2 : 0 ≤ a2 := by
    dsimp only [a2]
    exact add_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hp0.le))
      (inv_nonneg.mpr (by linarith))
  have ha2pos : 0 < a2 := by
    dsimp only [a2]
    exact lt_of_lt_of_le (mul_pos (by norm_num) (inv_pos.mpr hp0))
      (le_add_of_nonneg_right (inv_nonneg.mpr (by linarith)))
  have hA1 :
      (ENNReal.ofReal (p - 1))⁻¹ + (ENNReal.ofReal (3 - p))⁻¹ =
        ENNReal.ofReal a1 := by
    dsimp only [a1]
    rw [← ENNReal.ofReal_inv_of_pos (by linarith : 0 < p - 1)]
    rw [← ENNReal.ofReal_inv_of_pos (by linarith : 0 < 3 - p)]
    rw [← ENNReal.ofReal_add (inv_nonneg.mpr (by linarith))
      (inv_nonneg.mpr (by linarith))]
  have hA2 :
      ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹ +
          (ENNReal.ofReal (2 - p))⁻¹ = ENNReal.ofReal a2 := by
    change ENNReal.ofReal ((1 : ℝ) / 4) * (ENNReal.ofReal p)⁻¹ +
        (ENNReal.ofReal (2 - p))⁻¹ =
      ENNReal.ofReal (((1 : ℝ) / 4) * p⁻¹ + (2 - p)⁻¹)
    rw [← ENNReal.ofReal_inv_of_pos hp0]
    rw [← ENNReal.ofReal_inv_of_pos (by linarith : 0 < 2 - p)]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) (inv_nonneg.mpr hp0.le))
      (inv_nonneg.mpr (by linarith))]
  have hweak1norm :
      ∀ j (g : SchwartzMap (Euclidean d) ℂ) {s : ℝ}, 0 < s →
        ENNReal.ofReal s * volume {x | s < T j g x} ≤
          ENNReal.ofReal (c1 * (2 : ℝ) ^ (j : ℝ)) *
            ∫⁻ x, ENNReal.ofReal ‖g x‖ :=
    relative_dyadic_normalize_weak_one T hD1 hV (by rfl)
      (by
        intro j g a ha hga s hs
        simpa only [V] using hweak1 j g ha hga hs)
  have hweak2norm :
      ∀ j (g : SchwartzMap (Euclidean d) ℂ) {s : ℝ}, 0 < s →
        ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j g x} ≤
          ENNReal.ofReal (c2 * (2 : ℝ) ^ (-((d : ℝ) - 2) * (j : ℝ))) *
            ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) := by
    intro j g s hs
    have hexp : -(((d : ℝ) - 2) * (j : ℝ)) =
        -((d : ℝ) - 2) * (j : ℝ) := by ring
    simpa only [c2, hexp] using hweak2 j g hs
  let A : ℝ := p * (4 * c2 * a2 + 2 * c1 * a1)
  let ε : ℝ := ((d : ℝ) - 1) * p - d
  refine ⟨A, ε, ?_, heps, ?_⟩
  · dsimp only [A]
    have hfirst : 0 < 4 * c2 * a2 :=
      mul_pos (mul_pos (by norm_num) hc2pos) ha2pos
    have hbracket : 0 < 4 * c2 * a2 + 2 * c1 * a1 :=
      hfirst.trans_le (le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (by norm_num) hc1) ha1))
    exact mul_pos hp0 hbracket
  intro j f
  simpa only [A, ε] using
    relative_dyadic_one_two_fixed T hTmeas hTnonneg hT_subadd
      hd2 hp1 hp_lt hp0 hc1 hc2 hc2pos ha1 ha2 ha2pos
      hweak1norm hweak2norm hA1 hA2 j f


/-- The square endpoint is already a decaying strong-type estimate. -/
private theorem relative_dyadic_strong_type_at_two
    {d : ℕ} (hd : 3 ≤ d)
    (T : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ)
    (hstrong : ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      MemLp (T j f) 2 volume ∧
      (∫ x : Euclidean d, (T j f x) ^ (2 : ℕ)) ≤
        D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
          ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ)) :
    ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧
      ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
        MemLp (T j f) (ENNReal.ofReal (2 : ℝ)) volume ∧
        (∫ x : Euclidean d, (T j f x) ^ (2 : ℝ)) ≤
          A * (2 : ℝ) ^ (-ε * j) * ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℝ) := by
  obtain ⟨D, hD, hbound⟩ := hstrong
  refine ⟨D, (d : ℝ) - 2, hD, ?_, ?_⟩
  · have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  · intro j f
    rcases hbound j f with ⟨hmem, hbound⟩
    constructor
    · norm_num
      exact hmem
    · have hexp : -((d : ℝ) - 2) * (j : ℝ) =
          -(((d : ℝ) - 2) * (j : ℝ)) := by ring
      simpa only [Real.rpow_two, hexp] using hbound

/-- A fixed Schwartz multiplier supplies the scale-uniform top endpoint. -/
private theorem relative_dyadic_bandpass_top_bound
    {d : ℕ} (φ ψ : SchwartzMap (Euclidean d) ℂ)
    (hψ : ∀ η, ψ η =
      φ (((2 : ℝ) ^ (0 + 1))⁻¹ • η) - φ (((2 : ℝ) ^ 0)⁻¹ • η)) :
    ∃ Ctop : ℝ, 0 < Ctop ∧ ∀ j (f : SchwartzMap (Euclidean d) ℂ)
      (a : ℝ), 0 ≤ a → (∀ x, ‖f x‖ ≤ a) → ∀ x,
        relativeBandpassMaximal d φ j f x ≤ Ctop * a := by
  let B : ℝ :=
    (∫ y : Euclidean d, ‖(𝓕⁻ ψ : SchwartzMap (Euclidean d) ℂ) y‖) *
      surfaceMass d
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (integral_nonneg fun y => norm_nonneg _) ENNReal.toReal_nonneg
  refine ⟨B + 1, by linarith, ?_⟩
  intro j f a ha hfa x
  rw [relative_dyadic_bandpass_eq_scaled φ ψ hψ j f x]
  calc
    (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (-r.1 • ξ) *
        ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
        𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal ≤
        (a * ∫ y : Euclidean d,
          ‖(𝓕⁻ ψ : SchwartzMap (Euclidean d) ℂ) y‖) *
            surfaceMass d :=
      iSup_norm_fourierInv_relative_surface_scaled_schwartz_multiplier_le
        ψ f j hfa x
    _ = B * a := by
      dsimp only [B]
      ring
    _ ≤ (B + 1) * a := by nlinarith

/-- Interpolating the weak square endpoint with the top endpoint gives a
lower-integral estimate at every dyadic frequency. -/
private theorem relative_dyadic_two_top_lintegral_bound
    {d : ℕ} {p : ℝ} (hp_gt : 2 < p)
    (T : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ)
    (hTmeas : ∀ j f, AEStronglyMeasurable (T j f) volume)
    (hTnonneg : ∀ j f x, 0 ≤ T j f x)
    (hT_subadd : ∀ j f g x, T j (f + g) x ≤ T j f x + T j g x)
    (D Ctop : ℝ) (hD : 0 < D) (hCtop : 0 < Ctop)
    (hweak : ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
      {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j f x} ≤
        ENNReal.ofReal
          (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) *
          ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)))
    (htop : ∀ j (f : SchwartzMap (Euclidean d) ℂ)
      (a : ℝ), 0 ≤ a → (∀ x, ‖f x‖ ≤ a) → ∀ x,
        T j f x ≤ Ctop * a) :
    ∃ A : ℝ, 0 < A ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
        ENNReal.ofReal
          (A * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
            ∫ x : Euclidean d, ‖f x‖ ^ p) := by
  have hp0 : 0 < p := by linarith
  let Atail : ℝ := (p - 2)⁻¹ * (4 : ℝ) ^ (p - 2)
  let A : ℝ := p * (2 : ℝ) ^ (2 : ℝ) * D * Atail * Ctop ^ (p - 2)
  refine ⟨A, ?_, ?_⟩
  · dsimp only [A, Atail]
    positivity
  intro j f
  obtain ⟨low, high, hlow, hhigh, hsplit⟩ :=
    exists_schwartz_smooth_low_high_family f
  let J : ℝ := ∫ x : Euclidean d, ‖f x‖ ^ p
  have hinput : (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖f x‖) ^ p) =
      ENNReal.ofReal J := by
    dsimp only [J]
    exact schwartz_lintegral_rpow_eq_ofReal_integral f hp0
  let Aq : ℝ := Atail * J
  have hAq : 0 ≤ Aq := by
    dsimp only [Aq]
    exact mul_nonneg (by dsimp only [Atail]; positivity)
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p)
  have htail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x : Euclidean d, (ENNReal.ofReal ‖high t x‖) ^ (2 : ℝ)) *
          (ENNReal.ofReal t) ^ (p - 2 - 1)) ≤ ENNReal.ofReal Aq := by
    have h := smooth_bump_schwartz_high_q_weighted_tail f low high hlow hhigh
      (q := (2 : ℝ)) (p := p) (by norm_num) hp_gt
    rw [hinput] at h
    have htail_eq :
        (ENNReal.ofReal (p - 2))⁻¹ * (ENNReal.ofReal (4 : ℝ)) ^ (p - 2) *
            ENNReal.ofReal J = ENNReal.ofReal Aq := by
      dsimp only [Aq, Atail]
      rw [← ENNReal.ofReal_inv_of_pos (by linarith : 0 < p - 2)]
      rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 4)]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (p - 2)⁻¹)]
      rw [← ENNReal.ofReal_mul
        (by positivity : 0 ≤ (p - 2)⁻¹ * (4 : ℝ) ^ (p - 2))]
    rw [htail_eq] at h
    exact h
  have hlin :
      (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
        ENNReal.ofReal
          (p * (2 : ℝ) ^ (2 : ℝ) *
            (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) * Aq * Ctop ^ (p - 2)) := by
    apply marcinkiewicz_weak_q_top_on_additive_split_real_top_scaled
      (D := Set.univ) (eval := fun g : SchwartzMap (Euclidean d) ℂ =>
        (g : Euclidean d → ℂ)) (T := T j) (q := (2 : ℝ))
        (Cq := D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) (Ctop := Ctop)
        (p := p) (f := f) (low := low) (high := high) (Aq := Aq)
    · intro g x
      exact hTnonneg j g x
    · intro g h _ _ x
      exact hT_subadd j g h x
    · norm_num
    · exact hCtop
    · intro g _ s hs
      have hw := hweak j g hs
      simpa [ENNReal.ofReal_rpow_of_pos hs,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
          (by norm_num : (0 : ℝ) ≤ 2)] using hw
    · intro g _ a ha hga x
      exact htop j g a ha hga x
    · exact hp_gt
    · exact (hTmeas j f).aemeasurable
    · intro t
      simp
    · intro t
      simp
    · intro t
      ext x
      exact hsplit t x
    · intro t ht x
      exact smooth_low_norm_le_half_height f (low t) ht (hlow t) x
    · exact measurable_smooth_high_profile_lintegrals f low high hlow hhigh 2
    · exact htail
    · exact hAq
  have hcoeff :
      p * (2 : ℝ) ^ (2 : ℝ) *
          (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) * Aq * Ctop ^ (p - 2) =
        A * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) * J := by
    dsimp only [A, Aq, Atail]
    ring
  rw [← hcoeff]
  exact hlin

/-- Convert the dyadic lower-integral estimate into the real strong-type
estimate used by frequency reassembly. -/
private theorem relative_dyadic_two_top_real_bound
    {d : ℕ} {p : ℝ} (hp0 : 0 < p)
    (T : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ)
    (hTmeas : ∀ j f, AEStronglyMeasurable (T j f) volume)
    (hTnonneg : ∀ j f x, 0 ≤ T j f x)
    (A : ℝ) (hA : 0 < A)
    (hlower : ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      (∫⁻ x : Euclidean d, ENNReal.ofReal ((T j f x) ^ p)) ≤
        ENNReal.ofReal
          (A * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
            ∫ x : Euclidean d, ‖f x‖ ^ p)) :
    ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      MemLp (T j f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (T j f x) ^ p) ≤
        A * (2 : ℝ) ^ (-((d : ℝ) - 2) * j) * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  intro j f
  have hright_nonneg :
      0 ≤ A * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
        ∫ x : Euclidean d, ‖f x‖ ^ p := by
    exact mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (by norm_num) _))
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p)
  rcases memLp_and_integral_of_lintegral_rpow_bound (T j f)
      (hTmeas j f) (hTnonneg j f) hp0 (hlower j f) hright_nonneg with
    ⟨hMem, hbound⟩
  refine ⟨hMem, ?_⟩
  calc
    (∫ x : Euclidean d, (T j f x) ^ p) ≤
        A * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
          ∫ x : Euclidean d, ‖f x‖ ^ p := hbound
    _ = A * (2 : ℝ) ^ (-((d : ℝ) - 2) * j) *
          ∫ x : Euclidean d, ‖f x‖ ^ p := by
            congr 2
            ring_nf

/-- Interpolation of the weak square endpoint with a uniform top endpoint. -/
private theorem relative_dyadic_strong_type_two_top
    {d : ℕ} (hd : 3 ≤ d) {p : ℝ} (hp_gt : 2 < p)
    (T : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ)
    (hTmeas : ∀ j f, AEStronglyMeasurable (T j f) volume)
    (hTnonneg : ∀ j f x, 0 ≤ T j f x)
    (hT_subadd : ∀ j f g x, T j (f + g) x ≤ T j f x + T j g x)
    (hT_weak_two :
      ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
        {s : ℝ}, 0 < s →
        ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j f x} ≤
          ENNReal.ofReal
            (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) *
            ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)))
    (hT_top :
      ∃ Ctop : ℝ, 0 < Ctop ∧ ∀ j (f : SchwartzMap (Euclidean d) ℂ)
        (a : ℝ), 0 ≤ a → (∀ x, ‖f x‖ ≤ a) → ∀ x,
          T j f x ≤ Ctop * a) :
    ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧
      ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
        MemLp (T j f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (T j f x) ^ p) ≤
          A * (2 : ℝ) ^ (-ε * j) * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  rcases hT_weak_two with ⟨D, hD, hweak⟩
  rcases hT_top with ⟨Ctop, hCtop, htop⟩
  obtain ⟨A, hA, hlower⟩ :=
    relative_dyadic_two_top_lintegral_bound (d := d) (p := p) hp_gt
      T hTmeas hTnonneg hT_subadd D Ctop hD hCtop hweak htop
  refine ⟨A, (d : ℝ) - 2, hA, ?_, ?_⟩
  · have hdreal : (2 : ℝ) < d := by
      exact_mod_cast (show 2 < d by omega)
    linarith
  exact relative_dyadic_two_top_real_bound (d := d) (p := p) (by linarith)
    T hTmeas hTnonneg A hA hlower

private theorem relative_lowpass_fixed_radius_bound
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ)
    (f : SchwartzMap (Euclidean d) ℂ) {a : ℝ} (ha : 0 < a)
    (r : Ioi (0 : ℝ)) (x : Euclidean d) :
    ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) * φ (a • (r.1 • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
      (‖f.toBoundedContinuousFunction‖ *
        ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖) *
        surfaceMass d := by
  let R₀ : ℝ := (a * r.1)⁻¹
  have hR₀ : 0 < R₀ := inv_pos.mpr (mul_pos ha r.2)
  let A₀ : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 R₀⁻¹ (inv_ne_zero hR₀.ne'))
  let ψ : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A₀ φ
  let h : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (ψ : Euclidean d → ℂ) (𝓕 f)
  have hψ (ξ : Euclidean d) : ψ ξ = φ (a • (r.1 • ξ)) := by
    change φ (A₀ ξ) = φ (a • (r.1 • ξ))
    change φ (R₀⁻¹ • ξ) = φ (a • (r.1 • ξ))
    dsimp only [R₀]
    rw [inv_inv]
    simp [smul_smul]
  have hh (ξ : Euclidean d) : h ξ =
      φ (a • (r.1 • ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ := by
    simp only [h, SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth,
      SchwartzMap.fourier_coe, smul_eq_mul]
    rw [hψ]
  have hbridge := sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier h r.1
  have hbound : ∀ y : Euclidean d,
      ‖(𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) y‖ ≤
        ‖f.toBoundedContinuousFunction‖ *
          ∫ z : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) z‖ := by
    intro y
    rw [SchwartzMap.fourierInv_coe]
    rw [show (h : Euclidean d → ℂ) =
        fun ξ : Euclidean d => φ (R₀⁻¹ • ξ) *
          𝓕 (f : Euclidean d → ℂ) ξ by
      funext ξ
      rw [hh]
      exact (congrArg (fun z : ℂ => z * 𝓕 (f : Euclidean d → ℂ) ξ)
        (hψ ξ)).symm]
    exact norm_fourierInv_scaled_schwartz_multiplier_le φ f hR₀
      (fun z => by
        change ‖f.toBoundedContinuousFunction z‖ ≤ ‖f.toBoundedContinuousFunction‖
        exact BoundedContinuousFunction.norm_coe_le_norm _ _) y
  calc
    ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) * φ (a • (r.1 • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ =
        ‖𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) * h ξ) x‖ := by
          apply congrArg (fun q : Euclidean d → ℂ => ‖𝓕⁻ q x‖)
          funext ξ
          rw [hh]
          ring
    _ = ‖sphericalAverage d ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) :
        Euclidean d → ℂ) r.1 x‖ := by
          exact congrArg norm (congrFun hbridge x).symm
    _ ≤ _ := norm_sphericalAverage_le_surfaceMass_mul d
      ((𝓕⁻ h : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r.1 x hbound

private theorem relative_bandpass_fixed_radius_bound
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ)
    (hφcompact : HasCompactSupport (φ : Euclidean d → ℂ))
    (f : SchwartzMap (Euclidean d) ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (r : Ioi (0 : ℝ)) (x : Euclidean d) :
    ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) *
          (φ (a • (r.1 • ξ)) - φ (b • (r.1 • ξ))) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
      2 * ((‖f.toBoundedContinuousFunction‖ *
        ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖) *
        surfaceMass d) := by
  let Rₐ : ℝ := (a * r.1)⁻¹
  let Rᵦ : ℝ := (b * r.1)⁻¹
  have hRₐ : 0 < Rₐ := inv_pos.mpr (mul_pos ha r.2)
  have hRᵦ : 0 < Rᵦ := inv_pos.mpr (mul_pos hb r.2)
  let Aₐ : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 Rₐ⁻¹ (inv_ne_zero hRₐ.ne'))
  let Aᵦ : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 Rᵦ⁻¹ (inv_ne_zero hRᵦ.ne'))
  let ψₐ : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Aₐ φ
  let ψᵦ : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Aᵦ φ
  have hψₐ (ξ : Euclidean d) : ψₐ ξ = φ (a • (r.1 • ξ)) := by
    change φ (Aₐ ξ) = φ (a • (r.1 • ξ))
    change φ (Rₐ⁻¹ • ξ) = φ (a • (r.1 • ξ))
    dsimp only [Rₐ]
    rw [inv_inv]
    simp [smul_smul]
  have hψᵦ (ξ : Euclidean d) : ψᵦ ξ = φ (b • (r.1 • ξ)) := by
    change φ (Aᵦ ξ) = φ (b • (r.1 • ξ))
    change φ (Rᵦ⁻¹ • ξ) = φ (b • (r.1 • ξ))
    dsimp only [Rᵦ]
    rw [inv_inv]
    simp [smul_smul]
  have hψₐcompact : HasCompactSupport (ψₐ : Euclidean d → ℂ) := by
    change HasCompactSupport ((φ : Euclidean d → ℂ) ∘
      (Aₐ.toHomeomorph : Euclidean d → Euclidean d))
    exact hφcompact.comp_homeomorph Aₐ.toHomeomorph
  have hψᵦcompact : HasCompactSupport (ψᵦ : Euclidean d → ℂ) := by
    change HasCompactSupport ((φ : Euclidean d → ℂ) ∘
      (Aᵦ.toHomeomorph : Euclidean d → Euclidean d))
    exact hφcompact.comp_homeomorph Aᵦ.toHomeomorph
  obtain ⟨mₐ, hmₐ⟩ :=
    exists_schwartz_compactSupport_mul_surfaceFourier ψₐ hψₐcompact r.1
  obtain ⟨mᵦ, hmᵦ⟩ :=
    exists_schwartz_compactSupport_mul_surfaceFourier ψᵦ hψᵦcompact r.1
  have hsub :
      𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) *
          (φ (a • (r.1 • ξ)) - φ (b • (r.1 • ξ))) *
          𝓕 (f : Euclidean d → ℂ) ξ) x =
        𝓕⁻ (fun ξ : Euclidean d => (mₐ ξ - mᵦ ξ) *
          𝓕 (f : Euclidean d → ℂ) ξ) x := by
    apply congrArg (fun q : Euclidean d → ℂ => 𝓕⁻ q x)
    funext ξ
    rw [hmₐ, hmᵦ, hψₐ, hψᵦ]
    ring
  have hmₐ' :
      𝓕⁻ (fun ξ : Euclidean d => mₐ ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x =
        𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) *
          φ (a • (r.1 • ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x := by
    apply congrArg (fun q : Euclidean d → ℂ => 𝓕⁻ q x)
    funext ξ
    rw [hmₐ, hψₐ]
    ring
  have hmᵦ' :
      𝓕⁻ (fun ξ : Euclidean d => mᵦ ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x =
        𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) *
          φ (b • (r.1 • ξ)) * 𝓕 (f : Euclidean d → ℂ) ξ) x := by
    apply congrArg (fun q : Euclidean d → ℂ => 𝓕⁻ q x)
    funext ξ
    rw [hmᵦ, hψᵦ]
    ring
  calc
    ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) *
          (φ (a • (r.1 • ξ)) - φ (b • (r.1 • ξ))) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ =
        ‖𝓕⁻ (fun ξ : Euclidean d => (mₐ ξ - mᵦ ξ) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ := congrArg norm hsub
    _ = ‖𝓕⁻ (fun ξ : Euclidean d => mₐ ξ *
        𝓕 (f : Euclidean d → ℂ) ξ) x -
          𝓕⁻ (fun ξ : Euclidean d => mᵦ ξ *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ := by
      rw [fourierInv_sub_schwartz_multiplier mₐ mᵦ f x]
    _ ≤ ‖𝓕⁻ (fun ξ : Euclidean d => mₐ ξ *
        𝓕 (f : Euclidean d → ℂ) ξ) x‖ +
          ‖𝓕⁻ (fun ξ : Euclidean d => mᵦ ξ *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ := norm_sub_le _ _
    _ ≤ ((‖f.toBoundedContinuousFunction‖ *
        ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖) *
          surfaceMass d) +
        ((‖f.toBoundedContinuousFunction‖ *
          ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖) *
          surfaceMass d) := by
      rw [hmₐ', hmᵦ']
      exact add_le_add
        (relative_lowpass_fixed_radius_bound φ f ha r x)
        (relative_lowpass_fixed_radius_bound φ f hb r x)
    _ = _ := by ring

private theorem relative_cutoff_maximal_aestronglyMeasurable
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ)
    (hφcompact : HasCompactSupport (φ : Euclidean d → ℂ))
    (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
    AEStronglyMeasurable (relativeCutoffMaximal d φ N f) volume := by
  let A₀ : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 ((2 : ℝ) ^ N)⁻¹ (inv_ne_zero (pow_ne_zero N (by norm_num))))
  let ψ : SchwartzMap (Euclidean d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A₀ φ
  have hψ (ξ : Euclidean d) : ψ ξ = φ (((2 : ℝ) ^ N)⁻¹ • ξ) := by
    change φ (A₀ ξ) = _
    simp [A₀]
  have hψcompact : HasCompactSupport (ψ : Euclidean d → ℂ) := by
    change HasCompactSupport ((φ : Euclidean d → ℂ) ∘
      (A₀.toHomeomorph : Euclidean d → Euclidean d))
    exact hφcompact.comp_homeomorph A₀.toHomeomorph
  obtain ⟨χ, hχ⟩ :=
    exists_schwartz_compactSupport_mul_surfaceFourier ψ hψcompact 1
  have hχ' (ξ : Euclidean d) :
      χ ξ = ψ ξ * surfaceFourier d (-ξ) := by
    simpa using hχ ξ
  have hrewrite : relativeCutoffMaximal d φ N f = fun x : Euclidean d =>
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
        χ (r.1 • ξ) * 𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal := by
    funext x
    dsimp only [relativeCutoffMaximal]
    congr 1
    apply iSup_congr
    intro r
    congr 2
    apply congrArg (fun g : Euclidean d → ℂ => 𝓕⁻ g x)
    funext ξ
    rw [hχ', hψ]
    simp only [neg_smul]
    ring
  rw [hrewrite]
  apply (ENNReal.measurable_toReal.comp ?_).aestronglyMeasurable
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_iSup
  intro r
  have hrinv : 0 < r.1⁻¹ := inv_pos.mpr r.2
  have hcont : Continuous (fun x : Euclidean d =>
      𝓕⁻ (fun ξ : Euclidean d => χ (r.1 • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x) := by
    simpa [inv_inv] using
      (continuous_fourierInv_scaled_schwartz_multiplier χ f hrinv)
  exact (ENNReal.continuous_ofReal.comp hcont.norm).lowerSemicontinuous

/-- Turn an extended-real Lp norm estimate into the corresponding moment bound. -/
private theorem relative_cutoff_moment_bound_of_eLpNorm
    {d : ℕ} {p : ℝ} (hp1 : 1 < p)
    (g : Euclidean d → ℝ) (hgmem : MemLp g (ENNReal.ofReal p) volume)
    (hg0 : ∀ x, 0 ≤ g x) (I : ℝ) (hI : 0 ≤ I)
    (D : ENNReal) (hDtop : D ≠ ⊤)
    (hnorm : eLpNorm g (ENNReal.ofReal p) volume ≤
      D * ENNReal.ofReal (I ^ p⁻¹))
    (C : ℝ) (hcoefficient : D.toReal ^ p ≤ C) :
    (∫ x : Euclidean d, g x ^ p) ≤ C * I := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hpNN : 0 ≤ p := hp0.le
  have hpE0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpET : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hint0 : 0 ≤ ∫ x : Euclidean d, g x ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (hg0 x) p
  have hrootbound : (∫ x : Euclidean d, g x ^ p) ^ p⁻¹ ≤
      D.toReal * (I ^ p⁻¹) := by
    have hnormEq : eLpNorm g (ENNReal.ofReal p) volume =
        ENNReal.ofReal ((∫ x : Euclidean d, g x ^ p) ^ p⁻¹) := by
      rw [hgmem.eLpNorm_eq_integral_rpow_norm hpE0 hpET,
        ENNReal.toReal_ofReal hpNN]
      apply congrArg ENNReal.ofReal
      apply congrArg (fun z : ℝ => z ^ p⁻¹)
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    have hnorm' :
        ENNReal.ofReal ((∫ x : Euclidean d, g x ^ p) ^ p⁻¹) ≤
          D * ENNReal.ofReal (I ^ p⁻¹) := by
      rw [← hnormEq]
      exact hnorm
    calc
      (∫ x : Euclidean d, g x ^ p) ^ p⁻¹ =
          (ENNReal.ofReal ((∫ x : Euclidean d, g x ^ p) ^ p⁻¹)).toReal := by
            rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hint0 _)]
      _ ≤ (D * ENNReal.ofReal (I ^ p⁻¹)).toReal :=
        (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top hDtop ENNReal.ofReal_ne_top)).mpr hnorm'
      _ = D.toReal * (I ^ p⁻¹) := by
        simp only [ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)]
  have hraised := Real.rpow_le_rpow
    (Real.rpow_nonneg hint0 _) hrootbound hpNN
  calc
    (∫ x : Euclidean d, g x ^ p) =
        ((∫ x : Euclidean d, g x ^ p) ^ p⁻¹) ^ p := by
          rw [Real.rpow_inv_rpow hint0 (ne_of_gt hp0)]
    _ ≤ (D.toReal * (I ^ p⁻¹)) ^ p := hraised
    _ = D.toReal ^ p * I := by
      rw [Real.mul_rpow ENNReal.toReal_nonneg (Real.rpow_nonneg hI _)]
      rw [Real.rpow_inv_rpow hI (ne_of_gt hp0)]
    _ ≤ C * I := mul_le_mul_of_nonneg_right hcoefficient hI

/-- Strong type with exponentially decaying constants for relative bands. -/
theorem relative_dyadic_strong_type
    {d : ℕ} (hd : 3 ≤ d) {p : ℝ}
    (hp : (d : ℝ) / ((d : ℝ) - 1) < p)
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (hφnorm : ∀ ξ, ‖φ ξ‖ ≤ 1) :
    ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧
      ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
        MemLp (relativeBandpassMaximal d φ j f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (relativeBandpassMaximal d φ j f x) ^ p) ≤
          A * (2 : ℝ) ^ (-ε * j) * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  let T : ℕ → SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
    fun j f => relativeBandpassMaximal d φ j f
  have hT_eq (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
      T j f = relativeBandpassMaximal d φ j f := by
    rfl
  have hTmeas : ∀ j f, AEStronglyMeasurable (T j f) volume := by
    intro j f
    simpa only [hT_eq] using
      relative_dyadic_bandpass_measurable φ hφone hφzero j f
  have hTnonneg : ∀ j f x, 0 ≤ T j f x := by
    intro j f x
    simpa only [hT_eq] using relative_dyadic_bandpass_nonneg φ j f x
  have hdyadic :
      ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧
        ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
          MemLp (T j f) (ENNReal.ofReal p) volume ∧
          (∫ x : Euclidean d, (T j f x) ^ p) ≤
            A * (2 : ℝ) ^ (-ε * j) * ∫ x : Euclidean d, ‖f x‖ ^ p := by
    obtain ⟨ψ, hψ⟩ := exists_schwartzMap_smooth_dyadic_bandpass φ 0
    have hrewrite (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
        T j f x =
          (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) *
              ψ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ)) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖).toReal := by
      rw [hT_eq]
      exact relative_dyadic_bandpass_eq_scaled φ ψ hψ j f x
    have hT_subadd (j : ℕ) (f g : SchwartzMap (Euclidean d) ℂ)
        (x : Euclidean d) : T j (f + g) x ≤ T j f x + T j g x := by
      rw [hrewrite j (f + g) x, hrewrite j f x, hrewrite j g x]
      exact
        toReal_iSup_ennreal_norm_fourierInv_relative_surface_scaled_schwartz_multiplier_add_le
          ψ f g j x
    obtain ⟨D1, hD1, hweak1⟩ :=
      relative_dyadic_bandpass_weak_one hd φ
    have hT_weak_one :
        ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
          {a : ℝ}, 0 ≤ a → (∀ x, ‖f x‖ ≤ a) → ∀ {s : ℝ}, 0 < s →
          ENNReal.ofReal s * volume {x | s < T j f x} ≤
            (ENNReal.ofReal
              (D * (2 : ℝ) ^ j *
                (volume (Metric.ball (0 : Euclidean d) 1)).toReal) *
              (ENNReal.ofReal (4 : ℝ)) ^ d) *
              ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
      refine ⟨D1, hD1, ?_⟩
      intro j f a ha hfa s hs
      simpa only [hT_eq] using hweak1 j f ha hfa hs
    obtain ⟨D2, hD2, hstrong2⟩ :=
      relative_dyadic_bandpass_strong_two hd φ hφone hφzero hφnorm
    have hT_strong_two :
        ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
          MemLp (T j f) 2 volume ∧
          (∫ x : Euclidean d, (T j f x) ^ (2 : ℕ)) ≤
            D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j)) *
              ∫ x : Euclidean d, ‖f x‖ ^ (2 : ℕ) := by
      refine ⟨D2, hD2, ?_⟩
      intro j f
      simpa only [hT_eq] using hstrong2 j f
    obtain ⟨D3, hD3, hweak2⟩ :=
      relative_dyadic_bandpass_weak_two hd φ hφone hφzero hφnorm
    have hT_weak_two :
        ∃ D : ℝ, 0 < D ∧ ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
          {s : ℝ}, 0 < s →
          ENNReal.ofReal (s ^ (2 : ℕ)) * volume {x | s < T j f x} ≤
            ENNReal.ofReal
              (D * (2 : ℝ) ^ (-(((d : ℝ) - 2) * j))) *
              ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) := by
      refine ⟨D3, hD3, ?_⟩
      intro j f s hs
      simpa only [hT_eq] using hweak2 j f hs
    rcases lt_trichotomy p 2 with hp_lt | hp_eq | hp_gt
    · exact relative_dyadic_strong_type_one_two hd hp hp_lt T hTmeas hTnonneg
        hT_subadd hT_weak_one hT_weak_two
    · subst p
      exact relative_dyadic_strong_type_at_two hd T hT_strong_two
    · obtain ⟨Ctop, hCtop, htop⟩ :=
        relative_dyadic_bandpass_top_bound φ ψ hψ
      have hT_top :
          ∃ Ctop : ℝ, 0 < Ctop ∧ ∀ j (f : SchwartzMap (Euclidean d) ℂ)
            (a : ℝ), 0 ≤ a → (∀ x, ‖f x‖ ≤ a) → ∀ x,
              T j f x ≤ Ctop * a := by
        refine ⟨Ctop, hCtop, ?_⟩
        intro j f a ha hfa x
        simpa only [hT_eq] using htop j f a ha hfa x
      exact relative_dyadic_strong_type_two_top hd hp_gt T hTmeas hTnonneg
        hT_subadd hT_weak_two hT_top
  simpa only [← hT_eq] using hdyadic
private def relative_radius_profile
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ) (r : Ioi (0 : ℝ)) :
    SchwartzMap (Euclidean d) ℂ :=
  let A : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 r.1 r.2.ne')
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A φ

private theorem relative_radius_profile_apply
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ) (r : Ioi (0 : ℝ))
    (ξ : Euclidean d) :
    relative_radius_profile φ r ξ = φ (r.1 • ξ) := by
  change φ ((ContinuousLinearEquiv.smulLeft (Units.mk0 r.1 r.2.ne')) ξ) =
    φ (r.1 • ξ)
  simp

private def relative_dyadic_profile
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ) (r : Ioi (0 : ℝ))
    (n : ℕ) : SchwartzMap (Euclidean d) ℂ :=
  let A : Euclidean d ≃L[ℝ] Euclidean d :=
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 ((2 : ℝ) ^ n)⁻¹ (inv_ne_zero (pow_ne_zero n (by norm_num))))
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (relative_radius_profile φ r)

private theorem relative_dyadic_profile_apply
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ) (r : Ioi (0 : ℝ))
    (n : ℕ) (ξ : Euclidean d) :
    relative_dyadic_profile φ r n ξ =
      φ (((2 : ℝ) ^ n)⁻¹ • (r.1 • ξ)) := by
  change relative_radius_profile φ r (((2 : ℝ) ^ n)⁻¹ • ξ) = _
  rw [relative_radius_profile_apply]
  rw [smul_smul, smul_smul]
  congr 2
  ring

private def relative_radius_data
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ) (r : Ioi (0 : ℝ))
    (n : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
    SchwartzMap (Euclidean d) ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (relative_dyadic_profile φ r n : Euclidean d → ℂ) (𝓕 f)

private theorem relative_radius_data_apply
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ) (r : Ioi (0 : ℝ))
    (n : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (ξ : Euclidean d) :
    relative_radius_data φ r n f ξ =
      φ (((2 : ℝ) ^ n)⁻¹ • (r.1 • ξ)) *
        𝓕 (f : Euclidean d → ℂ) ξ := by
  simp only [relative_radius_data,
    SchwartzMap.smulLeftCLM_apply (relative_dyadic_profile φ r n).hasTemperateGrowth,
    SchwartzMap.fourier_coe, smul_eq_mul]
  rw [relative_dyadic_profile_apply]

private theorem relative_radius_data_telescopes
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ) (r : Ioi (0 : ℝ))
    (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
    relative_radius_data φ r N f = relative_radius_data φ r 0 f +
      ∑ j ∈ Finset.range N,
        (relative_radius_data φ r (j + 1) f - relative_radius_data φ r j f) := by
  have hsum_apply (ξ : Euclidean d) :
      (∑ j ∈ Finset.range N,
        (relative_radius_data φ r (j + 1) f - relative_radius_data φ r j f)) ξ =
        ∑ j ∈ Finset.range N,
          (relative_radius_data φ r (j + 1) f - relative_radius_data φ r j f) ξ := by
    change (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
      (Euclidean d) ℂ)
        (∑ j ∈ Finset.range N,
          (relative_radius_data φ r (j + 1) f - relative_radius_data φ r j f)) ξ =
        ∑ j ∈ Finset.range N,
          (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
            (Euclidean d) ℂ)
            (relative_radius_data φ r (j + 1) f - relative_radius_data φ r j f) ξ
    simpa only [Finset.sum_apply] using
      congrFun (map_sum (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
        (Euclidean d) ℂ)
        (fun j => relative_radius_data φ r (j + 1) f - relative_radius_data φ r j f)
        (Finset.range N)) ξ
  ext ξ
  rw [add_apply, hsum_apply, relative_radius_data_apply, relative_radius_data_apply]
  rw [show (∑ j ∈ Finset.range N,
      (relative_radius_data φ r (j + 1) f - relative_radius_data φ r j f) ξ) =
        ∑ j ∈ Finset.range N,
          (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
            φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sub_apply, relative_radius_data_apply, relative_radius_data_apply]
      ring]
  rw [← Finset.sum_mul]
  simp only [pow_zero, inv_one, one_smul]
  rw [smooth_dyadic_bandpass_sum]
  ring

private theorem sphericalAverage_schwartz_add_finset_sum
    {d : ℕ} (g : SchwartzMap (Euclidean d) ℂ)
    (gs : ℕ → SchwartzMap (Euclidean d) ℂ) (s : Finset ℕ)
    (r : ℝ) (x : Euclidean d) :
    sphericalAverage d
        ((g + ∑ j ∈ s, gs j : SchwartzMap (Euclidean d) ℂ) :
          Euclidean d → ℂ) r x =
      sphericalAverage d (g : Euclidean d → ℂ) r x +
        ∑ j ∈ s, sphericalAverage d (gs j : Euclidean d → ℂ) r x := by
  have hg : Integrable (fun ω : Metric.sphere (0 : Euclidean d) 1 =>
      g (x + r • (ω : Euclidean d))) (unitSurfaceMeasure d) :=
    (g.continuous.comp
      ((continuous_const : Continuous fun _ : Metric.sphere (0 : Euclidean d) 1 => x).add
        ((continuous_const : Continuous fun _ : Metric.sphere (0 : Euclidean d) 1 => r).smul
          continuous_subtype_val))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgs (j : ℕ) : Integrable (fun ω : Metric.sphere (0 : Euclidean d) 1 =>
      gs j (x + r • (ω : Euclidean d))) (unitSurfaceMeasure d) :=
    ((gs j).continuous.comp
      ((continuous_const : Continuous fun _ : Metric.sphere (0 : Euclidean d) 1 => x).add
        ((continuous_const : Continuous fun _ : Metric.sphere (0 : Euclidean d) 1 => r).smul
          continuous_subtype_val))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold sphericalAverage
  have hsum_apply (ω : Metric.sphere (0 : Euclidean d) 1) :
      (∑ j ∈ s, gs j) (x + r • (ω : Euclidean d)) =
        ∑ j ∈ s, gs j (x + r • (ω : Euclidean d)) := by
    change (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
      (Euclidean d) ℂ) (∑ j ∈ s, gs j) (x + r • (ω : Euclidean d)) =
        ∑ j ∈ s,
          (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
            (Euclidean d) ℂ) (gs j) (x + r • (ω : Euclidean d))
    simpa only [Finset.sum_apply] using
      congrFun (map_sum (FunLike.coeAddMonoidHom (SchwartzMap (Euclidean d) ℂ)
        (Euclidean d) ℂ) gs s) (x + r • (ω : Euclidean d))
  rw [show (fun ω : Metric.sphere (0 : Euclidean d) 1 =>
      (g + ∑ j ∈ s, gs j) (x + r • (ω : Euclidean d))) =
        fun (ω : Metric.sphere (0 : Euclidean d) 1) =>
          g (x + r • (ω : Euclidean d)) +
          ∑ j ∈ s, gs j (x + r • (ω : Euclidean d)) by
      funext ω
      rw [add_apply, hsum_apply ω]]
  have hsum : Integrable (fun ω : Metric.sphere (0 : Euclidean d) 1 =>
      ∑ j ∈ s, gs j (x + r • (ω : Euclidean d))) (unitSurfaceMeasure d) := by
    apply integrable_finsetSum
    intro j hj
    exact hgs j
  rw [MeasureTheory.integral_add hg hsum]
  rw [MeasureTheory.integral_finsetSum s (fun j _ => hgs j)]

private theorem surface_multiplier_reassembles_from_schwartz_data
    {d : ℕ} (gN g : SchwartzMap (Euclidean d) ℂ)
    (gs : ℕ → SchwartzMap (Euclidean d) ℂ) (s : Finset ℕ)
    (r : ℝ) (x : Euclidean d)
    (hdata : gN = g + ∑ j ∈ s, gs j) :
    𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * gN ξ) x =
      𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * g ξ) x +
        ∑ j ∈ s,
          𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * gs j ξ) x := by
  have hinv : (𝓕⁻ gN : SchwartzMap (Euclidean d) ℂ) =
      (𝓕⁻ g : SchwartzMap (Euclidean d) ℂ) +
        ∑ j ∈ s, (𝓕⁻ (gs j) : SchwartzMap (Euclidean d) ℂ) := by
    rw [hdata, fourierInv_add, fourierInv_sum]
  calc
    𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * gN ξ) x =
        sphericalAverage d ((𝓕⁻ gN : SchwartzMap (Euclidean d) ℂ) :
          Euclidean d → ℂ) r x :=
      (congrFun (sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier gN r) x).symm
    _ = sphericalAverage d
        ((((𝓕⁻ g : SchwartzMap (Euclidean d) ℂ) +
          ∑ j ∈ s, (𝓕⁻ (gs j) : SchwartzMap (Euclidean d) ℂ)) :
          SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r x := by
      rw [hinv]
    _ = sphericalAverage d ((𝓕⁻ g : SchwartzMap (Euclidean d) ℂ) :
          Euclidean d → ℂ) r x +
        ∑ j ∈ s, sphericalAverage d
          ((𝓕⁻ (gs j) : SchwartzMap (Euclidean d) ℂ) : Euclidean d → ℂ) r x :=
      sphericalAverage_schwartz_add_finset_sum
        (𝓕⁻ g : SchwartzMap (Euclidean d) ℂ)
        (fun j => (𝓕⁻ (gs j) : SchwartzMap (Euclidean d) ℂ)) s r x
    _ = 𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * g ξ) x +
        ∑ j ∈ s,
          𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * gs j ξ) x := by
      rw [sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier g r]
      apply congrArg (fun z : ℂ =>
        𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r • ξ) * g ξ) x + z)
      apply Finset.sum_congr rfl
      intro j hj
      exact congrFun
        (sphericalAverage_fourierInv_schwartz_eq_surfaceMultiplier (gs j) r) x

private theorem relative_cutoff_fixed_radius_le_low_add_band_sum
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ)
    (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
    (r : Ioi (0 : ℝ)) (x : Euclidean d) :
    ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) *
          φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
      ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ +
        ∑ j ∈ Finset.range N, ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
              φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ := by
  let gN : SchwartzMap (Euclidean d) ℂ := relative_radius_data φ r N f
  let g : SchwartzMap (Euclidean d) ℂ := relative_radius_data φ r 0 f
  let gs : ℕ → SchwartzMap (Euclidean d) ℂ := fun j =>
    relative_radius_data φ r (j + 1) f - relative_radius_data φ r j f
  have hdata : gN = g + ∑ j ∈ Finset.range N, gs j := by
    dsimp only [gN, g, gs]
    exact relative_radius_data_telescopes φ r N f
  have hreassemble := surface_multiplier_reassembles_from_schwartz_data
    gN g gs (Finset.range N) r.1 x hdata
  have hgN : (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) * gN ξ) =
      fun ξ => surfaceFourier d (-r.1 • ξ) *
        φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
          𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    dsimp only [gN]
    rw [relative_radius_data_apply]
    ring
  have hg : (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) * g ξ) =
      fun ξ => surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    dsimp only [g]
    rw [relative_radius_data_apply]
    norm_num
    ring
  have hgs (j : ℕ) :
      (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) * gs j ξ) =
        fun ξ => surfaceFourier d (-r.1 • ξ) *
          (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
            φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
          𝓕 (f : Euclidean d → ℂ) ξ := by
    funext ξ
    dsimp only [gs]
    rw [sub_apply, relative_radius_data_apply, relative_radius_data_apply]
    ring
  rw [hgN, hg] at hreassemble
  rw [show (∑ j ∈ Finset.range N,
      𝓕⁻ (fun ξ : Euclidean d => surfaceFourier d (-r.1 • ξ) * gs j ξ) x) =
        ∑ j ∈ Finset.range N, 𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
              φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hgs j]] at hreassemble
  have hsum :
      ‖∑ j ∈ Finset.range N, 𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
              φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ ≤
        ∑ j ∈ Finset.range N, ‖𝓕⁻ (fun ξ : Euclidean d =>
          surfaceFourier d (-r.1 • ξ) *
            (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
              φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
            𝓕 (f : Euclidean d → ℂ) ξ) x‖ := by
    exact norm_sum_le _ _
  calc
    _ = ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
          𝓕 (f : Euclidean d → ℂ) ξ) x +
          ∑ j ∈ Finset.range N, 𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) *
              (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
                φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖ := congrArg norm hreassemble
    _ ≤ ‖𝓕⁻ (fun ξ : Euclidean d =>
        surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
          𝓕 (f : Euclidean d → ℂ) ξ) x‖ +
          ‖∑ j ∈ Finset.range N, 𝓕⁻ (fun ξ : Euclidean d =>
            surfaceFourier d (-r.1 • ξ) *
              (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
                φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
              𝓕 (f : Euclidean d → ℂ) ξ) x‖ := norm_add_le _ _
    _ ≤ _ := add_le_add_right hsum _

private theorem relative_cutoff_maximal_le_low_add_band_sum
    {d : ℕ} (φ : SchwartzMap (Euclidean d) ℂ)
    (hφcompact : HasCompactSupport (φ : Euclidean d → ℂ))
    (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    relativeCutoffMaximal d φ N f x ≤
      relativeLowpassMaximal d φ f x +
        ∑ j ∈ Finset.range N, relativeBandpassMaximal d φ j f x := by
  let pval : Ioi (0 : ℝ) → ℝ := fun r =>
    ‖𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (-r.1 • ξ) *
        φ (((2 : ℝ) ^ N)⁻¹ • (r.1 • ξ)) *
        𝓕 (f : Euclidean d → ℂ) ξ) x‖
  let rval : Ioi (0 : ℝ) → ℝ := fun r =>
    ‖𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (-r.1 • ξ) * φ (r.1 • ξ) *
        𝓕 (f : Euclidean d → ℂ) ξ) x‖
  let tval : ℕ → Ioi (0 : ℝ) → ℝ := fun j r =>
    ‖𝓕⁻ (fun ξ : Euclidean d =>
      surfaceFourier d (-r.1 • ξ) *
        (φ (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • ξ)) -
          φ (((2 : ℝ) ^ j)⁻¹ • (r.1 • ξ))) *
        𝓕 (f : Euclidean d → ℂ) ξ) x‖
  let C : ℝ := (‖f.toBoundedContinuousFunction‖ *
    ∫ y : Euclidean d, ‖(𝓕⁻ φ : SchwartzMap (Euclidean d) ℂ) y‖) * surfaceMass d
  have hRbound (r : Ioi (0 : ℝ)) : rval r ≤ C := by
    dsimp only [rval, C]
    simpa only [one_smul] using (relative_lowpass_fixed_radius_bound φ f zero_lt_one r x)
  have hRbdd : BddAbove (Set.range rval) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact hRbound r
  have hTbound (j : ℕ) (r : Ioi (0 : ℝ)) : tval j r ≤ 2 * C := by
    have ha : 0 < ((2 : ℝ) ^ (j + 1))⁻¹ :=
      inv_pos.mpr (pow_pos (by norm_num) _)
    have hb : 0 < ((2 : ℝ) ^ j)⁻¹ :=
      inv_pos.mpr (pow_pos (by norm_num) _)
    dsimp only [tval, C]
    exact relative_bandpass_fixed_radius_bound φ hφcompact f ha hb r x
  have hTbdd (j : ℕ) : BddAbove (Set.range (tval j)) := by
    refine ⟨2 * C, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact hTbound j r
  letI : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  have hsup : (⨆ r : Ioi (0 : ℝ), pval r) ≤
      (⨆ r : Ioi (0 : ℝ), rval r) +
        ∑ j ∈ Finset.range N, ⨆ r : Ioi (0 : ℝ), tval j r := by
    apply ciSup_le
    intro r
    calc
      pval r ≤ rval r + ∑ j ∈ Finset.range N, tval j r :=
        relative_cutoff_fixed_radius_le_low_add_band_sum φ N f r x
      _ ≤ (⨆ r : Ioi (0 : ℝ), rval r) +
          ∑ j ∈ Finset.range N, ⨆ r : Ioi (0 : ℝ), tval j r := by
        apply add_le_add
        · exact le_ciSup hRbdd r
        · apply Finset.sum_le_sum
          intro j hj
          exact le_ciSup (hTbdd j) r
  change (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal (pval r)).toReal ≤
    (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal (rval r)).toReal +
      ∑ j ∈ Finset.range N,
        (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal (tval j r)).toReal
  simp_rw [ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
  simpa [pval, rval, tval, ENNReal.toReal_ofReal] using hsup

/- A finite sum of `MemLp` functions is again `MemLp`; the norm estimate is
the geometric summation lemma used in the reassembly argument below. -/
private theorem finite_geometric_band_sum
    {d : ℕ} {q : ENNReal} (hq : (1 : ENNReal) ≤ q)
    (T : ℕ → Euclidean d → ℝ) (hTmem : ∀ j, MemLp (T j) q volume)
    (C ρ : ENNReal)
    (hTnorm : ∀ j, eLpNorm (T j) q volume ≤ C * ρ ^ j)
    (N : ℕ) :
    MemLp (fun x => ∑ j ∈ Finset.range N, T j x) q volume ∧
      eLpNorm (fun x => ∑ j ∈ Finset.range N, T j x) q volume ≤
        C * (1 - ρ)⁻¹ := by
  constructor
  · induction N with
    | zero =>
      change MemLp 0 q volume
      exact MemLp.zero
    | succ n ih =>
      have hsum := ih.add (hTmem n)
      convert hsum using 1
      funext x
      simp only [Finset.sum_range_succ, Pi.add_apply]
  · apply eLpNorm_sum_range_le_geometric volume q hq T
    · intro j
      exact (hTmem j).1
    · exact hTnorm

/- Combine a regular maximal term with a geometrically summable collection of
band terms.  The pointwise hypothesis is kept separate from the Lp data so
this lemma can be reused for each finite reassembly. -/
private theorem finite_reassembly_eLpNorm
    {d : ℕ} {q : ENNReal} (hq : (1 : ENNReal) ≤ q)
    (P R : Euclidean d → ℝ) (T : ℕ → Euclidean d → ℝ)
    (N : ℕ) (hPmeas : AEStronglyMeasurable P volume)
    (hpointwise : ∀ x, P x ≤ R x + ∑ j ∈ Finset.range N, T j x)
    (hP0 : ∀ x, 0 ≤ P x) (hR0 : ∀ x, 0 ≤ R x)
    (hT0 : ∀ j x, 0 ≤ T j x)
    (hRmem : MemLp R q volume) (CR hroot : ENNReal)
    (hRnorm : eLpNorm R q volume ≤ CR * hroot)
    (hTmem : ∀ j, MemLp (T j) q volume) (CT ρ : ENNReal)
    (hTnorm : ∀ j, eLpNorm (T j) q volume ≤ (CT * hroot) * ρ ^ j) :
    MemLp P q volume ∧
      eLpNorm P q volume ≤ (CR + CT * (1 - ρ)⁻¹) * hroot := by
  let S : Euclidean d → ℝ := fun x => ∑ j ∈ Finset.range N, T j x
  have hS := finite_geometric_band_sum hq T hTmem (CT * hroot) ρ hTnorm N
  have hSmem : MemLp S q volume := by
    simpa only [S] using hS.1
  have hSnorm : eLpNorm S q volume ≤ (CT * hroot) * (1 - ρ)⁻¹ := by
    simpa only [S] using hS.2
  have hS0 (x : Euclidean d) : 0 ≤ S x := by
    dsimp only [S]
    exact Finset.sum_nonneg fun j _ => hT0 j x
  have hsum0 (x : Euclidean d) : 0 ≤ R x + S x :=
    add_nonneg (hR0 x) (hS0 x)
  have hsum_mem : MemLp (R + S) q volume := hRmem.add hSmem
  have hPmem : MemLp P q volume := by
    apply hsum_mem.mono hPmeas
    filter_upwards with x
    change ‖P x‖ ≤ ‖R x + S x‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x), Real.norm_eq_abs,
      abs_of_nonneg (hsum0 x)]
    simpa only [S] using hpointwise x
  refine ⟨hPmem, ?_⟩
  calc
    eLpNorm P q volume ≤ eLpNorm (R + S) q volume := by
      apply eLpNorm_mono
      intro x
      change ‖P x‖ ≤ ‖R x + S x‖
      rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x), Real.norm_eq_abs,
        abs_of_nonneg (hsum0 x)]
      simpa only [S] using hpointwise x
    _ ≤ eLpNorm R q volume + eLpNorm S q volume :=
      eLpNorm_add_le hRmem.1 hSmem.1 hq
    _ ≤ CR * hroot + (CT * hroot) * (1 - ρ)⁻¹ :=
      add_le_add hRnorm hSnorm
    _ = (CR + CT * (1 - ρ)⁻¹) * hroot := by ring


/-- Convert a nonnegative low-pass moment estimate into its `eLpNorm` form. -/
private theorem eLpNorm_le_of_lowpass_moment_bound
    {d : ℕ} {p B I : ℝ} (hp0 : 0 < p)
    (g : Euclidean d → ℝ) (hgmem : MemLp g (ENNReal.ofReal p) volume)
    (hg0 : ∀ x, 0 ≤ g x) (hB : 0 ≤ B) (hI : 0 ≤ I)
    (hmoment : (∫ x : Euclidean d, (g x) ^ p) ≤ B * I) :
    eLpNorm g (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (B ^ p⁻¹) * ENNReal.ofReal (I ^ p⁻¹) := by
  have hpNN : 0 ≤ p := hp0.le
  have hpE0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpET : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [hgmem.eLpNorm_eq_integral_rpow_norm hpE0 hpET]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hB _)]
  rw [← Real.mul_rpow hB hI]
  apply ENNReal.ofReal_le_ofReal
  rw [ENNReal.toReal_ofReal hpNN]
  apply Real.rpow_le_rpow
  · exact integral_nonneg fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
      exact Real.rpow_nonneg (hg0 x) p
  · calc
      (∫ x : Euclidean d, ‖g x‖ ^ p) = ∫ x : Euclidean d, (g x) ^ p := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
      _ ≤ B * I := hmoment
  · exact inv_nonneg.mpr hpNN

/-- Convert a nonnegative dyadic moment estimate into its `eLpNorm` form. -/
private theorem eLpNorm_le_of_bandpass_moment_bound
    {d : ℕ} {p A ε I : ℝ} (hp0 : 0 < p)
    (g : Euclidean d → ℝ) (hgmem : MemLp g (ENNReal.ofReal p) volume)
    (hg0 : ∀ x, 0 ≤ g x) (hA : 0 ≤ A) (hI : 0 ≤ I) (j : ℕ)
    (hmoment : (∫ x : Euclidean d, (g x) ^ p) ≤
      A * (2 : ℝ) ^ (-ε * j) * I) :
    eLpNorm g (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (A ^ p⁻¹) * ENNReal.ofReal (I ^ p⁻¹)) *
        ENNReal.ofReal ((2 : ℝ) ^ (-ε / p)) ^ j := by
  have hpNN : 0 ≤ p := hp0.le
  have hpE0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpET : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    eLpNorm g (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((A * (2 : ℝ) ^ (-ε * (j : ℝ)) * I) ^ p⁻¹) := by
      rw [hgmem.eLpNorm_eq_integral_rpow_norm hpE0 hpET]
      apply ENNReal.ofReal_le_ofReal
      rw [ENNReal.toReal_ofReal hpNN]
      apply Real.rpow_le_rpow
      · exact integral_nonneg fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
          exact Real.rpow_nonneg (hg0 x) p
      · calc
          (∫ x : Euclidean d, ‖g x‖ ^ p) = ∫ x : Euclidean d, (g x) ^ p := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
          _ ≤ A * (2 : ℝ) ^ (-ε * j) * I := hmoment
      · exact inv_nonneg.mpr hpNN
    _ = (ENNReal.ofReal (A ^ p⁻¹) * ENNReal.ofReal (I ^ p⁻¹)) *
          ENNReal.ofReal ((2 : ℝ) ^ (-ε / p)) ^ j := by
      rw [show (A * (2 : ℝ) ^ (-ε * (j : ℝ)) * I) ^ p⁻¹ =
          (A ^ p⁻¹ * I ^ p⁻¹) * ((2 : ℝ) ^ (-ε / p)) ^ j by
        rw [show A * (2 : ℝ) ^ (-ε * (j : ℝ)) * I =
            (A * I) * (2 : ℝ) ^ (-ε * (j : ℝ)) by ring]
        rw [Real.mul_rpow (mul_nonneg hA hI) (Real.rpow_nonneg (by norm_num) _)]
        rw [Real.mul_rpow hA hI]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        rw [show (-ε * (j : ℝ)) * p⁻¹ = (-ε / p) * (j : ℝ) by
          field_simp]
        exact Real.rpow_mul_natCast (by norm_num) _ _]
      rw [ENNReal.ofReal_mul
        (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hI _))]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hA _)]
      rw [ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _) j]

/- Assemble low-pass and band-pass moment estimates once the pointwise finite
telescoping inequality and cutoff measurability have been established. -/
private theorem finite_relative_reassembly_from_estimates
    {d : ℕ} {p : ℝ} (hpone : 1 < p)
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hregular :
      ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
        MemLp (relativeLowpassMaximal d φ f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (relativeLowpassMaximal d φ f x) ^ p) ≤
          B * ∫ x : Euclidean d, ‖f x‖ ^ p)
    (hdyadic :
      ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧
        ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
          MemLp (relativeBandpassMaximal d φ j f) (ENNReal.ofReal p) volume ∧
          (∫ x : Euclidean d, (relativeBandpassMaximal d φ j f x) ^ p) ≤
            A * (2 : ℝ) ^ (-ε * j) * ∫ x : Euclidean d, ‖f x‖ ^ p)
    (hPmeas : ∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      AEStronglyMeasurable (relativeCutoffMaximal d φ N f) volume)
    (htelescoping : ∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ)
      (x : Euclidean d),
      relativeCutoffMaximal d φ N f x ≤
        relativeLowpassMaximal d φ f x +
          ∑ j ∈ Finset.range N, relativeBandpassMaximal d φ j f x) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      MemLp (relativeCutoffMaximal d φ N f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (relativeCutoffMaximal d φ N f x) ^ p) ≤
        A * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  obtain ⟨B, hB, hreg⟩ := hregular
  obtain ⟨A, ε, hA, hε, hdy⟩ := hdyadic
  have hp0 : 0 < p := lt_trans zero_lt_one hpone
  have hpENN : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hpone.le
  let ρ : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (-ε / p))
  let CT : ENNReal := ENNReal.ofReal (A ^ p⁻¹)
  let CR : ENNReal := ENNReal.ofReal (B ^ p⁻¹)
  let D : ENNReal := CR + CT * (1 - ρ)⁻¹
  have hρreal : (2 : ℝ) ^ (-ε / p) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · norm_num
    · exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hε) hp0
  have hρ : ρ < 1 := by
    dsimp only [ρ]
    exact ENNReal.ofReal_lt_one.mpr hρreal
  have hρpos : 0 < 1 - ρ := tsub_pos_of_lt hρ
  have hρinvtop : (1 - ρ)⁻¹ < ⊤ := ENNReal.inv_lt_top.mpr hρpos
  have hCRtop : CR < ⊤ := by
    dsimp only [CR]
    exact ENNReal.ofReal_lt_top
  have hCTtop : CT < ⊤ := by
    dsimp only [CT]
    exact ENNReal.ofReal_lt_top
  have hDtop : D < ⊤ := by
    dsimp only [D]
    exact ENNReal.add_lt_top.mpr
      ⟨hCRtop, ENNReal.mul_lt_top hCTtop hρinvtop⟩
  let C : ℝ := D.toReal ^ p + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N f
  let I : ℝ := ∫ x : Euclidean d, ‖f x‖ ^ p
  have hI : 0 ≤ I := by
    dsimp only [I]
    exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
  let hroot : ENNReal := ENNReal.ofReal (I ^ p⁻¹)
  have hR0 (x : Euclidean d) : 0 ≤ relativeLowpassMaximal d φ f x :=
    ENNReal.toReal_nonneg
  have hT0 (j : ℕ) (x : Euclidean d) :
      0 ≤ relativeBandpassMaximal d φ j f x := ENNReal.toReal_nonneg
  have hP0 (x : Euclidean d) : 0 ≤ relativeCutoffMaximal d φ N f x :=
    ENNReal.toReal_nonneg
  have hRnorm : eLpNorm (relativeLowpassMaximal d φ f) (ENNReal.ofReal p)
      volume ≤ CR * hroot := by
    simpa only [CR, hroot] using
      eLpNorm_le_of_lowpass_moment_bound hp0 (relativeLowpassMaximal d φ f)
        (hreg f).1 hR0 hB.le hI (by simpa only [I] using (hreg f).2)
  have hTnorm (j : ℕ) :
      eLpNorm (relativeBandpassMaximal d φ j f) (ENNReal.ofReal p) volume ≤
        (CT * hroot) * ρ ^ j := by
    simpa only [CT, hroot, ρ] using
      eLpNorm_le_of_bandpass_moment_bound hp0
        (relativeBandpassMaximal d φ j f) (hdy j f).1 (hT0 j) hA.le hI j
        (by simpa only [I] using (hdy j f).2)
  have hP : MemLp (relativeCutoffMaximal d φ N f) (ENNReal.ofReal p) volume ∧
      eLpNorm (relativeCutoffMaximal d φ N f) (ENNReal.ofReal p) volume ≤
        D * hroot := by
    simpa only [D] using
      finite_reassembly_eLpNorm hpENN (relativeCutoffMaximal d φ N f)
        (relativeLowpassMaximal d φ f)
        (fun j => relativeBandpassMaximal d φ j f) N (hPmeas N f)
        (htelescoping N f) hP0 hR0 hT0 (hreg f).1 CR hroot hRnorm
        (fun j => (hdy j f).1) CT ρ hTnorm
  refine ⟨hP.1, ?_⟩
  change (∫ x : Euclidean d, (relativeCutoffMaximal d φ N f x) ^ p) ≤ C * I
  apply relative_cutoff_moment_bound_of_eLpNorm hpone
    (relativeCutoffMaximal d φ N f) hP.1 hP0 I hI D hDtop.ne
  · simpa only [hroot] using hP.2
  · dsimp only [C]
    exact le_add_of_nonneg_right (by norm_num)

/-- Uniform strong type for finite relative-frequency reassembly. -/
theorem finite_relative_reassembly
    {d : ℕ} (hd : 3 ≤ d) {p : ℝ}
    (hp : (d : ℝ) / ((d : ℝ) - 1) < p)
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (hregular :
      ∃ B : ℝ, 0 < B ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
        MemLp (relativeLowpassMaximal d φ f) (ENNReal.ofReal p) volume ∧
        (∫ x : Euclidean d, (relativeLowpassMaximal d φ f x) ^ p) ≤
          B * ∫ x : Euclidean d, ‖f x‖ ^ p)
    (hdyadic :
      ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧
        ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
          MemLp (relativeBandpassMaximal d φ j f) (ENNReal.ofReal p) volume ∧
          (∫ x : Euclidean d, (relativeBandpassMaximal d φ j f x) ^ p) ≤
            A * (2 : ℝ) ^ (-ε * j) * ∫ x : Euclidean d, ‖f x‖ ^ p) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      MemLp (relativeCutoffMaximal d φ N f) (ENNReal.ofReal p) volume ∧
      (∫ x : Euclidean d, (relativeCutoffMaximal d φ N f x) ^ p) ≤
        A * ∫ x : Euclidean d, ‖f x‖ ^ p := by
  have hφcompact : HasCompactSupport (φ : Euclidean d → ℂ) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) 2)
    intro ξ hξ
    apply hφzero ξ
    have hlt : 2 < ‖ξ‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hξ
      exact lt_of_not_ge hξ
    exact hlt.le
  have hdreal : (2 : ℝ) < d := by
    exact_mod_cast (show 2 < d by omega)
  have hdenom : 0 < (d : ℝ) - 1 := by linarith
  have hcritical : 1 < (d : ℝ) / ((d : ℝ) - 1) := by
    rw [lt_div_iff₀ hdenom]
    nlinarith
  have hpone : 1 < p := hcritical.trans hp
  exact finite_relative_reassembly_from_estimates hpone φ hregular hdyadic
    (fun N f => relative_cutoff_maximal_aestronglyMeasurable φ hφcompact N f)
    (fun N f x => relative_cutoff_maximal_le_low_add_band_sum φ hφcompact N f x)
end

end LeanSpherical.HarmonicAnalysis
