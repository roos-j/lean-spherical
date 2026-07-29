/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Continuity of the Fourier transform of concrete surface measure

The unit-sphere measure is finite, while its Fourier kernel has norm one.
Consequently, dominated convergence gives continuity of its Fourier--Stieltjes
transform directly.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- The oscillatory phase is jointly continuous in frequency and the point on
the unit sphere. -/
theorem continuous_surfacePhase (d : ℕ) :
    Continuous (fun p : Euclidean d × sphere (0 : Euclidean d) 1 =>
      surfacePhase d p.1 p.2) := by
  unfold surfacePhase
  fun_prop

/-- The Fourier--Stieltjes transform of the concrete unit-sphere measure is
continuous. -/
theorem continuous_surfaceFourier (d : ℕ) : Continuous (surfaceFourier d) := by
  unfold surfaceFourier
  apply continuous_of_dominated (F := fun ξ ω => Complex.exp (surfacePhase d ξ ω))
    (bound := fun _ => (1 : ℝ))
  · intro ξ
    exact ((continuous_surfacePhase d).comp
      ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => ξ).prodMk
        continuous_id)).cexp.aestronglyMeasurable
  · intro ξ
    filter_upwards with ω
    exact norm_surfaceFourier_kernel d ξ ω |>.le
  · exact integrable_const _
  · filter_upwards with ω
    exact ((continuous_surfacePhase d).comp
      (continuous_id.prodMk
        (continuous_const : Continuous fun _ : Euclidean d => ω))).cexp

/-- Restricting the concrete Fourier transform to any radial line gives a
continuous one-variable function. -/
theorem continuous_surfaceFourier_radial (d : ℕ) (ξ : Euclidean d) :
    Continuous (fun r : ℝ => surfaceFourier d (r • ξ)) := by
  exact (continuous_surfaceFourier d).comp (continuous_id.smul continuous_const)

/-- The norm of the concrete Fourier transform is continuous. -/
theorem continuous_norm_surfaceFourier (d : ℕ) :
    Continuous (fun ξ : Euclidean d => ‖surfaceFourier d ξ‖) :=
  (continuous_surfaceFourier d).norm

/-- The Fourier transform of the concrete compact surface measure is smooth
in every dimension.  This is obtained from the characteristic-function
regularity theorem after pushing surface measure forward to Euclidean space. -/
theorem contDiff_surfaceFourier (d : Nat) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (surfaceFourier d) := by
  let μ : Measure (Euclidean d) :=
    Measure.map Subtype.val (unitSurfaceMeasure d)
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hbound : ∀ᵐ x : Euclidean d ∂μ, ‖x‖ ≤ 1 := by
    rw [MeasureTheory.ae_map_iff continuous_subtype_val.aemeasurable
      (measurableSet_le continuous_norm.measurable measurable_const)]
    filter_upwards with ω
    have hnorm : ‖(ω : Euclidean d)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ω.property
    exact hnorm.le
  have htop : MemLp (id : Euclidean d → Euclidean d) ⊤ μ :=
    memLp_top_of_bound continuous_id.aestronglyMeasurable 1 hbound
  have hmoment : ∀ k : Nat, MemLp (id : Euclidean d → Euclidean d) (k : ENNReal) μ := by
    intro k
    exact htop.mono_exponent (by simp)
  have hcf : ContDiff ℝ (↑(⊤ : ℕ∞)) (MeasureTheory.charFun μ) :=
    MeasureTheory.contDiff_charFun' (n := ⊤) hmoment
  have heq : surfaceFourier d = fun ξ : Euclidean d =>
      MeasureTheory.charFun μ ((-2 * Real.pi) • ξ) := by
    funext ξ
    unfold surfaceFourier MeasureTheory.charFun μ
    rw [MeasureTheory.integral_map continuous_subtype_val.aemeasurable]
    · apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      unfold surfacePhase
      rw [inner_smul_right]
    · exact (by fun_prop)
  rw [heq]
  exact hcf.comp (ContinuousLinearMap.contDiff
    (ContinuousLinearMap.lsmul ℝ ℝ (-2 * Real.pi)))

/-- Multiplying the literal surface multiplier by compactly supported Schwartz
data produces a Schwartz multiplier, in every dimension. -/
theorem exists_schwartz_compactSupport_mul_surfaceFourier
    {d : Nat} (ψ : SchwartzMap (Euclidean d) ℂ)
    (hψcompact : HasCompactSupport (ψ : Euclidean d → ℂ))
    (r : ℝ) :
    ∃ m : SchwartzMap (Euclidean d) ℂ,
      ∀ ξ, m ξ = ψ ξ * surfaceFourier d (-r • ξ) := by
  let g : Euclidean d → ℂ := fun ξ => ψ ξ * surfaceFourier d (-r • ξ)
  have hcompact : HasCompactSupport g := by
    exact hψcompact.mul_right
  have hsurface : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun ξ : Euclidean d => surfaceFourier d (-r • ξ)) := by
    exact (contDiff_surfaceFourier d).comp
      (ContinuousLinearMap.contDiff (ContinuousLinearMap.lsmul ℝ ℝ (-r)))
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    exact (ψ.smooth (⊤ : ℕ∞)).mul hsurface
  exact ⟨hcompact.toSchwartzMap hsmooth, fun ξ => rfl⟩

/-- The radius derivative of the literal surface multiplier is also smooth
after compact Schwartz localization. -/
theorem exists_schwartz_compactSupport_mul_surfaceFourier_radius_deriv
    {d : Nat} (ψ : SchwartzMap (Euclidean d) ℂ)
    (hψcompact : HasCompactSupport (ψ : Euclidean d → ℂ))
    (r : ℝ) :
    ∃ m : SchwartzMap (Euclidean d) ℂ,
      ∀ ξ, m ξ = ψ ξ *
        deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r := by
  let D : Euclidean d → ℂ := fun ξ =>
    fderiv ℝ (surfaceFourier d) ((-r) • ξ) (-ξ)
  let g : Euclidean d → ℂ := fun ξ => ψ ξ * D ξ
  have hsurface : ContDiff ℝ (↑(⊤ : ℕ∞)) (surfaceFourier d) :=
    contDiff_surfaceFourier d
  have harg : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun ξ : Euclidean d => (-r) • ξ) :=
    ContinuousLinearMap.contDiff (ContinuousLinearMap.lsmul ℝ ℝ (-r))
  have hvec : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun ξ : Euclidean d => -ξ) := by
    simpa only [id_eq] using
      (contDiff_id.neg : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun ξ : Euclidean d => -ξ))
  let K : Euclidean d → Euclidean d → ℂ := fun _ => surfaceFourier d
  have hK : ContDiff ℝ (↑(⊤ : ℕ∞)) (Function.uncurry K) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun q : Euclidean d × Euclidean d => surfaceFourier d q.2)
    exact hsurface.comp contDiff_snd
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) D := by
    dsimp only [D]
    simpa only [K] using hK.fderiv_apply harg hvec (by simp)
  have hcompact : HasCompactSupport g := by
    exact hψcompact.mul_right
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    exact (ψ.smooth (⊤ : ℕ∞)).mul hD
  refine ⟨hcompact.toSchwartzMap hsmooth, ?_⟩
  intro ξ
  have hsfAt : HasFDerivAt (surfaceFourier d)
      (fderiv ℝ (surfaceFourier d) (r • (-ξ))) (r • (-ξ)) :=
    ((hsurface.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hlinear : HasDerivAt (fun s : ℝ => s • (-ξ)) (-ξ) r :=
    by simpa only [id_eq, one_smul] using (hasDerivAt_id r).smul_const (-ξ)
  have hderiv := hsfAt.comp_hasDerivAt r hlinear
  change ψ ξ * D ξ = ψ ξ *
    deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r
  rw [show D ξ = fderiv ℝ (surfaceFourier d) ((-r) • ξ) (-ξ) by rfl]
  rw [show ((-r) • ξ : Euclidean d) = r • (-ξ) by rw [smul_neg, neg_smul]]
  rw [show deriv (fun s : ℝ => surfaceFourier d (s • (-ξ))) r =
      fderiv ℝ (surfaceFourier d) (r • (-ξ)) (-ξ) by
    change deriv ((surfaceFourier d) ∘ fun s : ℝ => s • (-ξ)) r = _
    exact hderiv.deriv]

end

end LeanSpherical.HarmonicAnalysis
