/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.PowerWeights.CapAverageLower
import LeanSpherical.HarmonicAnalysis.CoordinateIntegration
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Group.Prod

/-!
# Anisotropic tubes for the sharp lower test

The lower test uses a horizontal bump of radius `A` and a vertical bump of
thickness `b`.  This file develops the concrete coordinate, volume, and
incidence geometry for those boxes and the curved tubes on which their
spherical averages are large.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set
open scoped ENNReal ContDiff NNReal

noncomputable section

/-- Split off the final Euclidean coordinate. -/
def succCoordinates (n : ℕ) : Euclidean (n + 1) → Euclidean n × ℝ :=
  fun x =>
    (MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i => x (Fin.castAdd 1 i)),
      x (Fin.last n))

/-- Reassemble a Euclidean vector from its first `n` coordinates and its
final coordinate. -/
def joinCoordinates (n : ℕ) : Euclidean n × ℝ → Euclidean (n + 1) :=
  fun z =>
    MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)
      (Fin.lastCases z.2 (fun i => z.1 i))

theorem succCoordinates_joinCoordinates (n : ℕ) (z : Euclidean n) (t : ℝ) :
    succCoordinates n (joinCoordinates n (z, t)) = (z, t) := by
  apply Prod.ext
  · apply (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.injective
    funext i
    have hi : Fin.castAdd 1 i = Fin.castSucc i := Fin.ext rfl
    simp [succCoordinates, joinCoordinates, hi]
  · simp [succCoordinates, joinCoordinates]

theorem joinCoordinates_succCoordinates (n : ℕ) (x : Euclidean (n + 1)) :
    joinCoordinates n (succCoordinates n x) = x := by
  apply (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.injective
  funext i
  cases i using Fin.lastCases
  · simp [succCoordinates, joinCoordinates]
  · rename_i i
    have hi : Fin.castAdd 1 i = Fin.castSucc i := Fin.ext rfl
    simp [succCoordinates, joinCoordinates, hi]

theorem succCoordinates_add (n : ℕ) (x y : Euclidean (n + 1)) :
    succCoordinates n (x + y) = succCoordinates n x + succCoordinates n y := by
  apply Prod.ext
  · apply (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.injective
    funext i
    simp [succCoordinates]
  · simp [succCoordinates]

theorem succCoordinates_smul (n : ℕ) (c : ℝ) (x : Euclidean (n + 1)) :
    succCoordinates n (c • x) = c • succCoordinates n x := by
  apply Prod.ext
  · apply (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.injective
    funext i
    simp [succCoordinates]
  · simp [succCoordinates]

theorem succCoordinates_sub (n : ℕ) (x y : Euclidean (n + 1)) :
    succCoordinates n (x - y) = succCoordinates n x - succCoordinates n y := by
  rw [sub_eq_add_neg, succCoordinates_add, ← neg_one_smul ℝ y,
    succCoordinates_smul]
  simp [sub_eq_add_neg]

theorem measurable_succCoordinates (n : ℕ) : Measurable (succCoordinates n) := by
  unfold succCoordinates
  fun_prop

theorem contDiff_succCoordinates (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (succCoordinates n) := by
  have hraw : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Euclidean (n + 1) => fun i : Fin n => x (Fin.castAdd 1 i)) := by
    rw [contDiff_pi]
    intro i
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castAdd 1 i)).contDiff
  have hto : ContDiff ℝ (⊤ : ℕ∞)
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff
  have hfirst : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Euclidean (n + 1) =>
        MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i => x (Fin.castAdd 1 i))) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (MeasurableEquiv.toLp 2 (Fin n → ℝ) ∘
        fun x : Euclidean (n + 1) => fun i : Fin n => x (Fin.castAdd 1 i))
    exact hto.comp hraw
  have hlast : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Euclidean (n + 1) => x (Fin.last n)) := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).contDiff
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Euclidean (n + 1) =>
      (MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i => x (Fin.castAdd 1 i)),
        x (Fin.last n)))
  exact hfirst.prodMk hlast

theorem norm_sq_succCoordinates (n : ℕ) (x : Euclidean (n + 1)) :
    ‖x‖ ^ 2 = ‖(succCoordinates n x).1‖ ^ 2 + (succCoordinates n x).2 ^ 2 := by
  exact norm_sq_euclideanSucc_coordinates n x

theorem norm_le_succCoordinates (n : ℕ) (x : Euclidean (n + 1)) :
    ‖x‖ ≤ ‖(succCoordinates n x).1‖ + |(succCoordinates n x).2| := by
  have hsq := norm_sq_succCoordinates n x
  have habs : |(succCoordinates n x).2| ^ 2 = (succCoordinates n x).2 ^ 2 :=
    sq_abs _
  rw [← habs] at hsq
  have hnonneg : 0 ≤ ‖(succCoordinates n x).1‖ * |(succCoordinates n x).2| :=
    mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsqle : ‖x‖ ^ 2 ≤
      (‖(succCoordinates n x).1‖ + |(succCoordinates n x).2|) ^ 2 := by
    rw [hsq]
    nlinarith
  have habsle := sq_le_sq.mp hsqle
  simpa only [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (add_nonneg (norm_nonneg _) (abs_nonneg _))] using habsle

theorem norm_fst_succCoordinates_le_norm (n : ℕ) (x : Euclidean (n + 1)) :
    ‖(succCoordinates n x).1‖ ≤ ‖x‖ := by
  have hsq := norm_sq_succCoordinates n x
  have hsqle : ‖(succCoordinates n x).1‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (succCoordinates n x).2]
  have hle := sq_le_sq.mp hsqle
  simpa only [abs_of_nonneg (norm_nonneg _)] using hle

theorem abs_snd_succCoordinates_le_norm (n : ℕ) (x : Euclidean (n + 1)) :
    |(succCoordinates n x).2| ≤ ‖x‖ := by
  have hsq := norm_sq_succCoordinates n x
  have habs : |(succCoordinates n x).2| ^ 2 = (succCoordinates n x).2 ^ 2 := sq_abs _
  rw [← habs] at hsq
  have hsqle : |(succCoordinates n x).2| ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(succCoordinates n x).1‖]
  have hle := sq_le_sq.mp hsqle
  simpa only [abs_of_nonneg (abs_nonneg _), abs_of_nonneg (norm_nonneg _)] using hle

/-- On the upper hemisphere, a small Euclidean cap has quadratic vertical
variation once its centre is close to the vertical axis.  This is the
curvature gain used by the sharp tube test. -/
theorem abs_snd_sub_le_horizontal_mul_of_unit_vectors
    (n : ℕ) {u v : Euclidean (n + 1)} {h : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hh : 0 ≤ h) (hquarter : h ≤ 1 / 4)
    (hvlast : 1 / 2 ≤ (succCoordinates n v).2) (hdist : dist u v ≤ h) :
    |(succCoordinates n u).2 - (succCoordinates n v).2| ≤
      4 * (‖(succCoordinates n v).1‖ * h + h ^ 2) := by
  have hnormsub : ‖u - v‖ ≤ h := by
    simpa only [dist_eq_norm_sub] using hdist
  have hhor : ‖(succCoordinates n u).1 - (succCoordinates n v).1‖ ≤ h := by
    calc
      ‖(succCoordinates n u).1 - (succCoordinates n v).1‖ =
          ‖(succCoordinates n (u - v)).1‖ := by
            simp only [succCoordinates_sub, Prod.fst_sub]
      _ ≤ ‖u - v‖ := norm_fst_succCoordinates_le_norm n (u - v)
      _ ≤ h := hnormsub
  have hvertical : |(succCoordinates n u).2 - (succCoordinates n v).2| ≤ h := by
    calc
      |(succCoordinates n u).2 - (succCoordinates n v).2| =
          |(succCoordinates n (u - v)).2| := by
            simp only [succCoordinates_sub, Prod.snd_sub]
      _ ≤ ‖u - v‖ := abs_snd_succCoordinates_le_norm n (u - v)
      _ ≤ h := hnormsub
  let U : ℝ := ‖(succCoordinates n u).1‖
  let V : ℝ := ‖(succCoordinates n v).1‖
  let s : ℝ := (succCoordinates n u).2
  let t : ℝ := (succCoordinates n v).2
  have hUV : |V - U| ≤ h := by
    calc
      |V - U| ≤ ‖(succCoordinates n v).1 - (succCoordinates n u).1‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖(succCoordinates n u).1 - (succCoordinates n v).1‖ := norm_sub_rev _ _
      _ ≤ h := hhor
  have hUle : U ≤ V + h := by
    have : U - V ≤ h := (le_abs_self _).trans (by simpa only [abs_sub_comm] using hUV)
    linarith
  have hsum : V + U ≤ 2 * V + h := by linarith
  have hnormu : U ^ 2 + s ^ 2 = 1 := by
    dsimp only [U, s]
    nlinarith [norm_sq_succCoordinates n u]
  have hnormv : V ^ 2 + t ^ 2 = 1 := by
    dsimp only [V, t]
    nlinarith [norm_sq_succCoordinates n v]
  have hsqdiff : |s ^ 2 - t ^ 2| = |V ^ 2 - U ^ 2| := by
    congr 1
    nlinarith
  have hquad : |V ^ 2 - U ^ 2| ≤ h * (2 * V + h) := by
    calc
      |V ^ 2 - U ^ 2| = |(V - U) * (V + U)| := by
        congr 1
        ring
      _ = |V - U| * |V + U| := abs_mul _ _
      _ = |V - U| * (V + U) := by
        rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      _ ≤ h * (2 * V + h) := by
        exact mul_le_mul hUV hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) hh
  have hs_lower : t - h ≤ s := by
    rcases abs_le.mp (by simpa only [s, t] using hvertical) with ⟨hleft, _⟩
    linarith
  have hst : 1 / 2 ≤ s + t := by
    have ht : 1 / 2 ≤ t := by simpa only [t] using hvlast
    linarith
  have hprod : |s - t| * (s + t) = |s ^ 2 - t ^ 2| := by
    have hsum_nonneg : 0 ≤ s + t := by linarith
    calc
      |s - t| * (s + t) = |s - t| * |s + t| := by
        rw [abs_of_nonneg hsum_nonneg]
      _ = |(s - t) * (s + t)| := (abs_mul _ _).symm
      _ = |s ^ 2 - t ^ 2| := by
        congr 1
        ring
  have hlinear : |s - t| ≤ 2 * |s ^ 2 - t ^ 2| := by
    have hnonneg : 0 ≤ (s + t - 1 / 2) * |s - t| :=
      mul_nonneg (by linarith) (abs_nonneg _)
    nlinarith
  calc
    |(succCoordinates n u).2 - (succCoordinates n v).2| = |s - t| := by rfl
    _ ≤ 2 * |s ^ 2 - t ^ 2| := hlinear
    _ = 2 * |V ^ 2 - U ^ 2| := by rw [hsqdiff]
    _ ≤ 4 * (V * h + h ^ 2) := by
      nlinarith [sq_nonneg h]
    _ = 4 * (‖(succCoordinates n v).1‖ * h + h ^ 2) := by rfl

/-- A horizontal ball times a vertical open interval, pulled back to
Euclidean space. -/
def horizontalSlab (n : ℕ) (ρ a b : ℝ) : Set (Euclidean (n + 1)) :=
  succCoordinates n ⁻¹' (ball (0 : Euclidean n) ρ ×ˢ Ioo a b)

theorem measurableSet_horizontalSlab (n : ℕ) (ρ a b : ℝ) :
    MeasurableSet (horizontalSlab n ρ a b) := by
  unfold horizontalSlab
  exact (measurableSet_ball.prod measurableSet_Ioo).preimage
    (measurable_succCoordinates n)

/-- Exact Lebesgue volume of a horizontal ball times a vertical interval. -/
theorem volume_horizontalSlab (n : ℕ) (ρ a b : ℝ) :
    volume (horizontalSlab n ρ a b) =
      volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (b - a) := by
  let S : Set (Euclidean n × ℝ) := ball (0 : Euclidean n) ρ ×ˢ Ioo a b
  have hS : MeasurableSet S := measurableSet_ball.prod measurableSet_Ioo
  have hmap : Measure.map (succCoordinates n) volume =
      ((volume : Measure (Euclidean n)).prod volume) := by
    have h := map_euclideanSucc_coordinates_volume n
    change Measure.map (succCoordinates n) volume =
      ((volume : Measure (Euclidean n)).prod volume) at h
    exact h
  calc
    volume (horizontalSlab n ρ a b) =
        Measure.map (succCoordinates n) volume S := by
      change volume ((succCoordinates n) ⁻¹' S) =
        Measure.map (succCoordinates n) volume S
      exact (Measure.map_apply (measurable_succCoordinates n) hS).symm
    _ = ((volume : Measure (Euclidean n)).prod volume) S := by rw [hmap]
    _ = volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (b - a) := by
      dsimp only [S]
      rw [Measure.prod_prod, Real.volume_Ioo]

/-- A convenient outer radius for the product cutoff. -/
def anisotropicCutoffRadius (ρ b a : ℝ) : ℝ := ρ + |a| + b

theorem anisotropicCutoffRadius_pos {ρ b a : ℝ} (hρ : 0 < ρ) (hb : 0 < b) :
    0 < anisotropicCutoffRadius ρ b a := by
  unfold anisotropicCutoffRadius
  positivity

noncomputable def anisotropicOuterBump (n : ℕ) (ρ b a : ℝ)
    (hρ : 0 < ρ) (hb : 0 < b) : ContDiffBump (0 : Euclidean (n + 1)) :=
  ⟨anisotropicCutoffRadius ρ b a, 2 * anisotropicCutoffRadius ρ b a,
    anisotropicCutoffRadius_pos (a := a) hρ hb,
    by linarith [anisotropicCutoffRadius_pos (a := a) hρ hb]⟩

noncomputable def anisotropicHorizontalBump (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiffBump (0 : Euclidean n) :=
  ⟨ρ, 2 * ρ, hρ, by linarith⟩

noncomputable def anisotropicVerticalBump (a b : ℝ) (hb : 0 < b) : ContDiffBump a :=
  ⟨b, 2 * b, hb, by linarith⟩

/-- A smooth test function for one horizontal slab.  It is one on the slab,
bounded between zero and one, and vanishes as soon as either slab coordinate
leaves the doubled box.  The outer bump only supplies compact support. -/
theorem exists_schwartz_horizontalSlab_cutoff (n : ℕ) {A B a : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    ∃ g : Euclidean (n + 1) → ℝ, ∃ f : SchwartzMap (Euclidean (n + 1)) ℂ,
      (∀ y, f y = (g y : ℂ)) ∧
      Continuous g ∧
      (∀ y, 0 ≤ g y) ∧
      (∀ y, g y ≤ 1) ∧
      (∀ y ∈ horizontalSlab n A (a - B) (a + B), g y = 1) ∧
      (∀ y, 2 * A ≤ ‖(succCoordinates n y).1‖ → g y = 0) ∧
      (∀ y, 2 * B ≤ |(succCoordinates n y).2 - a| → g y = 0) ∧
      (∀ y ∉ horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B), g y = 0) := by
  let bO : ContDiffBump (0 : Euclidean (n + 1)) :=
    anisotropicOuterBump n A B a hA hB
  let bH : ContDiffBump (0 : Euclidean n) := anisotropicHorizontalBump n A hA
  let bV : ContDiffBump a := anisotropicVerticalBump a B hB
  let g : Euclidean (n + 1) → ℝ := fun y =>
    bO y * bH (succCoordinates n y).1 * bV (succCoordinates n y).2
  let o : Euclidean (n + 1) → ℂ := fun y => (bO y : ℂ)
  let qH : Euclidean (n + 1) → ℂ :=
    fun y => (bH (succCoordinates n y).1 : ℂ)
  let qV : Euclidean (n + 1) → ℂ :=
    fun y => (bV (succCoordinates n y).2 : ℂ)
  let q : Euclidean (n + 1) → ℂ := fun y => o y * qH y * qV y
  have hoCompact : HasCompactSupport o := by
    change HasCompactSupport (Complex.ofRealCLM ∘ bO)
    exact bO.hasCompactSupport.comp_left (by rfl)
  have hoSmooth : ContDiff ℝ (⊤ : ℕ∞) o := by
    change ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ bO)
    exact Complex.ofRealCLM.contDiff.comp bO.contDiff
  have hHSmooth : ContDiff ℝ (⊤ : ℕ∞) qH := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (Complex.ofRealCLM ∘ bH ∘ fun y : Euclidean (n + 1) =>
        (succCoordinates n y).1)
    exact Complex.ofRealCLM.contDiff.comp
      (bH.contDiff.comp (contDiff_succCoordinates n).fst)
  have hVSmooth : ContDiff ℝ (⊤ : ℕ∞) qV := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (Complex.ofRealCLM ∘ bV ∘ fun y : Euclidean (n + 1) =>
        (succCoordinates n y).2)
    exact Complex.ofRealCLM.contDiff.comp
      (bV.contDiff.comp (contDiff_succCoordinates n).snd)
  have hqCompact : HasCompactSupport q := by
    have hoHCompact : HasCompactSupport (o * qH) :=
      HasCompactSupport.mul_right (f' := qH) hoCompact
    change HasCompactSupport ((o * qH) * qV)
    exact HasCompactSupport.mul_right (f' := qV) hoHCompact
  have hqSmooth : ContDiff ℝ (⊤ : ℕ∞) q := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => o y * qH y * qV y)
    exact (hoSmooth.mul hHSmooth).mul hVSmooth
  let f : SchwartzMap (Euclidean (n + 1)) ℂ := hqCompact.toSchwartzMap hqSmooth
  have hbO : ContDiff ℝ (⊤ : ℕ∞) bO := bO.contDiff
  have hbH : ContDiff ℝ (⊤ : ℕ∞) bH := bH.contDiff
  have hbV : ContDiff ℝ (⊤ : ℕ∞) bV := bV.contDiff
  have hgContinuous : Continuous g := by
    dsimp only [g]
    exact ((hbO.continuous.mul
      (hbH.continuous.comp (contDiff_succCoordinates n).continuous.fst)).mul
      (hbV.continuous.comp (contDiff_succCoordinates n).continuous.snd))
  refine ⟨g, f, ?_, hgContinuous, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    change q y = (g y : ℂ)
    simp [q, o, qH, qV, g, Complex.ofReal_mul]
  · intro y
    dsimp only [g]
    exact mul_nonneg (mul_nonneg bO.nonneg bH.nonneg) bV.nonneg
  · intro y
    dsimp only [g]
    exact mul_le_one₀ (mul_le_one₀ bO.le_one bH.nonneg bH.le_one)
      bV.nonneg bV.le_one
  · intro y hy
    change succCoordinates n y ∈ ball (0 : Euclidean n) A ×ˢ Ioo (a - B) (a + B) at hy
    rcases hy with ⟨hyH, hyV⟩
    have hyH' : ‖(succCoordinates n y).1‖ ≤ A := by
      have hyHlt : ‖(succCoordinates n y).1‖ < A := by
        simpa only [Metric.mem_ball, dist_zero_right] using hyH
      exact le_of_lt hyHlt
    have hyV' : |(succCoordinates n y).2 - a| < B := by
      rw [abs_lt]
      constructor <;> linarith [hyV.1, hyV.2]
    have hyO : ‖y‖ ≤ anisotropicCutoffRadius A B a := by
      apply le_trans (norm_le_succCoordinates n y)
      have hvertical : |(succCoordinates n y).2| ≤ |a| + B := by
        apply le_of_lt
        calc
          |(succCoordinates n y).2| =
              |((succCoordinates n y).2 - a) + a| := by ring_nf
          _ ≤ |(succCoordinates n y).2 - a| + |a| := abs_add_le _ _
          _ < B + |a| := by linarith [hyV']
          _ = |a| + B := by ring
      unfold anisotropicCutoffRadius
      linarith
    have hOone : bO y = 1 := by
      apply bO.one_of_mem_closedBall
      change y ∈ Metric.closedBall (0 : Euclidean (n + 1))
        (anisotropicCutoffRadius A B a)
      simpa only [Metric.mem_closedBall, dist_zero_right] using hyO
    have hHone : bH (succCoordinates n y).1 = 1 := by
      apply bH.one_of_mem_closedBall
      change (succCoordinates n y).1 ∈ Metric.closedBall (0 : Euclidean n) A
      simpa only [Metric.mem_closedBall, dist_zero_right] using hyH'
    have hVone : bV (succCoordinates n y).2 = 1 := by
      apply bV.one_of_mem_closedBall
      change (succCoordinates n y).2 ∈ Metric.closedBall a B
      simpa only [Metric.mem_closedBall, Real.dist_eq] using le_of_lt hyV'
    dsimp only [g]
    rw [hOone, hHone, hVone]
    norm_num
  · intro y hy
    dsimp only [g]
    have hzero : bH (succCoordinates n y).1 = 0 := by
      apply bH.zero_of_le_dist
      change 2 * A ≤ dist (succCoordinates n y).1 0
      simpa only [dist_zero_right] using hy
    rw [hzero]
    ring
  · intro y hy
    dsimp only [g]
    have hzero : bV (succCoordinates n y).2 = 0 := by
      apply bV.zero_of_le_dist
      change 2 * B ≤ dist (succCoordinates n y).2 a
      simpa only [Real.dist_eq] using hy
    rw [hzero]
    ring
  · intro y hy
    by_cases hyH : ‖(succCoordinates n y).1‖ < 2 * A
    · by_cases hyV : (succCoordinates n y).2 ∈ Ioo (a - 2 * B) (a + 2 * B)
      · exact False.elim (hy (by
          change succCoordinates n y ∈
            ball (0 : Euclidean n) (2 * A) ×ˢ Ioo (a - 2 * B) (a + 2 * B)
          constructor
          · simpa only [Metric.mem_ball, dist_zero_right] using hyH
          · exact hyV))
      · have hdev : 2 * B ≤ |(succCoordinates n y).2 - a| := by
          apply le_of_not_gt
          intro hlt
          apply hyV
          rw [abs_lt] at hlt
          constructor <;> linarith
        dsimp only [g]
        have hzero : bV (succCoordinates n y).2 = 0 := by
          apply bV.zero_of_le_dist
          change 2 * B ≤ dist (succCoordinates n y).2 a
          simpa only [Real.dist_eq] using hdev
        rw [hzero]
        ring
    · have hbound : 2 * A ≤ ‖(succCoordinates n y).1‖ := le_of_not_gt hyH
      dsimp only [g]
      have hzero : bH (succCoordinates n y).1 = 0 := by
        apply bH.zero_of_le_dist
        change 2 * A ≤ dist (succCoordinates n y).1 0
        simpa only [dist_zero_right] using hbound
      rw [hzero]
      ring

/-- The cutoff from `exists_schwartz_horizontalSlab_cutoff` has weighted
input norm controlled by the weighted measure of its literal doubled slab. -/
theorem eLpNorm_horizontalSlab_cutoff_le (n : ℕ) {p α A B a : ℝ}
    (hp0 : ENNReal.ofReal p ≠ 0)
    (g : Euclidean (n + 1) → ℝ) (f : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hfg : ∀ y, f y = (g y : ℂ))
    (hgnonneg : ∀ y, 0 ≤ g y) (hgle_one : ∀ y, g y ≤ 1)
    (hsupport : ∀ y ∉ horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B),
      g y = 0) :
    eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume (n + 1) α) ≤
      (powerWeightedVolume (n + 1) α
        (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B))) ^
          (1 / (ENNReal.ofReal p).toReal) := by
  let D : Set (Euclidean (n + 1)) :=
    horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B)
  have hD : MeasurableSet D :=
    measurableSet_horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B)
  calc
    eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume (n + 1) α) ≤
      eLpNorm (D.indicator (fun _ : Euclidean (n + 1) => (1 : ℂ)))
        (ENNReal.ofReal p) (powerWeightedVolume (n + 1) α) := by
          apply eLpNorm_mono
          intro y
          by_cases hy : y ∈ D
          · rw [indicator_of_mem hy, hfg]
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgnonneg y)]
            simpa using hgle_one y
          · have hzero : g y = 0 := hsupport y (by simpa only [D] using hy)
            rw [indicator_of_notMem hy, hfg, hzero]
            norm_num
    _ = (powerWeightedVolume (n + 1) α D) ^
          (1 / (ENNReal.ofReal p).toReal) := by
      rw [eLpNorm_indicator_const hD hp0 ENNReal.ofReal_ne_top]
      norm_num [enorm]
    _ = (powerWeightedVolume (n + 1) α
        (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B))) ^
          (1 / (ENNReal.ofReal p).toReal) := by rfl

/-- Away from the origin a nonpositive radial power is bounded above by its
value at any lower bound for the radius. -/
theorem radialPowerWeight_le_of_norm_lower
    {d : ℕ} {α r : ℝ} (hα : α ≤ 0) (hr : 0 < r)
    {x : Euclidean d} (hx : r ≤ ‖x‖) :
    radialPowerWeight d α x ≤ (ENNReal.ofReal r) ^ α := by
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hr hx
  unfold radialPowerWeight
  rw [ENNReal.ofReal_rpow_of_pos hr, ENNReal.ofReal_rpow_of_pos hxpos]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_nonpos hr hx hα)

/-- A negative radial power is bounded below on a ball by its value at the
outer radius, including at the origin where the density is infinite. -/
theorem radialPowerWeight_ball_lower_for_tube
    {d : ℕ} {α R : ℝ} (hα : α < 0) (hR : 0 < R)
    {x : Euclidean d} (hx : x ∈ ball (0 : Euclidean d) R) :
    (ENNReal.ofReal R) ^ α ≤ radialPowerWeight d α x := by
  rw [Metric.mem_ball, dist_zero_right] at hx
  by_cases hxzero : x = 0
  · subst x
    simp [radialPowerWeight, ENNReal.zero_rpow_of_neg hα]
  · have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hxzero
    unfold radialPowerWeight
    rw [ENNReal.ofReal_rpow_of_pos hR,
      ENNReal.ofReal_rpow_of_pos hnormpos]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos hnormpos hx.le hα.le)

/-- Any measurable set contained in a ball has at least its Lebesgue volume
times the outer-radius negative power weight. -/
theorem powerWeightedVolume_set_lower_of_subset_ball
    {d : ℕ} {α R : ℝ} {S : Set (Euclidean d)}
    (hα : α < 0) (hR : 0 < R) (hS : MeasurableSet S)
    (hsubset : S ⊆ ball (0 : Euclidean d) R) :
    (ENNReal.ofReal R) ^ α * volume S ≤ powerWeightedVolume d α S := by
  calc
    (ENNReal.ofReal R) ^ α * volume S =
        ∫⁻ _x in S, (ENNReal.ofReal R) ^ α :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in S, radialPowerWeight d α x ∂volume := by
      apply setLIntegral_mono (measurable_radialPowerWeight d α)
      intro x hx
      exact radialPowerWeight_ball_lower_for_tube hα hR (hsubset hx)
    _ = powerWeightedVolume d α S := by
      rw [powerWeightedVolume, withDensity_apply _ hS]

/-- The literal horizontal slab used for the input cutoff has weighted volume
at most its exact product volume times the power weight at its lower vertical
radius. -/
theorem powerWeightedVolume_horizontalSlab_le_of_nonpos
    (n : ℕ) {α A B a : ℝ} (hα : α ≤ 0) (haB : 0 < a - B) :
    powerWeightedVolume (n + 1) α (horizontalSlab n A (a - B) (a + B)) ≤
      (ENNReal.ofReal (a - B)) ^ α *
        (volume (ball (0 : Euclidean n) A) * ENNReal.ofReal (2 * B)) := by
  let D : Set (Euclidean (n + 1)) := horizontalSlab n A (a - B) (a + B)
  have hD : MeasurableSet D := measurableSet_horizontalSlab n A (a - B) (a + B)
  have hpoint (y : Euclidean (n + 1)) (hy : y ∈ D) :
      radialPowerWeight (n + 1) α y ≤ (ENNReal.ofReal (a - B)) ^ α := by
    change succCoordinates n y ∈ ball (0 : Euclidean n) A ×ˢ Ioo (a - B) (a + B) at hy
    have ht : a - B < (succCoordinates n y).2 := hy.2.1
    have hnorm : a - B ≤ ‖y‖ := by
      calc
        a - B ≤ (succCoordinates n y).2 := le_of_lt ht
        _ ≤ |(succCoordinates n y).2| := le_abs_self _
        _ ≤ ‖y‖ := abs_snd_succCoordinates_le_norm n y
    exact radialPowerWeight_le_of_norm_lower hα haB hnorm
  calc
    powerWeightedVolume (n + 1) α D =
        ∫⁻ y in D, radialPowerWeight (n + 1) α y ∂volume := by
      rw [powerWeightedVolume, withDensity_apply _ hD]
    _ ≤ ∫⁻ _y in D, (ENNReal.ofReal (a - B)) ^ α ∂volume := by
      exact setLIntegral_mono measurable_const hpoint
    _ = (ENNReal.ofReal (a - B)) ^ α * volume D :=
      setLIntegral_const _ _
    _ = (ENNReal.ofReal (a - B)) ^ α *
        (volume (ball (0 : Euclidean n) A) * ENNReal.ofReal (2 * B)) := by
      rw [volume_horizontalSlab]
      have hwidth : (a + B) - (a - B) = 2 * B := by ring
      rw [hwidth]

/-- In particular, every such slab has finite weighted volume. -/
theorem powerWeightedVolume_horizontalSlab_lt_top_of_nonpos
    (n : ℕ) {α A B a : ℝ} (hα : α ≤ 0) (haB : 0 < a - B) :
    powerWeightedVolume (n + 1) α (horizontalSlab n A (a - B) (a + B)) <
      (∞ : ℝ≥0∞) := by
  refine (powerWeightedVolume_horizontalSlab_le_of_nonpos n hα haB).trans_lt ?_
  apply ENNReal.mul_lt_top
  · rw [ENNReal.ofReal_rpow_of_pos haB]
    exact ENNReal.ofReal_lt_top
  · apply ENNReal.mul_lt_top
    · exact measure_ball_lt_top
    · exact ENNReal.ofReal_lt_top

/-- Vertical translation by a measurable height function. -/
def verticalShear (n : ℕ) (φ : Euclidean n → ℝ) :
    Euclidean n × ℝ → Euclidean n × ℝ := fun z => (z.1, z.2 + φ z.1)

/-- The measurable equivalence underlying a vertical shear. -/
def verticalShearEquiv (n : ℕ) (φ : Euclidean n → ℝ)
    (hφ : Measurable φ) : Euclidean n × ℝ ≃ᵐ Euclidean n × ℝ where
  toEquiv :=
    { toFun := verticalShear n φ
      invFun := fun z => (z.1, z.2 - φ z.1)
      left_inv := by
        intro z
        ext <;> simp [verticalShear]
      right_inv := by
        intro z
        ext <;> simp [verticalShear] }
  measurable_toFun := by
    exact measurable_fst.prodMk (measurable_snd.add (hφ.comp measurable_fst))
  measurable_invFun := by
    exact measurable_fst.prodMk (measurable_snd.sub (hφ.comp measurable_fst))

theorem measurePreserving_verticalShear (n : ℕ) (φ : Euclidean n → ℝ)
    (hφ : Measurable φ) :
    MeasurePreserving (verticalShear n φ)
      ((volume : Measure (Euclidean n)).prod volume)
      ((volume : Measure (Euclidean n)).prod volume) := by
  refine MeasurePreserving.skew_product
    (μa := (volume : Measure (Euclidean n))) (μc := (volume : Measure ℝ))
    (μd := (volume : Measure ℝ))
    (MeasurePreserving.id (volume : Measure (Euclidean n)))
    (g := fun z (t : ℝ) => t + φ z) ?_ ?_
  · exact measurable_snd.add (hφ.comp measurable_fst)
  · filter_upwards [] with z
    exact MeasureTheory.map_add_right_eq_self volume (φ z)

/-- The lower branch of a radius-`r` sphere over the horizontal plane,
translated so that it passes through vertical height `a`. -/
def graphHeight (r a : ℝ) (z : Euclidean n) : ℝ :=
  a - Real.sqrt (r ^ 2 - ‖z‖ ^ 2)

theorem measurable_graphHeight (r a : ℝ) : Measurable (graphHeight (n := n) r a) := by
  unfold graphHeight
  fun_prop

/-- Over a horizontal ball of radius at most the sphere radius, the lower
spherical graph stays within one horizontal radius of its axial height. -/
theorem graphHeight_abs_le_abs_sub_add_horizontal
    (n : ℕ) {r a ρ : ℝ} (hr : 0 ≤ r) (hρr : ρ ≤ r)
    {z : Euclidean n} (hz : ‖z‖ ≤ ρ) :
    |graphHeight r a z| ≤ |a - r| + ρ := by
  have hρnonneg : 0 ≤ ρ := (norm_nonneg z).trans hz
  have hzsquare : ‖z‖ ^ 2 ≤ ρ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg z) hρnonneg).mpr hz
  have hradic : 0 ≤ r ^ 2 - ‖z‖ ^ 2 := by nlinarith
  have hsqrt : 0 ≤ Real.sqrt (r ^ 2 - ‖z‖ ^ 2) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (r ^ 2 - ‖z‖ ^ 2) ^ 2 = r ^ 2 - ‖z‖ ^ 2 :=
    Real.sq_sqrt hradic
  have hsqrt_le : Real.sqrt (r ^ 2 - ‖z‖ ^ 2) ≤ r := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hr
    · nlinarith
  have hdiff : 0 ≤ r - Real.sqrt (r ^ 2 - ‖z‖ ^ 2) := sub_nonneg.mpr hsqrt_le
  have hcurvature : r - Real.sqrt (r ^ 2 - ‖z‖ ^ 2) ≤ ρ := by
    have hsq : (r - ρ) ^ 2 ≤ Real.sqrt (r ^ 2 - ‖z‖ ^ 2) ^ 2 := by
      rw [hsqrt_sq]
      nlinarith [mul_nonneg hρnonneg (sub_nonneg.mpr hρr)]
    have hleft : 0 ≤ r - ρ := sub_nonneg.mpr hρr
    have hle := sq_le_sq.mp hsq
    have hroot : r - ρ ≤ Real.sqrt (r ^ 2 - ‖z‖ ^ 2) := by
      simpa only [abs_of_nonneg hleft, abs_of_nonneg hsqrt] using hle
    linarith
  calc
    |graphHeight r a z| = |(a - r) + (r - Real.sqrt (r ^ 2 - ‖z‖ ^ 2))| := by
      unfold graphHeight
      congr 1
      ring
    _ ≤ |a - r| + |r - Real.sqrt (r ^ 2 - ‖z‖ ^ 2)| := abs_add_le _ _
    _ = |a - r| + (r - Real.sqrt (r ^ 2 - ‖z‖ ^ 2)) := by rw [abs_of_nonneg hdiff]
    _ ≤ |a - r| + ρ := by gcongr

/-- The unit direction from a point on the lower radius-`r` graph toward its
vertical-axis centre.  For a point in a tube, it is still the central
direction associated to the same horizontal coordinate. -/
def graphDirection (n : ℕ) (r : ℝ) (x : Euclidean (n + 1)) : Euclidean (n + 1) :=
  joinCoordinates n
    (- (r⁻¹ • (succCoordinates n x).1),
      Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) / r)

theorem succCoordinates_graphDirection (n : ℕ) (r : ℝ) (x : Euclidean (n + 1)) :
    succCoordinates n (graphDirection n r x) =
      (- (r⁻¹ • (succCoordinates n x).1),
        Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) / r) := by
  unfold graphDirection
  exact succCoordinates_joinCoordinates _ _ _

theorem norm_graphDirection (n : ℕ) {r : ℝ} (x : Euclidean (n + 1))
    (hr : 0 < r) (hz : ‖(succCoordinates n x).1‖ ≤ r) :
    ‖graphDirection n r x‖ = 1 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have harg : 0 ≤ r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2 := by
    nlinarith [norm_nonneg (succCoordinates n x).1]
  have hnorm : ‖- (r⁻¹ • (succCoordinates n x).1)‖ =
      ‖(succCoordinates n x).1‖ / r := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    ring
  have hsum : (‖(succCoordinates n x).1‖ / r) ^ 2 +
      (Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) / r) ^ 2 = 1 := by
    field_simp [hr0]
    nlinarith [Real.sq_sqrt harg]
  have hsq := norm_sq_succCoordinates n (graphDirection n r x)
  rw [succCoordinates_graphDirection] at hsq
  rw [hnorm] at hsq
  have hnonneg : 0 ≤ ‖graphDirection n r x‖ := norm_nonneg _
  nlinarith

/-- If the horizontal graph radius is at most half the sphere radius, the
graph direction is in the fixed upper hemisphere. -/
theorem graphDirection_snd_ge_half (n : ℕ) {r ρ : ℝ}
    (hr : 0 < r) (hρ : 2 * ρ ≤ r) {x : Euclidean (n + 1)}
    (hx : ‖(succCoordinates n x).1‖ ≤ ρ) :
    1 / 2 ≤ (succCoordinates n (graphDirection n r x)).2 := by
  rw [succCoordinates_graphDirection]
  change 1 / 2 ≤ Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) / r
  rw [le_div_iff₀ hr]
  have hρnonneg : 0 ≤ ρ := by
    exact (norm_nonneg _).trans hx
  have hρr : ρ ≤ r := by linarith
  have hzsq : ‖(succCoordinates n x).1‖ ^ 2 ≤ ρ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hρnonneg).mpr hx
  have hρsq : ρ ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ hρnonneg hr.le).mpr hρr
  have hradic : 0 ≤ r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2 := by
    linarith
  have hsqrt : Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) ^ 2 =
      r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2 := Real.sq_sqrt hradic
  have hhalf_nonneg : 0 ≤ r / 2 := by linarith
  have hhalf_sq : (r / 2) ^ 2 ≤ r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2 := by
    have hρhalf : ρ ≤ r / 2 := by linarith
    have hzhalf_sq : ‖(succCoordinates n x).1‖ ^ 2 ≤ (r / 2) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hhalf_nonneg).mpr (hx.trans hρhalf)
    nlinarith
  have hroot_nonneg : 0 ≤ Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) :=
    Real.sqrt_nonneg _
  have hsqle : (r / 2) ^ 2 ≤
      Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) ^ 2 := by
    rw [hsqrt]
    exact hhalf_sq
  have hle := sq_le_sq.mp hsqle
  have hle' : r / 2 ≤ Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) := by
    simpa only [abs_of_nonneg hhalf_nonneg, abs_of_nonneg hroot_nonneg] using hle
  nlinarith [hle']

/-- Translating by the central direction kills the horizontal coordinate and
lands exactly at the vertical-axis point associated to the lower graph. -/
theorem succCoordinates_translate_graphDirection (n : ℕ) {r : ℝ}
    (x : Euclidean (n + 1)) (hr : 0 < r) :
    succCoordinates n (x + r • graphDirection n r x) =
      (0, (succCoordinates n x).2 +
        Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2)) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [succCoordinates_add, succCoordinates_smul,
    succCoordinates_graphDirection]
  apply Prod.ext
  · change (succCoordinates n x).1 +
        r • (-(r⁻¹ • (succCoordinates n x).1)) = 0
    rw [smul_neg, smul_smul]
    rw [mul_inv_cancel₀ hr0]
    simp
  · change (succCoordinates n x).2 +
        r * (Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) / r) =
      (succCoordinates n x).2 +
        Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2)
    field_simp [hr0]

/-- Moving the radius outwards moves the lower spherical graph down by at
least the change in radius, as long as the horizontal coordinate stays inside
the smaller ball. -/
theorem sqrt_radius_gap_lower {u r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hu : 0 ≤ u) (hur : u ≤ r ^ 2) :
    s - r ≤ Real.sqrt (s ^ 2 - u) - Real.sqrt (r ^ 2 - u) := by
  have hc : 0 ≤ s - r := sub_nonneg.mpr hrs
  have hs : 0 ≤ s := hr.trans hrs
  have hru : 0 ≤ r ^ 2 - u := sub_nonneg.mpr hur
  have hsu : 0 ≤ s ^ 2 - u := by nlinarith
  have hA : 0 ≤ Real.sqrt (r ^ 2 - u) := Real.sqrt_nonneg _
  have hB : 0 ≤ Real.sqrt (s ^ 2 - u) := Real.sqrt_nonneg _
  have hA2 : Real.sqrt (r ^ 2 - u) ^ 2 = r ^ 2 - u := Real.sq_sqrt hru
  have hB2 : Real.sqrt (s ^ 2 - u) ^ 2 = s ^ 2 - u := Real.sq_sqrt hsu
  have hAr : Real.sqrt (r ^ 2 - u) ≤ r := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hr
    · nlinarith
  have hmul : Real.sqrt (r ^ 2 - u) * (s - r) ≤ r * (s - r) :=
    mul_le_mul_of_nonneg_right hAr hc
  have hsq : (Real.sqrt (r ^ 2 - u) + (s - r)) ^ 2 ≤
      Real.sqrt (s ^ 2 - u) ^ 2 := by
    nlinarith
  have hsum : 0 ≤ Real.sqrt (r ^ 2 - u) + (s - r) := add_nonneg hA hc
  have hle := sq_le_sq.mp hsq
  have hsumle : Real.sqrt (r ^ 2 - u) + (s - r) ≤ Real.sqrt (s ^ 2 - u) := by
    simpa only [abs_of_nonneg hsum, abs_of_nonneg hB] using hle
  linarith

theorem graphHeight_radius_gap_lower (n : ℕ) {r s a : ℝ} {z : Euclidean n}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hz : ‖z‖ ≤ r) :
    s - r ≤ graphHeight r a z - graphHeight s a z := by
  have hu : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  have hur : ‖z‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg z]
  have h := sqrt_radius_gap_lower hr hrs hu hur
  unfold graphHeight
  nlinarith

/-- A thickness-`b` graph tube over the horizontal ball of radius `ρ`. -/
def graphTube (n : ℕ) (r a ρ b : ℝ) : Set (Euclidean (n + 1)) :=
  succCoordinates n ⁻¹'
    (verticalShear n (graphHeight (n := n) r a) ''
      (ball (0 : Euclidean n) ρ ×ˢ Ioo (-b) b))

/-- Membership in a graph tube is the expected horizontal-radius and
vertical-distance condition. -/
theorem mem_graphTube_iff (n : ℕ) (r a ρ b : ℝ) (x : Euclidean (n + 1)) :
    x ∈ graphTube n r a ρ b ↔
      ‖(succCoordinates n x).1‖ < ρ ∧
        |(succCoordinates n x).2 -
          graphHeight (n := n) r a (succCoordinates n x).1| < b := by
  let φ : Euclidean n → ℝ := graphHeight (n := n) r a
  constructor
  · rintro ⟨z, hz, heq⟩
    rcases z with ⟨u, t⟩
    change (u, t) ∈ ball (0 : Euclidean n) ρ ×ˢ Ioo (-b) b at hz
    change verticalShear n φ (u, t) = succCoordinates n x at heq
    rcases hz with ⟨hu, ht⟩
    have hfst : u = (succCoordinates n x).1 := by
      exact congrArg Prod.fst heq
    have hsnd : t + φ u = (succCoordinates n x).2 := by
      exact congrArg Prod.snd heq
    constructor
    · simpa only [Metric.mem_ball, dist_zero_right, hfst] using hu
    · rw [← hfst]
      rw [← hsnd]
      change |t + φ u - φ u| < b
      rw [mem_Ioo] at ht
      simpa only [add_sub_cancel_right, abs_lt] using ht
  · rintro ⟨hhor, hvert⟩
    let u : Euclidean n := (succCoordinates n x).1
    let t : ℝ := (succCoordinates n x).2 - φ u
    refine ⟨(u, t), ?_, ?_⟩
    · constructor
      · change u ∈ ball (0 : Euclidean n) ρ
        simpa only [u, Metric.mem_ball, dist_zero_right] using hhor
      · change t ∈ Ioo (-b) b
        rw [mem_Ioo, ← abs_lt]
        simpa only [t, u] using hvert
    · change verticalShear n φ (u, t) = succCoordinates n x
      ext <;> simp only [verticalShear, u, t, sub_add_cancel]

/-- The explicit graph tube lies near the origin whenever its axial mismatch,
horizontal radius, and thickness do. -/
theorem graphTube_subset_ball
    (n : ℕ) {r a ρ b R : ℝ} (hr : 0 ≤ r) (hρr : ρ ≤ r)
    (hR : |a - r| + 2 * ρ + b ≤ R) :
    graphTube n r a ρ b ⊆ ball (0 : Euclidean (n + 1)) R := by
  intro x hx
  rcases (mem_graphTube_iff n r a ρ b x).1 hx with ⟨hhor, hvert⟩
  let z : Euclidean n := (succCoordinates n x).1
  let t : ℝ := (succCoordinates n x).2
  have hzle : ‖z‖ ≤ ρ := le_of_lt (by simpa only [z] using hhor)
  have hheight : |graphHeight r a z| ≤ |a - r| + ρ :=
    graphHeight_abs_le_abs_sub_add_horizontal n hr hρr hzle
  have htbound : |t| < b + |graphHeight r a z| := by
    calc
      |t| = |(t - graphHeight r a z) + graphHeight r a z| := by
        congr 1
        ring
      _ ≤ |t - graphHeight r a z| + |graphHeight r a z| := abs_add_le _ _
      _ < b + |graphHeight r a z| := by
        have hv : |t - graphHeight r a z| < b := by
          simpa only [t, z] using hvert
        linarith
  rw [Metric.mem_ball, dist_zero_right]
  calc
    ‖x‖ ≤ ‖z‖ + |t| := by simpa only [z, t] using norm_le_succCoordinates n x
    _ < ρ + (b + |graphHeight r a z|) :=
      add_lt_add (by simpa only [z] using hhor) htbound
    _ ≤ ρ + (b + (|a - r| + ρ)) := by gcongr
    _ = |a - r| + 2 * ρ + b := by ring
    _ ≤ R := hR

/-- Every cap centred at the graph direction translates into the prescribed
horizontal slab.  The parameters record exactly the elementary margins: a
cap of chordal radius `h` moves coordinates by at most `r * h`. -/
theorem graphTube_cap_translate_subset_horizontalSlab (n : ℕ)
    {r a ρ b h A B : ℝ} (hr : 0 < r) (hA : r * h < A)
    (hB : b + r * h ≤ B) {x : Euclidean (n + 1)}
    (hx : x ∈ graphTube n r a ρ b)
    {w : sphere (0 : Euclidean (n + 1)) 1}
    (hw : w ∈ sphericalCap n (graphDirection n r x) h) :
    x + r • (w : Euclidean (n + 1)) ∈ horizontalSlab n A (a - B) (a + B) := by
  rcases (mem_graphTube_iff n r a ρ b x).1 hx with ⟨hhor, hvert⟩
  let δ : Euclidean (n + 1) := (w : Euclidean (n + 1)) - graphDirection n r x
  have hδnorm : ‖δ‖ < h := by
    change dist (w : Euclidean (n + 1)) (graphDirection n r x) < h at hw
    simpa only [δ, dist_eq_norm] using hw
  have hδfst : ‖(succCoordinates n δ).1‖ < h :=
    (norm_fst_succCoordinates_le_norm n δ).trans_lt hδnorm
  have hδsnd : |(succCoordinates n δ).2| < h :=
    (abs_snd_succCoordinates_le_norm n δ).trans_lt hδnorm
  have hsplit : x + r • (w : Euclidean (n + 1)) =
      (x + r • graphDirection n r x) + r • δ := by
    dsimp only [δ]
    module
  have hcoord : succCoordinates n (x + r • (w : Euclidean (n + 1))) =
      (r • (succCoordinates n δ).1,
        (succCoordinates n x).2 +
          Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) +
            r * (succCoordinates n δ).2) := by
    rw [hsplit, succCoordinates_add, succCoordinates_smul,
      succCoordinates_translate_graphDirection n x hr]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst]
      simp
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rw [horizontalSlab]
  change succCoordinates n (x + r • (w : Euclidean (n + 1))) ∈
    ball (0 : Euclidean n) A ×ˢ Ioo (a - B) (a + B)
  rw [hcoord]
  constructor
  · change dist (r • (succCoordinates n δ).1) 0 < A
    rw [dist_zero_right]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left hδfst hr).trans hA
  · have hcentral :
        |(succCoordinates n x).2 +
            Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) - a| < b := by
      have heq :
          (succCoordinates n x).2 +
              Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) - a =
            (succCoordinates n x).2 -
              graphHeight r a (succCoordinates n x).1 := by
        unfold graphHeight
        ring
      rw [heq]
      exact hvert
    have hpert : |r * (succCoordinates n δ).2| < r * h := by
      rw [abs_mul, abs_of_pos hr]
      exact mul_lt_mul_of_pos_left hδsnd hr
    have htotal :
        |((succCoordinates n x).2 +
            Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) - a) +
          r * (succCoordinates n δ).2| < B := by
      calc
        |((succCoordinates n x).2 +
            Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) - a) +
          r * (succCoordinates n δ).2| ≤
            |(succCoordinates n x).2 +
              Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) - a| +
              |r * (succCoordinates n δ).2| := abs_add_le _ _
        _ < b + r * h := add_lt_add hcentral hpert
        _ ≤ B := hB
    rcases abs_lt.mp htotal with ⟨hlow, hupp⟩
    constructor <;> linarith

/-- The sharp version of the cap incidence.  On the upper hemisphere the
last-coordinate variation is `O (ρ h + r h²)`, rather than the coarse
`O (r h)`.  This is the curvature gain needed in the dyadic lower test. -/
theorem graphTube_sharpCap_translate_subset_horizontalSlab (n : ℕ)
    {r a ρ b h A B : ℝ} (hr : 0 < r) (hρr : ρ ≤ r) (hhemisphere : 2 * ρ ≤ r)
    (hh : 0 ≤ h) (hquarter : h ≤ 1 / 4) (hA : r * h < A)
    (hB : b + 4 * (ρ * h + r * h ^ 2) ≤ B) {x : Euclidean (n + 1)}
    (hx : x ∈ graphTube n r a ρ b)
    {w : sphere (0 : Euclidean (n + 1)) 1}
    (hw : w ∈ sphericalCap n (graphDirection n r x) h) :
    x + r • (w : Euclidean (n + 1)) ∈ horizontalSlab n A (a - B) (a + B) := by
  rcases (mem_graphTube_iff n r a ρ b x).1 hx with ⟨hhor, hvert⟩
  let δ : Euclidean (n + 1) := (w : Euclidean (n + 1)) - graphDirection n r x
  have hδnorm : ‖δ‖ < h := by
    change dist (w : Euclidean (n + 1)) (graphDirection n r x) < h at hw
    simpa only [δ, dist_eq_norm] using hw
  have hδfst : ‖(succCoordinates n δ).1‖ < h :=
    (norm_fst_succCoordinates_le_norm n δ).trans_lt hδnorm
  have hdir : ‖graphDirection n r x‖ = 1 := by
    apply norm_graphDirection n x hr
    exact (le_of_lt hhor).trans hρr
  have hwunit : ‖(w : Euclidean (n + 1))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp w.property
  have hlast : 1 / 2 ≤ (succCoordinates n (graphDirection n r x)).2 := by
    apply graphDirection_snd_ge_half n hr hhemisphere
    exact le_of_lt hhor
  have hδsnd : |(succCoordinates n δ).2| ≤
      4 * (‖(succCoordinates n (graphDirection n r x)).1‖ * h + h ^ 2) := by
    have hdist : dist (w : Euclidean (n + 1)) (graphDirection n r x) ≤ h := by
      simpa only [δ, dist_eq_norm] using le_of_lt hδnorm
    have h := abs_snd_sub_le_horizontal_mul_of_unit_vectors n hwunit hdir
      hh hquarter hlast hdist
    simpa only [δ, succCoordinates_sub, Prod.snd_sub] using h
  have hdirfst : r * ‖(succCoordinates n (graphDirection n r x)).1‖ ≤ ρ := by
    rw [succCoordinates_graphDirection]
    change r * ‖-(r⁻¹ • (succCoordinates n x).1)‖ ≤ ρ
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    calc
      r * (r⁻¹ * ‖(succCoordinates n x).1‖) =
          (r * r⁻¹) * ‖(succCoordinates n x).1‖ := by ring
      _ = ‖(succCoordinates n x).1‖ := by
        simp only [mul_inv_cancel₀ (ne_of_gt hr), one_mul]
      _ ≤ ρ := le_of_lt hhor
  have hdirterm :
      (r * ‖(succCoordinates n (graphDirection n r x)).1‖) * h ≤ ρ * h :=
    mul_le_mul_of_nonneg_right hdirfst hh
  have hscaled : r *
      (4 * (‖(succCoordinates n (graphDirection n r x)).1‖ * h + h ^ 2)) ≤
      4 * (ρ * h + r * h ^ 2) := by
    calc
      r * (4 * (‖(succCoordinates n (graphDirection n r x)).1‖ * h + h ^ 2)) =
          4 * ((r * ‖(succCoordinates n (graphDirection n r x)).1‖) * h +
            r * h ^ 2) := by ring
      _ ≤ 4 * (ρ * h + r * h ^ 2) := by
        gcongr
  have hsplit : x + r • (w : Euclidean (n + 1)) =
      (x + r • graphDirection n r x) + r • δ := by
    dsimp only [δ]
    module
  have hcoord : succCoordinates n (x + r • (w : Euclidean (n + 1))) =
      (r • (succCoordinates n δ).1,
        (succCoordinates n x).2 +
          Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) +
            r * (succCoordinates n δ).2) := by
    rw [hsplit, succCoordinates_add, succCoordinates_smul,
      succCoordinates_translate_graphDirection n x hr]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst]
      simp
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rw [horizontalSlab]
  change succCoordinates n (x + r • (w : Euclidean (n + 1))) ∈
    ball (0 : Euclidean n) A ×ˢ Ioo (a - B) (a + B)
  rw [hcoord]
  constructor
  · change dist (r • (succCoordinates n δ).1) 0 < A
    rw [dist_zero_right]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left hδfst hr).trans hA
  · have hcentral :
        |(succCoordinates n x).2 +
            Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) - a| < b := by
      have heq :
          (succCoordinates n x).2 +
              Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) - a =
            (succCoordinates n x).2 -
              graphHeight r a (succCoordinates n x).1 := by
        unfold graphHeight
        ring
      rw [heq]
      exact hvert
    have hpert : |r * (succCoordinates n δ).2| ≤
        4 * (ρ * h + r * h ^ 2) := by
      rw [abs_mul, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left hδsnd hr.le).trans hscaled
    have htotal :
        |((succCoordinates n x).2 +
            Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) - a) +
          r * (succCoordinates n δ).2| < B := by
      calc
        |((succCoordinates n x).2 +
            Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) - a) +
          r * (succCoordinates n δ).2| ≤
            |(succCoordinates n x).2 +
              Real.sqrt (r ^ 2 - ‖(succCoordinates n x).1‖ ^ 2) - a| +
              |r * (succCoordinates n δ).2| := abs_add_le _ _
        _ < b + 4 * (ρ * h + r * h ^ 2) :=
          add_lt_add_of_lt_of_le hcentral hpert
        _ ≤ B := hB
    rcases abs_lt.mp htotal with ⟨hlow, hupp⟩
    constructor <;> linarith

/-- The cap lower bound with the curved vertical margin from
`graphTube_sharpCap_translate_subset_horizontalSlab`. -/
theorem graphTube_sharpCap_average_lower (n : ℕ) (hn : 2 ≤ n)
    {r a ρ b h A B : ℝ} (hr : 0 < r) (hρr : ρ ≤ r)
    (hhemisphere : 2 * ρ ≤ r) (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (hA : r * h < A) (hB : b + 4 * (ρ * h + r * h ^ 2) ≤ B)
    (g : Euclidean (n + 1) → ℝ) (hgContinuous : Continuous g)
    (hgnonneg : ∀ y, 0 ≤ g y)
    (hg_one : ∀ y ∈ horizontalSlab n A (a - B) (a + B), g y = 1)
    {x : Euclidean (n + 1)} (hx : x ∈ graphTube n r a ρ b) :
    (ENNReal.ofReal (surfaceMass n) *
        ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
        ENNReal.ofReal (surfaceMass (n + 1)) ≤
      ENNReal.ofReal ‖normalizedSphericalAverage (n + 1)
        (fun y => (g y : ℂ)) r x‖ := by
  rcases (mem_graphTube_iff n r a ρ b x).1 hx with ⟨hhor, _⟩
  have hdir : ‖graphDirection n r x‖ = 1 := by
    apply norm_graphDirection n x hr
    exact le_trans (le_of_lt hhor) hρr
  have hgi : Integrable (fun w : sphere (0 : Euclidean (n + 1)) 1 =>
      g (x + r • (w : Euclidean (n + 1))))
      (unitSurfaceMeasure (n + 1)) := by
    have hcont : Continuous (fun w : sphere (0 : Euclidean (n + 1)) 1 =>
        g (x + r • (w : Euclidean (n + 1)))) := by
      apply hgContinuous.comp
      fun_prop
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hhone : h ≤ 1 := hquarter.trans (by norm_num)
  apply poleCap_lower_le_ennreal_norm_normalizedSphericalAverage
    hn g r x hdir hh hhone hgi
  · intro w
    exact hgnonneg _
  · intro w hw
    apply hg_one
    exact graphTube_sharpCap_translate_subset_horizontalSlab n hr hρr hhemisphere
      hh.le hquarter hA hB hx hw

/-- The concrete cap incidence yields the quantitative cap contribution to a
normalized spherical average of a slab cutoff. -/
theorem graphTube_cap_average_lower (n : ℕ) (hn : 2 ≤ n)
    {r a ρ b h A B : ℝ} (hr : 0 < r) (hρr : ρ ≤ r)
    (hh : 0 < h) (hhone : h ≤ 1) (hA : r * h < A)
    (hB : b + r * h ≤ B)
    (g : Euclidean (n + 1) → ℝ) (hgContinuous : Continuous g)
    (hgnonneg : ∀ y, 0 ≤ g y)
    (hg_one : ∀ y ∈ horizontalSlab n A (a - B) (a + B), g y = 1)
    {x : Euclidean (n + 1)} (hx : x ∈ graphTube n r a ρ b) :
    (ENNReal.ofReal (surfaceMass n) *
        ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
        ENNReal.ofReal (surfaceMass (n + 1)) ≤
      ENNReal.ofReal ‖normalizedSphericalAverage (n + 1)
        (fun y => (g y : ℂ)) r x‖ := by
  rcases (mem_graphTube_iff n r a ρ b x).1 hx with ⟨hhor, _⟩
  have hdir : ‖graphDirection n r x‖ = 1 := by
    apply norm_graphDirection n x hr
    exact le_trans (le_of_lt hhor) hρr
  have hgi : Integrable (fun w : sphere (0 : Euclidean (n + 1)) 1 =>
      g (x + r • (w : Euclidean (n + 1))))
      (unitSurfaceMeasure (n + 1)) := by
    have hcont : Continuous (fun w : sphere (0 : Euclidean (n + 1)) 1 =>
        g (x + r • (w : Euclidean (n + 1)))) := by
      apply hgContinuous.comp
      fun_prop
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply poleCap_lower_le_ennreal_norm_normalizedSphericalAverage
    hn g r x hdir hh hhone hgi
  · intro w
    exact hgnonneg _
  · intro w hw
    apply hg_one
    exact graphTube_cap_translate_subset_horizontalSlab n hr hA hB hx hw

/-- Tubes above the same horizontal ball are disjoint once their radii are
separated by twice their vertical thickness.  This is the concrete geometric
input used for the finite-radius lower test. -/
theorem disjoint_graphTube_of_radius_separated (n : ℕ) {r s a ρ b : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hρr : ρ ≤ r) (hsep : 2 * b ≤ s - r) :
    Disjoint (graphTube n r a ρ b) (graphTube n s a ρ b) := by
  rw [Set.disjoint_left]
  intro x hxr hxs
  rcases (mem_graphTube_iff n r a ρ b x).1 hxr with ⟨hhor, hvr⟩
  rcases (mem_graphTube_iff n s a ρ b x).1 hxs with ⟨_, hvs⟩
  let z : Euclidean n := (succCoordinates n x).1
  let t : ℝ := (succCoordinates n x).2
  have hzr : ‖z‖ ≤ r := by
    exact le_trans (le_of_lt (by simpa only [z] using hhor)) hρr
  have hgap : 2 * b ≤ graphHeight r a z - graphHeight s a z :=
    hsep.trans (graphHeight_radius_gap_lower n hr hrs hzr)
  have hclose : |graphHeight r a z - graphHeight s a z| < 2 * b := by
    calc
      |graphHeight r a z - graphHeight s a z| =
          |(graphHeight r a z - t) + (t - graphHeight s a z)| := by ring_nf
      _ ≤ |graphHeight r a z - t| + |t - graphHeight s a z| := abs_add_le _ _
      _ = |t - graphHeight r a z| + |t - graphHeight s a z| := by
        rw [abs_sub_comm]
      _ < b + b := by
        exact add_lt_add
          (by simpa only [t, z] using hvr)
          (by simpa only [t, z] using hvs)
      _ = 2 * b := by ring
  exact (not_lt_of_ge (hgap.trans (le_abs_self _))) hclose

theorem measurableSet_graphTube (n : ℕ) (r a ρ b : ℝ) :
    MeasurableSet (graphTube n r a ρ b) := by
  let φ : Euclidean n → ℝ := graphHeight (n := n) r a
  let S : Set (Euclidean n × ℝ) := ball (0 : Euclidean n) ρ ×ˢ Ioo (-b) b
  let e := verticalShearEquiv n φ (measurable_graphHeight (n := n) r a)
  have hS : MeasurableSet S := measurableSet_ball.prod measurableSet_Ioo
  have himage : MeasurableSet (verticalShear n φ '' S) := by
    change MeasurableSet (e '' S)
    exact e.measurableEmbedding.measurableSet_image' hS
  change MeasurableSet ((succCoordinates n) ⁻¹' (verticalShear n φ '' S))
  exact himage.preimage (measurable_succCoordinates n)

/-- Exact volume of a graph tube.  The vertical shear preserves product
Lebesgue measure, leaving only the horizontal ball and interval factors. -/
theorem volume_graphTube (n : ℕ) (r a ρ b : ℝ) :
    volume (graphTube n r a ρ b) =
      volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b) := by
  let φ : Euclidean n → ℝ := graphHeight (n := n) r a
  let S : Set (Euclidean n × ℝ) := ball (0 : Euclidean n) ρ ×ˢ Ioo (-b) b
  let e := verticalShearEquiv n φ (measurable_graphHeight (n := n) r a)
  have hφ : Measurable φ := measurable_graphHeight (n := n) r a
  have hS : MeasurableSet S := measurableSet_ball.prod measurableSet_Ioo
  have himage : MeasurableSet (verticalShear n φ '' S) := by
    change MeasurableSet (e '' S)
    exact e.measurableEmbedding.measurableSet_image' hS
  have hcoord : Measure.map (succCoordinates n) volume =
      ((volume : Measure (Euclidean n)).prod volume) := by
    have h := map_euclideanSucc_coordinates_volume n
    change Measure.map (succCoordinates n) volume =
      ((volume : Measure (Euclidean n)).prod volume) at h
    exact h
  have hshear := measurePreserving_verticalShear n φ hφ
  calc
    volume (graphTube n r a ρ b) =
        Measure.map (succCoordinates n) volume (verticalShear n φ '' S) := by
      change volume ((succCoordinates n) ⁻¹' (verticalShear n φ '' S)) = _
      exact (Measure.map_apply (measurable_succCoordinates n) himage).symm
    _ = ((volume : Measure (Euclidean n)).prod volume)
        (verticalShear n φ '' S) := by rw [hcoord]
    _ = Measure.map (verticalShear n φ)
        ((volume : Measure (Euclidean n)).prod volume) (verticalShear n φ '' S) := by
      rw [hshear.map_eq]
    _ = ((volume : Measure (Euclidean n)).prod volume)
        ((verticalShear n φ) ⁻¹' (verticalShear n φ '' S)) :=
      Measure.map_apply (verticalShearEquiv n φ hφ).measurable himage
    _ = ((volume : Measure (Euclidean n)).prod volume) S := by
      apply congrArg
      have heq : (verticalShearEquiv n φ hφ :
          Euclidean n × ℝ → Euclidean n × ℝ) = verticalShear n φ := rfl
      rw [← heq]
      exact (verticalShearEquiv n φ hφ).preimage_image S
    _ = volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b) := by
      dsimp only [S]
      rw [Measure.prod_prod, Real.volume_Ioo]
      congr 2
      ring

/-- The near-origin weighted volume of an actual graph tube.  Its only
geometric input is the displayed ball containment, proved above from the
same `a-r`, horizontal, and thickness scales used in the construction. -/
theorem powerWeightedVolume_graphTube_lower_of_near_origin
    (n : ℕ) {α r a ρ b R : ℝ}
    (hα : α < 0) (hr : 0 ≤ r) (hρr : ρ ≤ r)
    (hRpos : 0 < R) (hR : |a - r| + 2 * ρ + b ≤ R) :
    (ENNReal.ofReal R) ^ α *
        (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b)) ≤
      powerWeightedVolume (n + 1) α (graphTube n r a ρ b) := by
  calc
    (ENNReal.ofReal R) ^ α *
        (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b)) =
        (ENNReal.ofReal R) ^ α * volume (graphTube n r a ρ b) := by
      rw [volume_graphTube]
    _ ≤ powerWeightedVolume (n + 1) α (graphTube n r a ρ b) :=
      powerWeightedVolume_set_lower_of_subset_ball hα hRpos
        (measurableSet_graphTube n r a ρ b)
        (graphTube_subset_ball n hr hρr hR)

/-- The literal finite-radius lower test in the first half of Lemma 4.1.

The radii in `T` are separated at the physical thickness `2 * b`, and the
output set is exactly the union of the graph tubes used above.  Thus no
abstract packing object intervenes between the cap computation and the
strong-type estimate.  The parameter `m` is the common weighted lower bound
for these *particular* graph tubes; the later near-origin calculation supplies
it with the dyadic value used in the theorem. -/
theorem restrictedStrongType_graphTube_finite_lower_of_bound
    (n : ℕ) (hn : 2 ≤ n) {E : Set ℝ} {p α C : ℝ}
    (hstrong : ∀ f : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume (n + 1) α) →
        MemLp (restrictedNormalizedSphericalMaximal (n + 1) E
          (f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume (n + 1) α) ∧
        eLpNorm (restrictedNormalizedSphericalMaximal (n + 1) E
          (f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume (n + 1) α) ≤
          ENNReal.ofReal C * eLpNorm (f : Euclidean (n + 1) → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume (n + 1) α))
    (T : Finset PositiveRadius) {a ρ b h A B : ℝ} {m : ℝ≥0∞}
    (hT : ∀ r ∈ T, (r : ℝ) ∈ E)
    (hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → 2 * b ≤ |(r : ℝ) - (s : ℝ)|)
    (hρ : ∀ r ∈ T, ρ ≤ (r : ℝ))
    (hhemisphere : ∀ r ∈ T, 2 * ρ ≤ (r : ℝ))
    (hm : ∀ r ∈ T, m ≤ powerWeightedVolume (n + 1) α
      (graphTube n (r : ℝ) a ρ b))
    (hppos : 0 < p) (hApos : 0 < A) (hBpos : 0 < B)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (hcapHorizontal : ∀ r ∈ T, (r : ℝ) * h < A)
    (hcapVertical : ∀ r ∈ T,
      b + 4 * (ρ * h + (r : ℝ) * h ^ 2) ≤ B)
    (hDfinite : powerWeightedVolume (n + 1) α
      (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B)) ≠ (∞ : ℝ≥0∞)) :
    ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((T.card : ℝ≥0∞) * m) ^ (1 / (ENNReal.ofReal p).toReal) ≤
        ENNReal.ofReal C *
          (powerWeightedVolume (n + 1) α
            (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B))) ^
              (1 / (ENNReal.ofReal p).toReal) := by
  classical
  let D : Set (Euclidean (n + 1)) :=
    horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B)
  let U : PositiveRadius → Set (Euclidean (n + 1)) :=
    fun r => graphTube n (r : ℝ) a ρ b
  let V : Set (Euclidean (n + 1)) := ⋃ r ∈ (↑T : Set PositiveRadius), U r
  rcases exists_schwartz_horizontalSlab_cutoff n hApos hBpos with
    ⟨g, f, hfg, hgcont, hgnonneg, hgleone, hgone, hzeroH, hzeroV, hsupport⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hppos)
  have hinput : eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume (n + 1) α) ≤
      (powerWeightedVolume (n + 1) α D) ^
        (1 / (ENNReal.ofReal p).toReal) := by
    dsimp only [D]
    exact eLpNorm_horizontalSlab_cutoff_le n hp0 g f hfg hgnonneg hgleone hsupport
  have hq : 0 ≤ 1 / (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hppos.le]
    positivity
  have hf : MemLp (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p)
      (powerWeightedVolume (n + 1) α) := by
    refine ⟨f.continuous.aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt hinput ?_
    exact ENNReal.rpow_lt_top_of_nonneg hq (by simpa only [D] using hDfinite)
  have hUmeas : ∀ r ∈ T, MeasurableSet (U r) := by
    intro r hr
    exact measurableSet_graphTube n (r : ℝ) a ρ b
  have hUdisjoint : (↑T : Set PositiveRadius).PairwiseDisjoint U := by
    intro r hr s hs hrs
    change Disjoint (U r) (U s)
    rcases le_total (r : ℝ) (s : ℝ) with hrsle | hsrle
    · apply disjoint_graphTube_of_radius_separated n r.2.le hrsle
        (hρ r (by simpa using hr))
      have hsep' := hsep r (by simpa using hr) s (by simpa using hs) hrs
      simpa [abs_of_nonpos (sub_nonpos.mpr hrsle), neg_sub] using hsep'
    · rw [disjoint_comm]
      apply disjoint_graphTube_of_radius_separated n s.2.le hsrle
        (hρ s (by simpa using hs))
      have hneq : s ≠ r := Ne.symm hrs
      have hsep' := hsep s (by simpa using hs) r (by simpa using hr) hneq
      simpa [abs_of_nonpos (sub_nonpos.mpr hsrle), neg_sub] using hsep'
  have hVmeas : MeasurableSet V := by
    dsimp only [V]
    exact T.measurableSet_biUnion hUmeas
  have hpoint : ∀ x ∈ V,
      (ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1)) ≤
        restrictedNormalizedSphericalMaximal (n + 1) E (f : Euclidean (n + 1) → ℂ) x := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨r, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hrT, hxr⟩
    calc
      (ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1)) ≤
          ENNReal.ofReal ‖normalizedSphericalAverage (n + 1)
            (fun y => (g y : ℂ)) (r : ℝ) x‖ :=
        graphTube_sharpCap_average_lower n hn r.2 (hρ r hrT) (hhemisphere r hrT)
          hh hquarter
          (hcapHorizontal r hrT) (hcapVertical r hrT) g hgcont hgnonneg hgone hxr
      _ = ENNReal.ofReal ‖normalizedSphericalAverage (n + 1)
          (f : Euclidean (n + 1) → ℂ) (r : ℝ) x‖ := by
        have hfun : (fun y : Euclidean (n + 1) => (g y : ℂ)) =
            (f : Euclidean (n + 1) → ℂ) := by
          funext y
          exact (hfg y).symm
        rw [hfun]
      _ ≤ restrictedNormalizedSphericalMaximal (n + 1) E
          (f : Euclidean (n + 1) → ℂ) x :=
        ennreal_norm_normalizedSphericalAverage_le_restrictedNormalizedSphericalMaximal
          f (hT r hrT) r.2 x
  have hvolume : (T.card : ℝ≥0∞) * m ≤ powerWeightedVolume (n + 1) α V := by
    calc
      (T.card : ℝ≥0∞) * m = ∑ r ∈ T, m := by simp [mul_comm]
      _ ≤ ∑ r ∈ T, powerWeightedVolume (n + 1) α (U r) := by
        gcongr with r hr
        exact hm r hr
      _ = powerWeightedVolume (n + 1) α V := by
        dsimp only [V]
        exact (measure_biUnion_finset hUdisjoint hUmeas).symm
  calc
    ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((T.card : ℝ≥0∞) * m) ^ (1 / (ENNReal.ofReal p).toReal) ≤
        ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        (powerWeightedVolume (n + 1) α V) ^
          (1 / (ENNReal.ofReal p).toReal) := by
      gcongr
    _ = eLpNorm (V.indicator (fun _ : Euclidean (n + 1) =>
        (ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))))
        (ENNReal.ofReal p) (powerWeightedVolume (n + 1) α) := by
      rw [eLpNorm_indicator_const hVmeas hp0 ENNReal.ofReal_ne_top]
      simp
    _ ≤ eLpNorm (restrictedNormalizedSphericalMaximal (n + 1) E
        (f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume (n + 1) α) := by
      apply eLpNorm_mono_enorm
      intro x
      by_cases hx : x ∈ V
      · rw [Set.indicator_of_mem hx]
        exact hpoint x hx
      · rw [Set.indicator_of_notMem hx]
        exact bot_le
    _ ≤ ENNReal.ofReal C * eLpNorm (f : Euclidean (n + 1) → ℂ)
        (ENNReal.ofReal p) (powerWeightedVolume (n + 1) α) := (hstrong f hf).2
    _ ≤ ENNReal.ofReal C *
        (powerWeightedVolume (n + 1) α D) ^
          (1 / (ENNReal.ofReal p).toReal) := by
      simpa only [mul_comm] using mul_le_mul_left hinput (ENNReal.ofReal C)
    _ = ENNReal.ofReal C *
        (powerWeightedVolume (n + 1) α
          (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B))) ^
            (1 / (ENNReal.ofReal p).toReal) := by rfl

/-- Existential-constant form of the finite graph-tube test. -/
theorem restrictedStrongType_graphTube_finite_lower
    (n : ℕ) (hn : 2 ≤ n) {E : Set ℝ} {p α : ℝ}
    (hstrong : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType
      (n + 1) E p α)
    (T : Finset PositiveRadius) {a ρ b h A B : ℝ} {m : ℝ≥0∞}
    (hT : ∀ r ∈ T, (r : ℝ) ∈ E)
    (hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → 2 * b ≤ |(r : ℝ) - (s : ℝ)|)
    (hρ : ∀ r ∈ T, ρ ≤ (r : ℝ))
    (hhemisphere : ∀ r ∈ T, 2 * ρ ≤ (r : ℝ))
    (hm : ∀ r ∈ T, m ≤ powerWeightedVolume (n + 1) α
      (graphTube n (r : ℝ) a ρ b))
    (hppos : 0 < p) (hApos : 0 < A) (hBpos : 0 < B)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (hcapHorizontal : ∀ r ∈ T, (r : ℝ) * h < A)
    (hcapVertical : ∀ r ∈ T,
      b + 4 * (ρ * h + (r : ℝ) * h ^ 2) ≤ B)
    (hDfinite : powerWeightedVolume (n + 1) α
      (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B)) ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧
      ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((T.card : ℝ≥0∞) * m) ^ (1 / (ENNReal.ofReal p).toReal) ≤
        ENNReal.ofReal C *
          (powerWeightedVolume (n + 1) α
            (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B))) ^
              (1 / (ENNReal.ofReal p).toReal) := by
  rcases hstrong with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  exact restrictedStrongType_graphTube_finite_lower_of_bound n hn hbound T
    hT hsep hρ hhemisphere hm hppos hApos hBpos hh hquarter
    hcapHorizontal hcapVertical hDfinite

/-- The graph-tube test with the radius family chosen as a maximal logarithmic
packing in one multiplicative interval.

The `δ / 2` in both the separation and net hypotheses is deliberate:
`multiplicativeEntropy ... δ` is defined using closed covering balls of radius
`δ / 2`.  Consequently the displayed net property gives the entropy bound at
the *same* scale `δ`, with no change of scale in the final lower test.  The
separate physical separation hypothesis is the calibrated form used by the
graph-tube disjointness calculation. -/
theorem restrictedStrongType_graphTube_localEntropy_lower_of_bound
    (n : ℕ) (hn : 2 ≤ n) {E : Set ℝ} {p α C : ℝ}
    (hstrong : ∀ f : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume (n + 1) α) →
        MemLp (restrictedNormalizedSphericalMaximal (n + 1) E
          (f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume (n + 1) α) ∧
        eLpNorm (restrictedNormalizedSphericalMaximal (n + 1) E
          (f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume (n + 1) α) ≤
          ENNReal.ofReal C * eLpNorm (f : Euclidean (n + 1) → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume (n + 1) α))
    (c : PositiveRadius) (diam δ : ℝ≥0) (T : Finset PositiveRadius)
    {a ρ b h A B : ℝ} {m : ℝ≥0∞}
    (hT : ∀ r ∈ T, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam)
    (_hlogsep : Metric.IsSeparated (((δ / 2 : ℝ≥0) : ℝ≥0∞))
      (logRadius '' (↑T : Set PositiveRadius)))
    (hnet : ∀ r : PositiveRadius, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam →
      ∃ t ∈ T, |logRadius r - logRadius t| ≤ ((δ : ℝ≥0) : ℝ) / 2)
    (hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → 2 * b ≤ |(r : ℝ) - (s : ℝ)|)
    (hρ : ∀ r ∈ T, ρ ≤ (r : ℝ))
    (hhemisphere : ∀ r ∈ T, 2 * ρ ≤ (r : ℝ))
    (hm : ∀ r ∈ T, m ≤ powerWeightedVolume (n + 1) α
      (graphTube n (r : ℝ) a ρ b))
    (hppos : 0 < p) (hApos : 0 < A) (hBpos : 0 < B)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (hcapHorizontal : ∀ r ∈ T, (r : ℝ) * h < A)
    (hcapVertical : ∀ r ∈ T,
      b + 4 * (ρ * h + (r : ℝ) * h ^ 2) ≤ B)
    (hDfinite : powerWeightedVolume (n + 1) α
      (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B)) ≠ (∞ : ℝ≥0∞)) :
    ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((localMultiplicativeEntropy E c diam δ).toENNReal * m) ^
          (1 / (ENNReal.ofReal p).toReal) ≤
        ENNReal.ofReal C *
          (powerWeightedVolume (n + 1) α
            (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B))) ^
              (1 / (ENNReal.ofReal p).toReal) := by
  classical
  let F : Set ℝ := E ∩ multiplicativeInterval c diam
  let centers : Set ℝ := logRadius '' (↑T : Set PositiveRadius)
  have hcover : Metric.IsCover (δ / 2) (logRadiusSet F) centers := by
    rintro u ⟨r, hrF, rfl⟩
    obtain ⟨t, htT, hrt⟩ := hnet r (by simpa only [F] using hrF)
    refine ⟨logRadius t, ⟨t, htT, rfl⟩, ?_⟩
    change edist (logRadius r) (logRadius t) ≤ ((δ / 2 : ℝ≥0) : ℝ≥0∞)
    rw [edist_dist]
    apply ENNReal.ofReal_le_coe.mpr
    simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_ofNat] using hrt
  have hCcard : centers.encard = T.card := by
    have hC : centers = (↑(T.image logRadius) : Set ℝ) := by
      ext u
      simp [centers]
    rw [hC, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective T logRadius_injective]
  have hentropyENat : localMultiplicativeEntropy E c diam δ ≤ T.card := by
    change Metric.externalCoveringNumber (δ / 2) (logRadiusSet F) ≤ T.card
    rw [← hCcard]
    exact hcover.externalCoveringNumber_le_encard
  have hentropy : (localMultiplicativeEntropy E c diam δ).toENNReal ≤
      (T.card : ℝ≥0∞) := by
    exact_mod_cast ENat.toENNReal_mono hentropyENat
  have hq : 0 ≤ 1 / (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hppos.le]
    positivity
  have hbound :=
    restrictedStrongType_graphTube_finite_lower_of_bound n hn hstrong T
      (fun r hr => (hT r hr).1) hsep hρ hhemisphere hm hppos hApos hBpos hh hquarter
      hcapHorizontal hcapVertical hDfinite
  calc
    ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((localMultiplicativeEntropy E c diam δ).toENNReal * m) ^
          (1 / (ENNReal.ofReal p).toReal) ≤
        ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((T.card : ℝ≥0∞) * m) ^ (1 / (ENNReal.ofReal p).toReal) := by
      gcongr
    _ ≤ ENNReal.ofReal C *
        (powerWeightedVolume (n + 1) α
          (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B))) ^
            (1 / (ENNReal.ofReal p).toReal) := hbound

/-- Existential-constant form of the local graph-tube entropy test. -/
theorem restrictedStrongType_graphTube_localEntropy_lower
    (n : ℕ) (hn : 2 ≤ n) {E : Set ℝ} {p α : ℝ}
    (hstrong : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType
      (n + 1) E p α)
    (c : PositiveRadius) (diam δ : ℝ≥0) (T : Finset PositiveRadius)
    {a ρ b h A B : ℝ} {m : ℝ≥0∞}
    (hT : ∀ r ∈ T, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam)
    (hlogsep : Metric.IsSeparated (((δ / 2 : ℝ≥0) : ℝ≥0∞))
      (logRadius '' (↑T : Set PositiveRadius)))
    (hnet : ∀ r : PositiveRadius, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam →
      ∃ t ∈ T, |logRadius r - logRadius t| ≤ ((δ : ℝ≥0) : ℝ) / 2)
    (hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → 2 * b ≤ |(r : ℝ) - (s : ℝ)|)
    (hρ : ∀ r ∈ T, ρ ≤ (r : ℝ))
    (hhemisphere : ∀ r ∈ T, 2 * ρ ≤ (r : ℝ))
    (hm : ∀ r ∈ T, m ≤ powerWeightedVolume (n + 1) α
      (graphTube n (r : ℝ) a ρ b))
    (hppos : 0 < p) (hApos : 0 < A) (hBpos : 0 < B)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (hcapHorizontal : ∀ r ∈ T, (r : ℝ) * h < A)
    (hcapVertical : ∀ r ∈ T,
      b + 4 * (ρ * h + (r : ℝ) * h ^ 2) ≤ B)
    (hDfinite : powerWeightedVolume (n + 1) α
      (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B)) ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧
      ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((localMultiplicativeEntropy E c diam δ).toENNReal * m) ^
          (1 / (ENNReal.ofReal p).toReal) ≤
        ENNReal.ofReal C *
          (powerWeightedVolume (n + 1) α
            (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B))) ^
              (1 / (ENNReal.ofReal p).toReal) := by
  rcases hstrong with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  exact restrictedStrongType_graphTube_localEntropy_lower_of_bound n hn hbound c diam δ T
    hT hlogsep hnet hsep hρ hhemisphere hm hppos hApos hBpos hh hquarter
    hcapHorizontal hcapVertical hDfinite

/-- The fully measured near-origin form of the finite graph-tube test.

Here the common tube volume and the cutoff input size are no longer abstract
premises: they are respectively the explicit near-origin lower bound and the
exact doubled-slab product-volume upper bound.  This is the form fed into the
dyadic exponents in Lemma 4.1. -/
theorem restrictedStrongType_graphTube_localEntropy_nearOrigin_lower_of_bound
    (n : ℕ) (hn : 2 ≤ n) {E : Set ℝ} {p α C : ℝ}
    (hstrong : ∀ f : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume (n + 1) α) →
        MemLp (restrictedNormalizedSphericalMaximal (n + 1) E
          (f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume (n + 1) α) ∧
        eLpNorm (restrictedNormalizedSphericalMaximal (n + 1) E
          (f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume (n + 1) α) ≤
          ENNReal.ofReal C * eLpNorm (f : Euclidean (n + 1) → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume (n + 1) α))
    (c : PositiveRadius) (diam δ : ℝ≥0) (T : Finset PositiveRadius)
    {a ρ b h A B R : ℝ}
    (hT : ∀ r ∈ T, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam)
    (_hlogsep : Metric.IsSeparated (((δ / 2 : ℝ≥0) : ℝ≥0∞))
      (logRadius '' (↑T : Set PositiveRadius)))
    (hnet : ∀ r : PositiveRadius, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam →
      ∃ t ∈ T, |logRadius r - logRadius t| ≤ ((δ : ℝ≥0) : ℝ) / 2)
    (hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → 2 * b ≤ |(r : ℝ) - (s : ℝ)|)
    (hρ : ∀ r ∈ T, ρ ≤ (r : ℝ))
    (hhemisphere : ∀ r ∈ T, 2 * ρ ≤ (r : ℝ))
    (hppos : 0 < p) (hα : α < 0)
    (hApos : 0 < A) (hBpos : 0 < B)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (hcapHorizontal : ∀ r ∈ T, (r : ℝ) * h < A)
    (hcapVertical : ∀ r ∈ T,
      b + 4 * (ρ * h + (r : ℝ) * h ^ 2) ≤ B)
    (hinputAway : 0 < a - 2 * B)
    (hRpos : 0 < R)
    (hnear : ∀ r ∈ T, |a - (r : ℝ)| + 2 * ρ + b ≤ R) :
    ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((localMultiplicativeEntropy E c diam δ).toENNReal *
          ((ENNReal.ofReal R) ^ α *
            (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b)))) ^
          (1 / (ENNReal.ofReal p).toReal) ≤
        ENNReal.ofReal C *
          ((ENNReal.ofReal (a - 2 * B)) ^ α *
            (volume (ball (0 : Euclidean n) (2 * A)) *
              ENNReal.ofReal (2 * (2 * B)))) ^
            (1 / (ENNReal.ofReal p).toReal) := by
  let m : ℝ≥0∞ := (ENNReal.ofReal R) ^ α *
    (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b))
  have hm : ∀ r ∈ T, m ≤ powerWeightedVolume (n + 1) α
      (graphTube n (r : ℝ) a ρ b) := by
    intro r hr
    exact powerWeightedVolume_graphTube_lower_of_near_origin n hα r.2.le
      (hρ r hr) hRpos (hnear r hr)
  have hDfinite : powerWeightedVolume (n + 1) α
      (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B)) ≠ (∞ : ℝ≥0∞) := by
    exact ne_of_lt
      (powerWeightedVolume_horizontalSlab_lt_top_of_nonpos
        (A := 2 * A) (B := 2 * B) (a := a) n hα.le hinputAway)
  have hDupper : powerWeightedVolume (n + 1) α
      (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B)) ≤
      (ENNReal.ofReal (a - 2 * B)) ^ α *
        (volume (ball (0 : Euclidean n) (2 * A)) *
          ENNReal.ofReal (2 * (2 * B))) := by
    exact powerWeightedVolume_horizontalSlab_le_of_nonpos
      (A := 2 * A) (B := 2 * B) (a := a) n hα.le hinputAway
  have hbound :=
    restrictedStrongType_graphTube_localEntropy_lower_of_bound n hn hstrong c diam δ T
      hT _hlogsep hnet hsep hρ hhemisphere hm hppos hApos hBpos hh hquarter
      hcapHorizontal hcapVertical hDfinite
  have hq : 0 ≤ 1 / (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hppos.le]
    positivity
  calc
    ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((localMultiplicativeEntropy E c diam δ).toENNReal *
          ((ENNReal.ofReal R) ^ α *
            (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b)))) ^
          (1 / (ENNReal.ofReal p).toReal) =
        ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((localMultiplicativeEntropy E c diam δ).toENNReal * m) ^
          (1 / (ENNReal.ofReal p).toReal) := by rfl
    _ ≤ ENNReal.ofReal C *
        (powerWeightedVolume (n + 1) α
          (horizontalSlab n (2 * A) (a - 2 * B) (a + 2 * B))) ^
            (1 / (ENNReal.ofReal p).toReal) := hbound
    _ ≤ ENNReal.ofReal C *
        ((ENNReal.ofReal (a - 2 * B)) ^ α *
          (volume (ball (0 : Euclidean n) (2 * A)) *
            ENNReal.ofReal (2 * (2 * B)))) ^
            (1 / (ENNReal.ofReal p).toReal) := by
      simpa only [mul_comm] using
        mul_le_mul_left (ENNReal.rpow_le_rpow hDupper hq) (ENNReal.ofReal C)

/-- Existential-constant form of the near-origin local graph-tube test. -/
theorem restrictedStrongType_graphTube_localEntropy_nearOrigin_lower
    (n : ℕ) (hn : 2 ≤ n) {E : Set ℝ} {p α : ℝ}
    (hstrong : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType
      (n + 1) E p α)
    (c : PositiveRadius) (diam δ : ℝ≥0) (T : Finset PositiveRadius)
    {a ρ b h A B R : ℝ}
    (hT : ∀ r ∈ T, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam)
    (hlogsep : Metric.IsSeparated (((δ / 2 : ℝ≥0) : ℝ≥0∞))
      (logRadius '' (↑T : Set PositiveRadius)))
    (hnet : ∀ r : PositiveRadius, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam →
      ∃ t ∈ T, |logRadius r - logRadius t| ≤ ((δ : ℝ≥0) : ℝ) / 2)
    (hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → 2 * b ≤ |(r : ℝ) - (s : ℝ)|)
    (hρ : ∀ r ∈ T, ρ ≤ (r : ℝ))
    (hhemisphere : ∀ r ∈ T, 2 * ρ ≤ (r : ℝ))
    (hppos : 0 < p) (hα : α < 0)
    (hApos : 0 < A) (hBpos : 0 < B)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (hcapHorizontal : ∀ r ∈ T, (r : ℝ) * h < A)
    (hcapVertical : ∀ r ∈ T,
      b + 4 * (ρ * h + (r : ℝ) * h ^ 2) ≤ B)
    (hinputAway : 0 < a - 2 * B)
    (hRpos : 0 < R)
    (hnear : ∀ r ∈ T, |a - (r : ℝ)| + 2 * ρ + b ≤ R) :
    ∃ C : ℝ, 0 < C ∧
      ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) *
        ((localMultiplicativeEntropy E c diam δ).toENNReal *
          ((ENNReal.ofReal R) ^ α *
            (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b)))) ^
          (1 / (ENNReal.ofReal p).toReal) ≤
        ENNReal.ofReal C *
          ((ENNReal.ofReal (a - 2 * B)) ^ α *
            (volume (ball (0 : Euclidean n) (2 * A)) *
              ENNReal.ofReal (2 * (2 * B)))) ^
            (1 / (ENNReal.ofReal p).toReal) := by
  rcases hstrong with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  exact restrictedStrongType_graphTube_localEntropy_nearOrigin_lower_of_bound
    n hn hbound c diam δ T hT hlogsep hnet hsep hρ hhemisphere hppos hα
    hApos hBpos hh hquarter hcapHorizontal hcapVertical hinputAway hRpos hnear

/-- The same near-origin lower test after raising the norm inequality to the
power `p`.  This is the literal local-entropy power inequality from which the
dyadic exponent `n * (p - 1)` is read off. -/
theorem restrictedStrongType_graphTube_localEntropy_nearOrigin_power_lower_of_bound
    (n : ℕ) (hn : 2 ≤ n) {E : Set ℝ} {p α C : ℝ}
    (hstrong : ∀ f : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume (n + 1) α) →
        MemLp (restrictedNormalizedSphericalMaximal (n + 1) E
          (f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume (n + 1) α) ∧
        eLpNorm (restrictedNormalizedSphericalMaximal (n + 1) E
          (f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume (n + 1) α) ≤
          ENNReal.ofReal C * eLpNorm (f : Euclidean (n + 1) → ℂ)
            (ENNReal.ofReal p) (powerWeightedVolume (n + 1) α))
    (c : PositiveRadius) (diam δ : ℝ≥0) (T : Finset PositiveRadius)
    {a ρ b h A B R : ℝ}
    (hT : ∀ r ∈ T, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam)
    (_hlogsep : Metric.IsSeparated (((δ / 2 : ℝ≥0) : ℝ≥0∞))
      (logRadius '' (↑T : Set PositiveRadius)))
    (hnet : ∀ r : PositiveRadius, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam →
      ∃ t ∈ T, |logRadius r - logRadius t| ≤ ((δ : ℝ≥0) : ℝ) / 2)
    (hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → 2 * b ≤ |(r : ℝ) - (s : ℝ)|)
    (hρ : ∀ r ∈ T, ρ ≤ (r : ℝ))
    (hhemisphere : ∀ r ∈ T, 2 * ρ ≤ (r : ℝ))
    (hppos : 0 < p) (hα : α < 0)
    (hApos : 0 < A) (hBpos : 0 < B)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (hcapHorizontal : ∀ r ∈ T, (r : ℝ) * h < A)
    (hcapVertical : ∀ r ∈ T,
      b + 4 * (ρ * h + (r : ℝ) * h ^ 2) ≤ B)
    (hinputAway : 0 < a - 2 * B)
    (hRpos : 0 < R)
    (hnear : ∀ r ∈ T, |a - (r : ℝ)| + 2 * ρ + b ≤ R) :
    ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) ^ p *
        ((localMultiplicativeEntropy E c diam δ).toENNReal *
          ((ENNReal.ofReal R) ^ α *
            (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b)))) ≤
        (ENNReal.ofReal C) ^ p *
          ((ENNReal.ofReal (a - 2 * B)) ^ α *
            (volume (ball (0 : Euclidean n) (2 * A)) *
              ENNReal.ofReal (2 * (2 * B)))) := by
  have hbound :=
    restrictedStrongType_graphTube_localEntropy_nearOrigin_lower_of_bound n hn hstrong c diam δ T
      hT _hlogsep hnet hsep hρ hhemisphere hppos hα hApos hBpos hh hquarter
      hcapHorizontal hcapVertical hinputAway hRpos hnear
  have hq : 1 / (ENNReal.ofReal p).toReal = p⁻¹ := by
    rw [ENNReal.toReal_ofReal hppos.le]
    simp only [one_div]
  rw [hq] at hbound
  have hpow := ENNReal.rpow_le_rpow hbound hppos.le
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hppos.le,
    ENNReal.rpow_inv_rpow hppos.ne'] using hpow

/-- Existential-constant form of the powered near-origin graph-tube test. -/
theorem restrictedStrongType_graphTube_localEntropy_nearOrigin_power_lower
    (n : ℕ) (hn : 2 ≤ n) {E : Set ℝ} {p α : ℝ}
    (hstrong : HasRestrictedNormalizedSphericalMaximalPowerWeightStrongType
      (n + 1) E p α)
    (c : PositiveRadius) (diam δ : ℝ≥0) (T : Finset PositiveRadius)
    {a ρ b h A B R : ℝ}
    (hT : ∀ r ∈ T, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam)
    (hlogsep : Metric.IsSeparated (((δ / 2 : ℝ≥0) : ℝ≥0∞))
      (logRadius '' (↑T : Set PositiveRadius)))
    (hnet : ∀ r : PositiveRadius, (r : ℝ) ∈ E ∩ multiplicativeInterval c diam →
      ∃ t ∈ T, |logRadius r - logRadius t| ≤ ((δ : ℝ≥0) : ℝ) / 2)
    (hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → 2 * b ≤ |(r : ℝ) - (s : ℝ)|)
    (hρ : ∀ r ∈ T, ρ ≤ (r : ℝ))
    (hhemisphere : ∀ r ∈ T, 2 * ρ ≤ (r : ℝ))
    (hppos : 0 < p) (hα : α < 0)
    (hApos : 0 < A) (hBpos : 0 < B)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (hcapHorizontal : ∀ r ∈ T, (r : ℝ) * h < A)
    (hcapVertical : ∀ r ∈ T,
      b + 4 * (ρ * h + (r : ℝ) * h ^ 2) ≤ B)
    (hinputAway : 0 < a - 2 * B)
    (hRpos : 0 < R)
    (hnear : ∀ r ∈ T, |a - (r : ℝ)| + 2 * ρ + b ≤ R) :
    ∃ C : ℝ, 0 < C ∧
      ((ENNReal.ofReal (surfaceMass n) *
          ((ENNReal.ofReal (h / 2)) ^ (n - 2) * ENNReal.ofReal (h ^ 2 / 4))) /
          ENNReal.ofReal (surfaceMass (n + 1))) ^ p *
        ((localMultiplicativeEntropy E c diam δ).toENNReal *
          ((ENNReal.ofReal R) ^ α *
            (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * b)))) ≤
        (ENNReal.ofReal C) ^ p *
          ((ENNReal.ofReal (a - 2 * B)) ^ α *
            (volume (ball (0 : Euclidean n) (2 * A)) *
              ENNReal.ofReal (2 * (2 * B)))) := by
  rcases hstrong with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  exact restrictedStrongType_graphTube_localEntropy_nearOrigin_power_lower_of_bound
    n hn hbound c diam δ T hT hlogsep hnet hsep hρ hhemisphere hppos hα
    hApos hBpos hh hquarter hcapHorizontal hcapVertical hinputAway hRpos hnear

end

end LeanSpherical.HarmonicAnalysis
