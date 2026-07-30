/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.ClusterPacking
import LeanSpherical.HarmonicAnalysis.SurfaceCore

/-!
# Cartesian geometry for clustered-radius tests

The clustered-radius construction uses thin slabs in the distinguished radial
coordinate and a common transverse ball.  This file records their exact
Lebesgue volumes and the elementary disjointness supplied by separated radial
centres.  It is deliberately independent of the spherical averaging step.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

/-- The standard splitting of `Euclidean (n + 1)` into its first `n`
coordinates and its final coordinate. -/
def euclideanSuccCoordinates (n : ℕ) : Euclidean (n + 1) → Euclidean n × ℝ :=
  fun x =>
    (MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i => x (Fin.castAdd 1 i)),
      x (Fin.last n))

/-- A transverse ball times an open interval in the final coordinate. -/
def horizontalSlab (n : ℕ) (ρ a b : ℝ) : Set (Euclidean (n + 1)) :=
  euclideanSuccCoordinates n ⁻¹' (ball (0 : Euclidean n) ρ ×ˢ Ioo a b)

theorem measurable_euclideanSuccCoordinates (n : ℕ) :
    Measurable (euclideanSuccCoordinates n) := by
  have hfirst : Measurable (fun x : Euclidean (n + 1) =>
      MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i => x (Fin.castAdd 1 i))) := by
    apply (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp
    apply measurable_pi_lambda
    intro i
    fun_prop
  exact hfirst.prodMk (by fun_prop)

theorem map_euclideanSuccCoordinates_volume (n : ℕ) :
    Measure.map (euclideanSuccCoordinates n) volume =
      ((volume : Measure (Euclidean n)).prod volume) := by
  change Measure.map (fun x : Euclidean (n + 1) =>
      (MeasurableEquiv.toLp 2 (Fin n → ℝ) (fun i => x (Fin.castAdd 1 i)),
        x (Fin.last n))) volume = ((volume : Measure (Euclidean n)).prod volume)
  exact LeanSpherical.HarmonicAnalysis.map_euclideanSucc_coordinates_volume n

theorem measurableSet_horizontalSlab (n : ℕ) (ρ a b : ℝ) :
    MeasurableSet (horizontalSlab n ρ a b) := by
  exact ((isOpen_ball.prod isOpen_Ioo).measurableSet).preimage
    (measurable_euclideanSuccCoordinates n)

/-- The exact volume of a Cartesian transverse-ball/radial-interval slab. -/
theorem volume_horizontalSlab (n : ℕ) (ρ a b : ℝ) :
    volume (horizontalSlab n ρ a b) =
      volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (b - a) := by
  let A : Set (Euclidean n × ℝ) := ball (0 : Euclidean n) ρ ×ˢ Ioo a b
  have hA : MeasurableSet A := (isOpen_ball.prod isOpen_Ioo).measurableSet
  calc
    volume (horizontalSlab n ρ a b) = Measure.map (euclideanSuccCoordinates n) volume A := by
      symm
      simpa only [horizontalSlab, A] using
        (Measure.map_apply (measurable_euclideanSuccCoordinates n) hA)
    _ = ((volume : Measure (Euclidean n)).prod volume) A := by
      rw [map_euclideanSuccCoordinates_volume]
    _ = volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (b - a) := by
      simp only [A, Measure.prod_prod, Real.volume_Ioo]

/-- A horizontal slab of half-width `h`, centred at the final coordinate
`t`. -/
def centeredHorizontalSlab (n : ℕ) (ρ h t : ℝ) : Set (Euclidean (n + 1)) :=
  horizontalSlab n ρ (t - h) (t + h)

/-- Slabs with sufficiently separated final-coordinate centres are disjoint.
Their transverse radii may be different. -/
theorem disjoint_centeredHorizontalSlab_of_two_mul_le_abs_sub
    {n : ℕ} {ρ ρ' h s t : ℝ} (hsep : 2 * h ≤ |s - t|) :
    Disjoint (centeredHorizontalSlab n ρ h s)
      (centeredHorizontalSlab n ρ' h t) := by
  unfold centeredHorizontalSlab horizontalSlab
  apply Disjoint.preimage
  apply Disjoint.set_prod_right
  rw [Ioo_disjoint_Ioo]
  by_cases hst : s ≤ t
  · have habs : |s - t| = t - s := by
      calc
        |s - t| = -(s - t) := abs_of_nonpos (sub_nonpos.mpr hst)
        _ = t - s := by ring
    rw [habs] at hsep
    calc
      min (s + h) (t + h) ≤ s + h := min_le_left _ _
      _ ≤ t - h := by linarith
      _ ≤ max (s - h) (t - h) := le_max_right _ _
  · have hts : t ≤ s := le_of_not_ge hst
    have habs : |s - t| = s - t := abs_of_nonneg (sub_nonneg.mpr hts)
    rw [habs] at hsep
    calc
      min (s + h) (t + h) ≤ t + h := min_le_right _ _
      _ ≤ s - h := by linarith
      _ ≤ max (s - h) (t - h) := le_max_left _ _

/-- A strictly separated finite family of centres produces pairwise disjoint
horizontal slabs when the half-width is one quarter of the separation mesh. -/
theorem strictlySeparated_pairwiseDisjoint_centeredHorizontalSlabs
    {n : ℕ} {s : Finset ℝ} {ρ δ : ℝ}
    (hsep : StrictlySeparated s (δ / 2)) :
    (↑s : Set ℝ).PairwiseDisjoint
      (fun t => centeredHorizontalSlab n ρ (δ / 8) t) := by
  intro r hr t ht hrt
  apply disjoint_centeredHorizontalSlab_of_two_mul_le_abs_sub
  have hstrict : δ / 2 < |r - t| := hsep hr ht hrt
  by_cases hδ : 0 ≤ δ
  · have hquarter : δ / 4 ≤ δ / 2 := by linarith
    calc
      2 * (δ / 8) = δ / 4 := by ring
      _ ≤ |r - t| := (lt_of_le_of_lt hquarter hstrict).le
  · have hδneg : δ < 0 := lt_of_not_ge hδ
    calc
      2 * (δ / 8) = δ / 4 := by ring
      _ ≤ 0 := by linarith
      _ ≤ |r - t| := abs_nonneg _

/-- The volume of a centred slab is the transverse-ball volume times its
full radial width. -/
theorem volume_centeredHorizontalSlab (n : ℕ) (ρ h t : ℝ) :
    volume (centeredHorizontalSlab n ρ h t) =
      volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * h) := by
  rw [centeredHorizontalSlab, volume_horizontalSlab]
  congr 2
  ring

theorem measurableSet_centeredHorizontalSlab (n : ℕ) (ρ h t : ℝ) :
    MeasurableSet (centeredHorizontalSlab n ρ h t) := by
  exact measurableSet_horizontalSlab n ρ (t - h) (t + h)

/-- Exact volume of the finite disjoint slab union used as the output region
in the clustered-radius test. -/
theorem volume_biUnion_centeredHorizontalSlab
    {n : ℕ} {s : Finset ℝ} {ρ δ : ℝ}
    (hsep : StrictlySeparated s (δ / 2)) :
    volume (⋃ t ∈ s, centeredHorizontalSlab n ρ (δ / 8) t) =
      (s.card : ENNReal) *
        (volume (ball (0 : Euclidean n) ρ) * ENNReal.ofReal (2 * (δ / 8))) := by
  rw [measure_biUnion_finset
    (strictlySeparated_pairwiseDisjoint_centeredHorizontalSlabs (n := n) (ρ := ρ) hsep)
    (fun t _ => measurableSet_centeredHorizontalSlab n ρ (δ / 8) t)]
  simp only [volume_centeredHorizontalSlab]
  simp

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
