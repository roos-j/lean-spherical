/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.MinkowskiFacts
import LeanSpherical.HarmonicAnalysis.FractalDilations.MinkowskiEstimate

/-!
# Positive Minkowski covers and finite-radius discretization

The definition of upper Minkowski dimension permits unused intervals in a
cover.  For maximal estimates it is useful to discard them: an interval that
actually meets a radius set contained in `[1,2]` is contained in the positive
half-line at every scale below one.  This file packages that elementary
cleanup together with the finite-cover maximal reduction.

The remaining analytic input in the paper is a scale-decaying estimate for
the interval maximal operators.  Once such an estimate is proved for a
frequency piece, `minkowski_finite_cover_reduction` supplies exactly its
Minkowski cardinality cost.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set

noncomputable section

/-- The part of a covering interval which lies in the ambient radius range
`[1,2]`.  Clipping lets the short-interval Fourier estimates be applied
without paying for harmless pieces of a cover outside the allowed radii. -/
def clippedCoverInterval (c δ : ℝ) : Set ℝ :=
  Icc (max 1 (c - δ / 2)) (min 2 (c + δ / 2))

theorem mem_clippedCoverInterval_of_mem_of_mem_interval
    {E : Set ℝ} {c δ r : ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hrE : r ∈ E) (hr : r ∈ Icc (c - δ / 2) (c + δ / 2)) :
    r ∈ clippedCoverInterval c δ := by
  constructor
  · exact max_le (hE hrE).1 hr.1
  · exact le_min (hE hrE).2 hr.2

theorem clippedCoverInterval_subset_Icc (c δ : ℝ) :
    clippedCoverInterval c δ ⊆ Icc (1 : ℝ) 2 := by
  intro r hr
  constructor
  · exact le_trans (le_max_left _ _) hr.1
  · exact le_trans hr.2 (min_le_left _ _)

theorem clippedCoverInterval_length_le (c δ : ℝ) :
    min 2 (c + δ / 2) - max 1 (c - δ / 2) ≤ δ := by
  have hright : min 2 (c + δ / 2) ≤ c + δ / 2 := min_le_right _ _
  have hleft : c - δ / 2 ≤ max 1 (c - δ / 2) := le_max_right _ _
  linarith

/-- Clipping every member of a cover to `[1,2]` still covers the radius
set. -/
theorem IsIntervalCover.clippedCoverIntervals
    {E : Set ℝ} {δ : ℝ} {ι : Finset ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hcover : IsIntervalCover E δ ι) :
    E ⊆ ⋃ c ∈ ι, clippedCoverInterval c δ := by
  intro r hrE
  rcases Set.mem_iUnion.mp (hcover hrE) with ⟨c, hc⟩
  rcases Set.mem_iUnion.mp hc with ⟨hcι, hr⟩
  exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcι,
    mem_clippedCoverInterval_of_mem_of_mem_interval hE hrE hr⟩⟩

/-- The subfamily of clipped intervals which are nonempty.  The original
Minkowski cover may contain unused intervals; filtering them here gives
honest endpoint intervals while retaining the same cardinality bound. -/
noncomputable def clippedActiveCenters (δ : ℝ) (ι : Finset ℝ) : Finset ℝ := by
  classical
  exact ι.filter fun c => (clippedCoverInterval c δ).Nonempty

theorem clippedActiveCenters_subset (δ : ℝ) (ι : Finset ℝ) :
    clippedActiveCenters δ ι ⊆ ι := by
  classical
  intro c hc
  exact (Finset.mem_filter.mp hc).1

theorem card_clippedActiveCenters_le (δ : ℝ) (ι : Finset ℝ) :
    (clippedActiveCenters δ ι).card ≤ ι.card := by
  classical
  exact Finset.card_filter_le _ _

theorem mem_clippedActiveCenters_interval_nonempty
    {δ : ℝ} {ι : Finset ℝ} {c : ℝ} (hc : c ∈ clippedActiveCenters δ ι) :
    (clippedCoverInterval c δ).Nonempty := by
  classical
  exact (Finset.mem_filter.mp hc).2

/-- After clipping and discarding empty intervals, the family still covers
`E`. -/
theorem IsIntervalCover.clippedActiveCover
    {E : Set ℝ} {δ : ℝ} {ι : Finset ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (hcover : IsIntervalCover E δ ι) :
    E ⊆ ⋃ c ∈ clippedActiveCenters δ ι, clippedCoverInterval c δ := by
  classical
  intro r hrE
  rcases Set.mem_iUnion.mp (hcover hrE) with ⟨c, hc⟩
  rcases Set.mem_iUnion.mp hc with ⟨hcι, hrc⟩
  have hrclip : r ∈ clippedCoverInterval c δ :=
    mem_clippedCoverInterval_of_mem_of_mem_interval hE hrE hrc
  have hnonempty : (clippedCoverInterval c δ).Nonempty := ⟨r, hrclip⟩
  have hcactive : c ∈ clippedActiveCenters δ ι := by
    exact Finset.mem_filter.mpr ⟨hcι, hnonempty⟩
  exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcactive, hrclip⟩⟩

/-- The members of a finite interval cover which really meet the covered
set. -/
noncomputable def activeIntervalCenters (E : Set ℝ) (δ : ℝ) (ι : Finset ℝ) : Finset ℝ := by
  classical
  exact ι.filter fun c => (E ∩ Icc (c - δ / 2) (c + δ / 2)).Nonempty

/-- Deleting inactive intervals cannot add centers. -/
theorem activeIntervalCenters_subset
    (E : Set ℝ) (δ : ℝ) (ι : Finset ℝ) :
    activeIntervalCenters E δ ι ⊆ ι := by
  classical
  intro c hc
  change c ∈ ι.filter fun c => (E ∩ Icc (c - δ / 2) (c + δ / 2)).Nonempty at hc
  exact (Finset.mem_filter.mp hc).1

/-- The active part of a cover still covers the same set. -/
theorem IsIntervalCover.activeIntervalCenters
    {E : Set ℝ} {δ : ℝ} {ι : Finset ℝ}
    (hcover : IsIntervalCover E δ ι) :
    IsIntervalCover E δ (activeIntervalCenters E δ ι) := by
  classical
  intro x hx
  rcases Set.mem_iUnion.mp (hcover hx) with ⟨c, hcx⟩
  rcases Set.mem_iUnion.mp hcx with ⟨hc, hxinterval⟩
  refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨?_, hxinterval⟩⟩
  change c ∈ ι.filter fun c => (E ∩ Icc (c - δ / 2) (c + δ / 2)).Nonempty
  refine Finset.mem_filter.mpr ⟨hc, ?_⟩
  exact ⟨x, hx, hxinterval⟩

/-- An active interval at a scale below one is wholly positive when the
radius set lies in `[1,2]`. -/
theorem interval_subset_Ioi_zero_of_mem_activeIntervalCenters
    {E : Set ℝ} {δ : ℝ} {ι : Finset ℝ} {c : ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) (_hδ : 0 < δ) (hδone : δ < 1)
    (hc : c ∈ activeIntervalCenters E δ ι) :
    Icc (c - δ / 2) (c + δ / 2) ⊆ Ioi (0 : ℝ) := by
  classical
  change c ∈ ι.filter fun c => (E ∩ Icc (c - δ / 2) (c + δ / 2)).Nonempty at hc
  rcases (Finset.mem_filter.mp hc).2 with ⟨x, hxE, hxinterval⟩
  intro y hy
  have hxone : 1 ≤ x := (hE hxE).1
  have hxc : x ≤ c + δ / 2 := hxinterval.2
  have hcy : c - δ / 2 ≤ y := hy.1
  change 0 < y
  nlinarith

/-- Active interval covers have no larger cardinality than the original
cover. -/
theorem card_activeIntervalCenters_le
    (E : Set ℝ) (δ : ℝ) (ι : Finset ℝ) :
    (activeIntervalCenters E δ ι).card ≤ ι.card := by
  classical
  change (ι.filter fun c => (E ∩ Icc (c - δ / 2) (c + δ / 2)).Nonempty).card ≤ ι.card
  exact Finset.card_filter_le _ _

/-- The upper Minkowski covering estimate can always be realized by intervals
contained in the positive half-line. -/
theorem exists_positive_intervalCovers_of_hasUpperMinkowskiExponent
    {E : Set ℝ} {β : ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hM : HasUpperMinkowskiExponent E β) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ ι : Finset ℝ, IsIntervalCover E δ ι ∧
        (ι.card : ℝ) ≤ C * δ ^ (-(β + ε)) ∧
        ∀ c ∈ ι, Icc (c - δ / 2) (c + δ / 2) ⊆ Ioi (0 : ℝ) := by
  intro ε hε
  obtain ⟨C, hC, hcovers⟩ := hM ε hε
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδone
  obtain ⟨ι, hcover, hcard⟩ := hcovers δ hδ hδone
  let κ : Finset ℝ := activeIntervalCenters E δ ι
  refine ⟨κ, hcover.activeIntervalCenters, ?_, ?_⟩
  · calc
      (κ.card : ℝ) ≤ (ι.card : ℝ) := by
        exact_mod_cast card_activeIntervalCenters_le E δ ι
      _ ≤ C * δ ^ (-(β + ε)) := hcard
  · intro c hc
    exact interval_subset_Ioi_zero_of_mem_activeIntervalCenters hE hδ hδone hc

/-- The preceding positive-cover statement with the usual arbitrary loss
obtained from equality of the upper Minkowski dimension. -/
theorem exists_positive_intervalCovers_of_upperMinkowskiDimension_eq
    {E : Set ℝ} {β : ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hdim : upperMinkowskiDimension E = β) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ ι : Finset ℝ, IsIntervalCover E δ ι ∧
        (ι.card : ℝ) ≤ C * δ ^ (-(β + ε)) ∧
        ∀ c ∈ ι, Icc (c - δ / 2) (c + δ / 2) ⊆ Ioi (0 : ℝ) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨C, hC, hcovers⟩ :=
    exists_positive_intervalCovers_of_hasUpperMinkowskiExponent hE
      (hasUpperMinkowskiExponent_add_of_upperMinkowskiDimension_eq hE hdim hhalf)
      (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδone
  obtain ⟨ι, hcover, hcard, hpositive⟩ := hcovers δ hδ hδone
  refine ⟨ι, hcover, ?_, hpositive⟩
  have hexp : -((β + ε / 2) + ε / 2) = -(β + ε) := by ring
  simpa only [hexp] using hcard

/-- A finite-scale Minkowski reduction for the fractal spherical maximal
operator.  The hypothesis `hlocal` is the sole analytic input: it is a
uniform estimate over intervals of length `δ`.  The conclusion separates its
cardinality loss from that local estimate. -/
theorem minkowski_finite_cover_reduction
    {d : ℕ} {E : Set ℝ} {β ε δ p q L : ℝ}
    (hd : 0 < d) (hE : E ⊆ Icc (1 : ℝ) 2)
    (hM : HasUpperMinkowskiExponent E β) (hε : 0 < ε)
    (hδ : 0 < δ) (hδone : δ < 1)
    (hq : 1 ≤ ENNReal.ofReal q)
    (hlocal : ∀ c : ℝ, ∀ f : SchwartzMap (Euclidean d) ℂ,
      eLpNorm (fractalSphericalMaximalReal d
        (Icc (c - δ / 2) (c + δ / 2)) f) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal L * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume) :
    ∃ C : ℝ, 0 < C ∧ ∃ ι : Finset ℝ,
      IsIntervalCover E δ ι ∧
      (ι.card : ℝ) ≤ C * δ ^ (-(β + ε)) ∧
      ∀ f : SchwartzMap (Euclidean d) ℂ,
        eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume ≤
          (ι.card : ENNReal) *
            (ENNReal.ofReal L * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume) := by
  obtain ⟨C, hC, hCovers⟩ :=
    exists_positive_intervalCovers_of_hasUpperMinkowskiExponent hE hM ε hε
  obtain ⟨ι, hcover, hcard, hpositive⟩ := hCovers δ hδ hδone
  refine ⟨C, hC, ι, hcover, hcard, ?_⟩
  intro f
  have hEpos : E ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one (hE hr).1
  exact eLpNorm_fractalSphericalMaximalReal_le_card_mul_of_intervalCover
    hd hcover hEpos hpositive hq (fun c hc g => hlocal c g) f

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
