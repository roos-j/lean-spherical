/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4SelectedSublinearity
import LeanSpherical.HarmonicAnalysis.InterpolationTail

/-!
# Exact finite radius-gap shell reassembly

The `TT*` kernel at one frequency is a finite sum over sampled radii.  This
file records the purely algebraic step which splits that literal sum into its
dyadic radius-gap shells.  It deliberately works with the actual kernel
operator, rather than a positive majorant: cancellation is retained inside
each shell and the triangle inequality is used only after the exact
partition identity.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The part of a finite relation carried by a prescribed gap level. -/
def q4LevelShellRelation
    {I L : Type*} (R : I → I → Prop) (level : I → I → L) (n : L) : I → I → Prop :=
  fun i l => R i l ∧ level i l = n

/-- The level shell inherits decidability from the original finite relation
and equality of levels. -/
instance instDecidableRelQ4LevelShellRelation
    {I L : Type*} (R : I → I → Prop) [DecidableRel R]
    (level : I → I → L) [DecidableEq L] (n : L) :
    DecidableRel (q4LevelShellRelation R level n) := by
  intro i l
  change Decidable (R i l ∧ level i l = n)
  infer_instance

/-- A finite relation is the disjoint union of the level relations provided
every active pair has a level in the supplied finite index set. -/
theorem q4KernelTTStarShell_eq_sum_levelShells
    {I L X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq I] [DecidableEq L]
    (μ : Measure X) (s : Finset I) (R : I → I → Prop) [DecidableRel R]
    (level : I → I → L) (levels : Finset L)
    (hlevels : ∀ i l, R i l → level i l ∈ levels)
    (K : I → I → X → ℂ) (g : I → X → ℂ) (i : I) (x : X) :
    q4KernelTTStarShell μ s R K g i x =
      ∑ n ∈ levels,
        q4KernelTTStarShell μ s (q4LevelShellRelation R level n) K g i x := by
  classical
  unfold q4KernelTTStarShell
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hR : R i l
  · have hmem : level i l ∈ levels := hlevels i l hR
    simp [q4LevelShellRelation, hR, hmem]
  · simp [q4LevelShellRelation, hR]

/-- The same exact partition identity after the measurable radius selector has
been inserted.  This is the identity used to pass from individual gap shells
back to the selected finite `TT*` operator. -/
theorem q4SelectedKernelTTStarShell_eq_sum_levelShells
    {I L X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq I] [DecidableEq L]
    (μ : Measure X) (s : Finset I) (R : I → I → Prop) [DecidableRel R]
    (level : I → I → L) (levels : Finset L)
    (hlevels : ∀ i l, R i l → level i l ∈ levels)
    (K : I → I → X → ℂ) (rho : X → I) (g : X → ℂ) (x : X) :
    q4SelectedKernelTTStarShell μ s R K rho g x =
      ∑ n ∈ levels,
        q4SelectedKernelTTStarShell μ s
          (q4LevelShellRelation R level n) K rho g x := by
  unfold q4SelectedKernelTTStarShell
  exact q4KernelTTStarShell_eq_sum_levelShells μ s R level levels hlevels K
    (q4SelectedFibre rho g) (rho x) x

/-- Cancellation is kept inside every gap shell; only after the exact
partition identity do we use the triangle inequality. -/
theorem norm_q4SelectedKernelTTStarShell_le_sum_levelShells
    {I L X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq I] [DecidableEq L]
    (μ : Measure X) (s : Finset I) (R : I → I → Prop) [DecidableRel R]
    (level : I → I → L) (levels : Finset L)
    (hlevels : ∀ i l, R i l → level i l ∈ levels)
    (K : I → I → X → ℂ) (rho : X → I) (g : X → ℂ) (x : X) :
    ‖q4SelectedKernelTTStarShell μ s R K rho g x‖ ≤
      ∑ n ∈ levels,
        ‖q4SelectedKernelTTStarShell μ s
          (q4LevelShellRelation R level n) K rho g x‖ := by
  rw [q4SelectedKernelTTStarShell_eq_sum_levelShells μ s R level levels
    hlevels K rho g x]
  exact norm_sum_le _ _

/-- Minkowski upgrades the pointwise shell reassembly to an actual finite
`Lᵠ` estimate.  The only hypotheses are measurability of the literal shell
outputs and `q ≥ 1`; no positivity or factorization of the `TT*` operator is
used. -/
theorem eLpNorm_norm_q4SelectedKernelTTStarShell_le_sum_levelShells
    {I L X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq I] [DecidableEq L]
    (μ : Measure X) (s : Finset I) (R : I → I → Prop) [DecidableRel R]
    (level : I → I → L) (levels : Finset L)
    (hlevels : ∀ i l, R i l → level i l ∈ levels)
    (K : I → I → X → ℂ) (rho : X → I) (g : X → ℂ)
    {q : ENNReal} (hq : 1 ≤ q)
    (hmeas : ∀ n ∈ levels, AEStronglyMeasurable
      (fun x => ‖q4SelectedKernelTTStarShell μ s
        (q4LevelShellRelation R level n) K rho g x‖) μ) :
    eLpNorm (fun x => ‖q4SelectedKernelTTStarShell μ s R K rho g x‖) q μ ≤
      ∑ n ∈ levels, eLpNorm (fun x => ‖q4SelectedKernelTTStarShell μ s
        (q4LevelShellRelation R level n) K rho g x‖) q μ := by
  let T : L → X → ℝ := fun n x => ‖q4SelectedKernelTTStarShell μ s
    (q4LevelShellRelation R level n) K rho g x‖
  calc
    eLpNorm (fun x => ‖q4SelectedKernelTTStarShell μ s R K rho g x‖) q μ ≤
        eLpNorm (fun x => ∑ n ∈ levels, T n x) q μ := by
      apply eLpNorm_mono_real
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      simpa only [T] using
        norm_q4SelectedKernelTTStarShell_le_sum_levelShells μ s R level levels
          hlevels K rho g x
    _ = eLpNorm (∑ n ∈ levels, T n) q μ := by
      apply eLpNorm_congr_ae
      filter_upwards with x
      simp only [Finset.sum_apply]
    _ ≤ ∑ n ∈ levels, eLpNorm (T n) q μ :=
      eLpNorm_sum_le (f := T) (s := levels) (fun n hn => by
        simpa only [T] using hmeas n hn) hq
    _ = ∑ n ∈ levels, eLpNorm (fun x => ‖q4SelectedKernelTTStarShell μ s
        (q4LevelShellRelation R level n) K rho g x‖) q μ := by
      apply Finset.sum_congr rfl
      intro n hn
      rfl

/-- If the literal gap shells have geometric `Lᵠ` bounds, their exact finite
reassembly has the corresponding uniform bound.  This is the shell summation
step used after the strict crossed estimate; it does not use Bourgain's
endpoint interpolation trick. -/
theorem eLpNorm_norm_q4SelectedKernelTTStarShell_le_geometric_levelShells
    {I X : Type*} [Sub X] [MeasurableSpace X] [DecidableEq I]
    (μ : Measure X) (s : Finset I) (R : I → I → Prop) [DecidableRel R]
    (level : I → I → ℕ) (N : ℕ)
    (hlevels : ∀ i l, R i l → level i l ∈ Finset.range N)
    (K : I → I → X → ℂ) (rho : X → I) (g : X → ℂ)
    {q : ENNReal} (hq : 1 ≤ q)
    (hmeas : ∀ n, AEStronglyMeasurable
      (fun x => ‖q4SelectedKernelTTStarShell μ s
        (q4LevelShellRelation R level n) K rho g x‖) μ)
    (C r : ENNReal)
    (hshell : ∀ n, eLpNorm (fun x => ‖q4SelectedKernelTTStarShell μ s
      (q4LevelShellRelation R level n) K rho g x‖) q μ ≤ C * r ^ n) :
    eLpNorm (fun x => ‖q4SelectedKernelTTStarShell μ s R K rho g x‖) q μ ≤
      C * (1 - r)⁻¹ := by
  let T : ℕ → X → ℝ := fun n x => ‖q4SelectedKernelTTStarShell μ s
    (q4LevelShellRelation R level n) K rho g x‖
  calc
    eLpNorm (fun x => ‖q4SelectedKernelTTStarShell μ s R K rho g x‖) q μ ≤
        eLpNorm (fun x => ∑ n ∈ Finset.range N, T n x) q μ := by
      apply eLpNorm_mono_real
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      simpa only [T] using
        norm_q4SelectedKernelTTStarShell_le_sum_levelShells μ s R level
          (Finset.range N) hlevels K rho g x
    _ ≤ C * (1 - r)⁻¹ := by
      apply eLpNorm_sum_range_le_geometric μ q hq T
      · intro n
        simpa only [T] using hmeas n
      · intro n
        simpa only [T] using hshell n

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
