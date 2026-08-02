/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.HardyLittlewoodMaximal
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# Finite Calderón--Zygmund data for lacunary kernels

This file exposes the finite, literal portion of the ball selection used in
the lacunary endpoint argument.  We deliberately keep the data as finite
families of Euclidean dyadic balls, which is the form consumed by the
finite-frequency/lacunary estimates.  No generic singular-integral interface
is introduced here.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set
open scoped BigOperators

noncomputable section

/-- The literal dyadic ball attached to a centre/scale pair. -/
def lacunaryCZBall {d : Nat} (a : Euclidean d × ℤ) : Set (Euclidean d) :=
  Metric.ball a.1 ((2 : ℝ) ^ a.2)

/-- The fixed fourfold enlargement used by the Vitali selection. -/
def lacunaryCZBallEnlarged {d : Nat} (a : Euclidean d × ℤ) : Set (Euclidean d) :=
  Metric.ball a.1 (4 * (2 : ℝ) ^ a.2)

/-- A finite family of dyadic balls admits a disjoint subfamily whose
fourfold enlargements cover the original family.  The radius cap is explicit
because it is exactly the finite-frequency truncation used below. -/
theorem exists_finset_lacunaryCZ_selection
    {d : Nat} (I : Finset (Euclidean d × ℤ)) (R : ℝ)
    (hR : ∀ a ∈ I, (2 : ℝ) ^ a.2 ≤ R) :
    ∃ U : Finset (Euclidean d × ℤ),
      (↑U : Set (Euclidean d × ℤ)) ⊆ I ∧
      (↑U : Set (Euclidean d × ℤ)).PairwiseDisjoint lacunaryCZBall ∧
      (⋃ a ∈ (I : Set (Euclidean d × ℤ)), lacunaryCZBall a) ⊆
        ⋃ a ∈ (U : Set (Euclidean d × ℤ)), lacunaryCZBallEnlarged a := by
  obtain ⟨u, huI, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (I : Set (Euclidean d × ℤ)) (fun a => a.1) (fun a => (2 : ℝ) ^ a.2) R
      (by
        intro a ha
        exact hR a ha)
      4 (by norm_num : (3 : ℝ) < 4)
  let U : Finset (Euclidean d × ℤ) :=
    (I.finite_toSet.subset huI).toFinset
  have hU : (U : Set (Euclidean d × ℤ)) = u := by
    simp only [U, Set.Finite.coe_toFinset]
  refine ⟨U, ?_, ?_, ?_⟩
  · simpa only [hU] using huI
  · rw [hU]
    change u.PairwiseDisjoint (fun a => Metric.ball a.1 ((2 : ℝ) ^ a.2))
    exact hdisj
  · intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨a, haI, hxa⟩
    rcases hcover a haI with ⟨b, hbu, hsub⟩
    refine Set.mem_iUnion₂.mpr ⟨b, ?_, hsub hxa⟩
    simpa only [hU] using hbu

/-- Euclidean volume scales by the fixed fourfold enlargement in the finite
dyadic selection. -/
theorem volume_lacunaryCZBall_enlarged
    {d : Nat} [NeZero d] (a : Euclidean d × ℤ) :
    volume (lacunaryCZBallEnlarged a) =
      (ENNReal.ofReal (4 : ℝ)) ^ d * volume (lacunaryCZBall a) := by
  unfold lacunaryCZBallEnlarged lacunaryCZBall
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), mul_pow]
  ring

/-- The real volume of a selected dyadic ball is its radius to the ambient
dimension times the fixed unit-ball volume. -/
theorem volume_lacunaryCZBall_toReal_eq_radius_pow_mul_unitBall
    {d : Nat} [NeZero d] (a : Euclidean d × ℤ) :
    (volume (lacunaryCZBall a)).toReal =
      ((2 : ℝ) ^ a.2) ^ d *
        (volume (Metric.ball (0 : Euclidean d) 1)).toReal := by
  have hr : 0 ≤ (2 : ℝ) ^ a.2 := (zpow_pos (by norm_num) _).le
  have hvol : volume (lacunaryCZBall a) =
      (ENNReal.ofReal ((2 : ℝ) ^ a.2)) ^ d *
        volume (Metric.ball (0 : Euclidean d) 1) := by
    unfold lacunaryCZBall
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
    simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]


/-- A half-open Euclidean dyadic cell.  Its scale is allowed to be any
integer, so this directly matches the finite scale truncations in the
lacunary argument. -/
structure LacunaryCZDyadicCubeIndex (d : Nat) where
  scale : ℤ
  translation : Fin d → ℤ
  deriving DecidableEq

/-- The literal coordinate dyadic cell indexed by a scale and an integer
translation vector. -/
def lacunaryCZDyadicCube {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    Set (Euclidean d) :=
  (WithLp.ofLp : Euclidean d → Fin d → ℝ) ⁻¹'
    Set.pi Set.univ (fun i =>
      Set.Ico ((q.translation i : ℝ) * (2 : ℝ) ^ q.scale)
        (((q.translation i + 1 : ℤ) : ℝ) * (2 : ℝ) ^ q.scale))

/-- The dyadic parent of a cell. -/
def lacunaryCZDyadicCubeParent {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    LacunaryCZDyadicCubeIndex d :=
  ⟨q.scale + 1, fun i => q.translation i / 2⟩

/-- Dyadic cells are measurable. -/
theorem measurableSet_lacunaryCZDyadicCube
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    MeasurableSet (lacunaryCZDyadicCube q) := by
  unfold lacunaryCZDyadicCube
  apply (PiLp.volume_preserving_ofLp (Fin d)).measurable
  apply MeasurableSet.pi Set.countable_univ
  intro i hi
  exact measurableSet_Ico

/-- The volume of a coordinate dyadic cell is the expected power of its
side length. -/
theorem volume_lacunaryCZDyadicCube
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    volume (lacunaryCZDyadicCube q) =
      ENNReal.ofReal ((2 : ℝ) ^ q.scale) ^ d := by
  let lo : Fin d → ℝ := fun i =>
    (q.translation i : ℝ) * (2 : ℝ) ^ q.scale
  let hi : Fin d → ℝ := fun i =>
    ((q.translation i + 1 : ℤ) : ℝ) * (2 : ℝ) ^ q.scale
  have hmeas : MeasurableSet (Set.pi Set.univ (fun i => Set.Ico (lo i) (hi i))) := by
    apply MeasurableSet.pi Set.countable_univ
    intro i hi
    exact measurableSet_Ico
  unfold lacunaryCZDyadicCube
  rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage hmeas.nullMeasurableSet]
  rw [Real.volume_pi_Ico]
  dsimp [lo, hi]
  have hside : ∀ i : Fin d,
      ((↑(q.translation i + 1) : ℝ) * (2 : ℝ) ^ q.scale -
        (q.translation i : ℝ) * (2 : ℝ) ^ q.scale) = (2 : ℝ) ^ q.scale := by
    intro i
    rw [Int.cast_add, Int.cast_one]
    ring
  simp_rw [hside]
  rw [Finset.prod_const]
  simp

/-- Every coordinate dyadic cell lies in its literal dyadic parent. -/
theorem lacunaryCZDyadicCube_subset_parent
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    lacunaryCZDyadicCube q ⊆ lacunaryCZDyadicCube (lacunaryCZDyadicCubeParent q) := by
  intro x hx
  change (WithLp.ofLp x) ∈ Set.pi Set.univ (fun i =>
    Set.Ico ((q.translation i : ℝ) * (2 : ℝ) ^ q.scale)
      (((q.translation i + 1 : ℤ) : ℝ) * (2 : ℝ) ^ q.scale)) at hx
  change (WithLp.ofLp x) ∈ Set.pi Set.univ (fun i =>
    Set.Ico (((q.translation i / 2 : ℤ) : ℝ) * (2 : ℝ) ^ (q.scale + 1))
      (((q.translation i / 2 + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (q.scale + 1)))
  rw [Set.mem_pi]
  intro i hi
  rw [Set.mem_pi] at hx
  have hxi := hx i (Set.mem_univ i)
  change (q.translation i : ℝ) * (2 : ℝ) ^ q.scale ≤ WithLp.ofLp x i ∧
    WithLp.ofLp x i < ((q.translation i + 1 : ℤ) : ℝ) * (2 : ℝ) ^ q.scale at hxi
  have hs : 0 < (2 : ℝ) ^ q.scale := zpow_pos (by norm_num) _
  have hdivlo : 2 * (q.translation i / 2) ≤ q.translation i := by omega
  have hdivhi : q.translation i + 1 ≤ 2 * (q.translation i / 2) + 2 := by omega
  have hdivloR : ((2 * (q.translation i / 2) : ℤ) : ℝ) ≤ q.translation i := by
    exact_mod_cast hdivlo
  have hdivhiR : ((q.translation i + 1 : ℤ) : ℝ) ≤
      (2 * (q.translation i / 2) + 2 : ℤ) := by
    exact_mod_cast hdivhi
  have hpow : (2 : ℝ) ^ (q.scale + 1) = (2 : ℝ) ^ q.scale * 2 := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  constructor
  · rw [hpow]
    have hform : ((q.translation i / 2 : ℤ) : ℝ) * ((2 : ℝ) ^ q.scale * 2) =
        ((2 * (q.translation i / 2) : ℤ) : ℝ) * (2 : ℝ) ^ q.scale := by
      push_cast
      ring
    rw [hform]
    exact (mul_le_mul_of_nonneg_right hdivloR hs.le).trans hxi.1
  · rw [hpow]
    have hform : ((q.translation i / 2 + 1 : ℤ) : ℝ) * ((2 : ℝ) ^ q.scale * 2) =
        ((2 * (q.translation i / 2) + 2 : ℤ) : ℝ) * (2 : ℝ) ^ q.scale := by
      push_cast
      ring
    rw [hform]
    exact hxi.2.trans_le (mul_le_mul_of_nonneg_right hdivhiR hs.le)

/-- One binary child of a literal dyadic cell. -/
def lacunaryCZDyadicCubeChild {d : Nat} (q : LacunaryCZDyadicCubeIndex d)
    (e : Fin d → Fin 2) : LacunaryCZDyadicCubeIndex d :=
  ⟨q.scale - 1, fun i => 2 * q.translation i + (e i : ℤ)⟩

/-- The finite family of all binary children of one dyadic cell. -/
def lacunaryCZDyadicCubeChildren {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    Finset (LacunaryCZDyadicCubeIndex d) :=
  Finset.univ.image (lacunaryCZDyadicCubeChild q)

theorem lacunaryCZDyadicCubeParent_child
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) (e : Fin d → Fin 2) :
    lacunaryCZDyadicCubeParent (lacunaryCZDyadicCubeChild q e) = q := by
  cases q with
  | mk k m =>
    dsimp [lacunaryCZDyadicCubeChild, lacunaryCZDyadicCubeParent]
    congr
    · omega
    · funext i
      have he : (e i : ℤ) = 0 ∨ (e i : ℤ) = 1 := by omega
      rcases he with he | he <;> rw [he] <;> omega

theorem lacunaryCZDyadicCube_child_subset
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) (e : Fin d → Fin 2) :
    lacunaryCZDyadicCube (lacunaryCZDyadicCubeChild q e) ⊆
      lacunaryCZDyadicCube q := by
  have hsub := lacunaryCZDyadicCube_subset_parent
    (lacunaryCZDyadicCubeChild q e)
  rw [lacunaryCZDyadicCubeParent_child q e] at hsub
  exact hsub

/-- A cell is exactly covered by its finite family of binary children. -/
theorem lacunaryCZDyadicCube_subset_biUnion_children
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    lacunaryCZDyadicCube q ⊆
      ⋃ r ∈ lacunaryCZDyadicCubeChildren q, lacunaryCZDyadicCube r := by
  intro x hx
  let s : ℝ := (2 : ℝ) ^ q.scale
  let e : Fin d → Fin 2 := fun i =>
    if WithLp.ofLp x i < ((q.translation i : ℝ) + 1 / 2) * s then 0 else 1
  refine Set.mem_iUnion₂.mpr ⟨lacunaryCZDyadicCubeChild q e, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  · change (WithLp.ofLp x) ∈ Set.pi Set.univ (fun i =>
      Set.Ico (((2 * q.translation i + (e i : ℤ) : ℤ) : ℝ) *
          (2 : ℝ) ^ (q.scale - 1))
        (((2 * q.translation i + (e i : ℤ) + 1 : ℤ) : ℝ) *
          (2 : ℝ) ^ (q.scale - 1)))
    change (WithLp.ofLp x) ∈ Set.pi Set.univ (fun i =>
      Set.Ico ((q.translation i : ℝ) * s)
        (((q.translation i + 1 : ℤ) : ℝ) * s)) at hx
    rw [Set.mem_pi] at hx ⊢
    have hs : 0 < s := by
      dsimp [s]
      exact zpow_pos (by norm_num) _
    have hhalf : (2 : ℝ) ^ (q.scale - 1) = s / 2 := by
      dsimp [s]
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    intro i hi
    have hxi := hx i (Set.mem_univ i)
    change (q.translation i : ℝ) * s ≤ WithLp.ofLp x i ∧
      WithLp.ofLp x i < ((q.translation i + 1 : ℤ) : ℝ) * s at hxi
    rw [Int.cast_add, Int.cast_one] at hxi
    rw [hhalf]
    by_cases hleft : WithLp.ofLp x i < ((q.translation i : ℝ) + 1 / 2) * s
    · have hleft' : WithLp.ofLp x i < ((q.translation i : ℝ) + 2⁻¹) * s := by
        simpa [one_div] using hleft
      have hei : e i = (0 : Fin 2) := by simp [e, hleft']
      rw [hei]
      norm_num
      have hlower : (2 * (q.translation i : ℝ)) * (s / 2) =
          (q.translation i : ℝ) * s := by ring
      have hupper : (2 * (q.translation i : ℝ) + 1) * (s / 2) =
          ((q.translation i : ℝ) + 2⁻¹) * s := by ring
      rw [hlower, hupper]
      exact ⟨hxi.1, hleft'⟩
    · have hright : ((q.translation i : ℝ) + 1 / 2) * s ≤ WithLp.ofLp x i :=
        le_of_not_gt hleft
      have hleft' : ¬ WithLp.ofLp x i < ((q.translation i : ℝ) + 2⁻¹) * s := by
        simpa [one_div] using hleft
      have hright' : ((q.translation i : ℝ) + 2⁻¹) * s ≤ WithLp.ofLp x i := by
        simpa [one_div] using hright
      have hei : e i = (1 : Fin 2) := by simp [e, hleft']
      rw [hei]
      norm_num
      have hlower : (2 * (q.translation i : ℝ) + 1) * (s / 2) =
          ((q.translation i : ℝ) + 2⁻¹) * s := by ring
      have hupper : (2 * (q.translation i : ℝ) + 1 + 1) * (s / 2) =
          ((q.translation i : ℝ) + 1) * s := by ring
      rw [hlower, hupper]
      exact ⟨hright', hxi.2⟩

/-- The cells at exactly a fixed binary depth below a dyadic cell. -/
def lacunaryCZDyadicCubeDescendants {d : Nat} (q : LacunaryCZDyadicCubeIndex d) : Nat →
    Finset (LacunaryCZDyadicCubeIndex d)
  | 0 => {q}
  | n + 1 => (lacunaryCZDyadicCubeDescendants q n).biUnion lacunaryCZDyadicCubeChildren

/-- The finite complete binary tree through a given depth below one dyadic cell. -/
def lacunaryCZDyadicCubeTree {d : Nat} (q : LacunaryCZDyadicCubeIndex d) : Nat →
    Finset (LacunaryCZDyadicCubeIndex d)
  | 0 => {q}
  | n + 1 => lacunaryCZDyadicCubeTree q n ∪
    (lacunaryCZDyadicCubeTree q n).biUnion lacunaryCZDyadicCubeChildren

theorem lacunaryCZDyadicCubeTree_mono {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    ∀ n, lacunaryCZDyadicCubeTree q n ⊆ lacunaryCZDyadicCubeTree q (n + 1) := by
  intro n r hr
  simp only [lacunaryCZDyadicCubeTree]
  exact Finset.mem_union_left _ hr

theorem lacunaryCZDyadicCubeDescendants_subset_tree
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    ∀ n, lacunaryCZDyadicCubeDescendants q n ⊆ lacunaryCZDyadicCubeTree q n := by
  intro n
  induction n with
  | zero => simp [lacunaryCZDyadicCubeDescendants, lacunaryCZDyadicCubeTree]
  | succ n ih =>
      intro r hr
      simp only [lacunaryCZDyadicCubeDescendants] at hr
      rcases Finset.mem_biUnion.mp hr with ⟨p, hp, hrp⟩
      simp only [lacunaryCZDyadicCubeTree]
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨p, ih hp, hrp⟩

/-- Every point of a root cell belongs to a cell at every prescribed finite
descendant depth. -/
theorem exists_lacunaryCZDyadicCubeDescendant_contains
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) (n : Nat)
    {x : Euclidean d} (hx : x ∈ lacunaryCZDyadicCube q) :
    ∃ r ∈ lacunaryCZDyadicCubeDescendants q n, x ∈ lacunaryCZDyadicCube r := by
  induction n generalizing q with
  | zero => exact ⟨q, by simp [lacunaryCZDyadicCubeDescendants], hx⟩
  | succ n ih =>
      obtain ⟨r, hr, hxr⟩ := ih q hx
      rcases Set.mem_iUnion₂.mp
        (lacunaryCZDyadicCube_subset_biUnion_children r hxr) with ⟨s, hs, hxs⟩
      refine ⟨s, ?_, hxs⟩
      simp only [lacunaryCZDyadicCubeDescendants]
      exact Finset.mem_biUnion.mpr ⟨r, hr, hs⟩

/-- Descendants at depth `n` have exactly `n` lower dyadic scales. -/
theorem lacunaryCZDyadicCubeDescendant_scale
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) (n : Nat)
    {r : LacunaryCZDyadicCubeIndex d}
    (hr : r ∈ lacunaryCZDyadicCubeDescendants q n) :
    r.scale = q.scale - n := by
  induction n generalizing r with
  | zero =>
      simp only [lacunaryCZDyadicCubeDescendants, Finset.mem_singleton] at hr
      subst r
      simp
  | succ n ih =>
      simp only [lacunaryCZDyadicCubeDescendants] at hr
      rcases Finset.mem_biUnion.mp hr with ⟨p, hp, hrp⟩
      rcases Finset.mem_image.mp hrp with ⟨e, he, her⟩
      subst r
      dsimp [lacunaryCZDyadicCubeChild]
      rw [ih hp]
      ring

theorem lacunaryCZDyadicCubeTree_scale_lower
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    ∀ n {r : LacunaryCZDyadicCubeIndex d}, r ∈ lacunaryCZDyadicCubeTree q n →
      q.scale - n ≤ r.scale := by
  intro n
  induction n with
  | zero =>
      intro r hr
      simp only [lacunaryCZDyadicCubeTree, Finset.mem_singleton] at hr
      subst r
      simp
  | succ n ih =>
      intro r hr
      simp only [lacunaryCZDyadicCubeTree] at hr
      rcases Finset.mem_union.mp hr with hr | hr
      · have h := ih hr
        omega
      · rcases Finset.mem_biUnion.mp hr with ⟨p, hp, hrp⟩
        rcases Finset.mem_image.mp hrp with ⟨e, he, her⟩
        subst r
        dsimp [lacunaryCZDyadicCubeChild]
        have h := ih hp
        omega

/-- Every nonroot cell in the finite tree has its literal parent in the
same tree. -/
theorem lacunaryCZDyadicCubeTree_parent_mem
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    ∀ n {r : LacunaryCZDyadicCubeIndex d}, r ∈ lacunaryCZDyadicCubeTree q n → r ≠ q →
      lacunaryCZDyadicCubeParent r ∈ lacunaryCZDyadicCubeTree q n := by
  intro n
  induction n with
  | zero =>
      intro r hr hneq
      simp only [lacunaryCZDyadicCubeTree, Finset.mem_singleton] at hr
      exact (hneq hr).elim
  | succ n ih =>
      intro r hr hneq
      simp only [lacunaryCZDyadicCubeTree] at hr ⊢
      rcases Finset.mem_union.mp hr with hr | hr
      · exact Finset.mem_union_left _ (ih hr hneq)
      · rcases Finset.mem_biUnion.mp hr with ⟨p, hp, hrp⟩
        rcases Finset.mem_image.mp hrp with ⟨e, he, her⟩
        subst r
        rw [lacunaryCZDyadicCubeParent_child]
        exact Finset.mem_union_left _ hp

/-- A finite forest of complete dyadic trees below a finite collection of roots. -/
def lacunaryCZDyadicCubeForest {d : Nat}
    (R : Finset (LacunaryCZDyadicCubeIndex d)) (n : Nat) :
    Finset (LacunaryCZDyadicCubeIndex d) :=
  R.biUnion fun q => lacunaryCZDyadicCubeTree q n

theorem lacunaryCZDyadicCubeForest_scale_lower
    {d : Nat} (R : Finset (LacunaryCZDyadicCubeIndex d))
    (L : ℤ) (n : Nat) (hscale : ∀ q ∈ R, q.scale = L)
    {r : LacunaryCZDyadicCubeIndex d} (hr : r ∈ lacunaryCZDyadicCubeForest R n) :
    L - n ≤ r.scale := by
  simp only [lacunaryCZDyadicCubeForest] at hr
  rcases Finset.mem_biUnion.mp hr with ⟨q, hq, hrq⟩
  rw [← hscale q hq]
  exact lacunaryCZDyadicCubeTree_scale_lower q n hrq

theorem lacunaryCZDyadicCubeForest_parent_mem_of_not_bad_roots
    {d : Nat} (R : Finset (LacunaryCZDyadicCubeIndex d)) (n : Nat)
    (bad : LacunaryCZDyadicCubeIndex d → Prop)
    (hroot : ∀ q ∈ R, ¬ bad q)
    {r : LacunaryCZDyadicCubeIndex d}
    (hr : r ∈ lacunaryCZDyadicCubeForest R n) (hrbad : bad r) :
    lacunaryCZDyadicCubeParent r ∈ lacunaryCZDyadicCubeForest R n := by
  simp only [lacunaryCZDyadicCubeForest] at hr ⊢
  rcases Finset.mem_biUnion.mp hr with ⟨q, hq, hrq⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨q, hq, ?_⟩
  apply lacunaryCZDyadicCubeTree_parent_mem q n hrq
  intro heq
  exact hroot q hq (heq ▸ hrbad)

/-- At a fixed scale, distinct coordinate dyadic cells are disjoint. -/
theorem disjoint_lacunaryCZDyadicCube_of_translation_ne
    {d : Nat} (k : ℤ) (m n : Fin d → ℤ) (hmn : m ≠ n) :
    Disjoint
      (lacunaryCZDyadicCube ⟨k, m⟩ : Set (Euclidean d))
      (lacunaryCZDyadicCube ⟨k, n⟩ : Set (Euclidean d)) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  have hcoord : ∃ i : Fin d, m i ≠ n i := by
    by_contra h
    push Not at h
    exact hmn (funext h)
  obtain ⟨i, hineq⟩ := hcoord
  change (WithLp.ofLp x) ∈ Set.pi Set.univ (fun i =>
    Set.Ico ((m i : ℝ) * (2 : ℝ) ^ k)
      (((m i + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k)) at hxm
  change (WithLp.ofLp x) ∈ Set.pi Set.univ (fun i =>
    Set.Ico ((n i : ℝ) * (2 : ℝ) ^ k)
      (((n i + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k)) at hxn
  rw [Set.mem_pi] at hxm hxn
  have hxm' := hxm i (Set.mem_univ i)
  have hxn' := hxn i (Set.mem_univ i)
  change (m i : ℝ) * (2 : ℝ) ^ k ≤ WithLp.ofLp x i ∧
    WithLp.ofLp x i < ((m i + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k at hxm'
  change (n i : ℝ) * (2 : ℝ) ^ k ≤ WithLp.ofLp x i ∧
    WithLp.ofLp x i < ((n i + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k at hxn'
  have hs : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  rcases lt_or_gt_of_ne hineq with hlt | hgt
  · have hstep : m i + 1 ≤ n i := by omega
    have hstepR : ((m i + 1 : ℤ) : ℝ) ≤ n i := by exact_mod_cast hstep
    have hbound : ((m i + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k ≤
        (n i : ℝ) * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hstepR hs.le
    exact (not_lt_of_ge (hbound.trans hxn'.1)) hxm'.2
  · have hstep : n i + 1 ≤ m i := by omega
    have hstepR : ((n i + 1 : ℤ) : ℝ) ≤ m i := by exact_mod_cast hstep
    have hbound : ((n i + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k ≤
        (m i : ℝ) * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hstepR hs.le
    exact (not_lt_of_ge (hbound.trans hxm'.1)) hxn'.2

/-- Iterated dyadic parents, used for a finite range of cell scales. -/
def lacunaryCZDyadicCubeParentIter {d : Nat} (n : ℕ)
    (q : LacunaryCZDyadicCubeIndex d) : LacunaryCZDyadicCubeIndex d :=
  (lacunaryCZDyadicCubeParent^[n]) q

/-- A cell is contained in every iterated parent. -/
theorem lacunaryCZDyadicCube_subset_parentIter
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) (n : ℕ) :
    lacunaryCZDyadicCube q ⊆
      lacunaryCZDyadicCube (lacunaryCZDyadicCubeParentIter n q) := by
  induction n with
  | zero => simp [lacunaryCZDyadicCubeParentIter]
  | succ n ih =>
      rw [lacunaryCZDyadicCubeParentIter, Function.iterate_succ_apply']
      exact ih.trans
        (lacunaryCZDyadicCube_subset_parent (lacunaryCZDyadicCubeParentIter n q))

/-- Iterating the parent raises the scale by exactly the number of steps. -/
theorem lacunaryCZDyadicCubeParentIter_scale
    {d : Nat} (n : ℕ) (q : LacunaryCZDyadicCubeIndex d) :
    (lacunaryCZDyadicCubeParentIter n q).scale = q.scale + n := by
  induction n with
  | zero => simp [lacunaryCZDyadicCubeParentIter]
  | succ n ih =>
      rw [lacunaryCZDyadicCubeParentIter, Function.iterate_succ_apply']
      change (lacunaryCZDyadicCubeParent
        (lacunaryCZDyadicCubeParentIter n q)).scale = _
      simp only [lacunaryCZDyadicCubeParent]
      rw [ih]
      push_cast
      ring

/-- Two cells at the same scale which are not disjoint are literally the
same indexed cell. -/
theorem lacunaryCZDyadicCube_eq_of_same_scale_not_disjoint
    {d : Nat} (q r : LacunaryCZDyadicCubeIndex d)
    (hscale : q.scale = r.scale)
    (hnot : ¬ Disjoint (lacunaryCZDyadicCube q) (lacunaryCZDyadicCube r)) : q = r := by
  cases q with
  | mk k m =>
    cases r with
    | mk l n =>
      dsimp at hscale hnot ⊢
      subst l
      have hmn : m = n := by
        by_contra hmn
        exact hnot (disjoint_lacunaryCZDyadicCube_of_translation_ne k m n hmn)
      subst n
      rfl

/-- The literal coordinate dyadic grid is laminar: any two intersecting
cells are nested.  This is the geometric hypothesis fed to the finite
maximal-bad-cell selection below. -/
theorem lacunaryCZDyadicCube_laminar
    {d : Nat} (q r : LacunaryCZDyadicCubeIndex d)
    (hnot : ¬ Disjoint (lacunaryCZDyadicCube q) (lacunaryCZDyadicCube r)) :
    lacunaryCZDyadicCube q ⊆ lacunaryCZDyadicCube r ∨
      lacunaryCZDyadicCube r ⊆ lacunaryCZDyadicCube q := by
  rcases le_total q.scale r.scale with hqr | hrq
  · let n : ℕ := (r.scale - q.scale).toNat
    have hn : q.scale + n = r.scale := by
      dsimp [n]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hqr)]
      ring
    have hsub := lacunaryCZDyadicCube_subset_parentIter q n
    have hscale : (lacunaryCZDyadicCubeParentIter n q).scale = r.scale := by
      rw [lacunaryCZDyadicCubeParentIter_scale, hn]
    have hnot' : ¬ Disjoint
        (lacunaryCZDyadicCube (lacunaryCZDyadicCubeParentIter n q))
        (lacunaryCZDyadicCube r) := by
      intro hdisj
      exact hnot (hdisj.mono hsub Subset.rfl)
    have heq : lacunaryCZDyadicCubeParentIter n q = r :=
      lacunaryCZDyadicCube_eq_of_same_scale_not_disjoint
        (lacunaryCZDyadicCubeParentIter n q) r hscale hnot'
    left
    simpa [heq] using hsub
  · let n : ℕ := (q.scale - r.scale).toNat
    have hn : r.scale + n = q.scale := by
      dsimp [n]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hrq)]
      ring
    have hsub := lacunaryCZDyadicCube_subset_parentIter r n
    have hscale : (lacunaryCZDyadicCubeParentIter n r).scale = q.scale := by
      rw [lacunaryCZDyadicCubeParentIter_scale, hn]
    have hnot' : ¬ Disjoint (lacunaryCZDyadicCube q)
        (lacunaryCZDyadicCube (lacunaryCZDyadicCubeParentIter n r)) := by
      intro hdisj
      exact hnot (hdisj.mono Subset.rfl hsub)
    have heq : q = lacunaryCZDyadicCubeParentIter n r :=
      lacunaryCZDyadicCube_eq_of_same_scale_not_disjoint q
        (lacunaryCZDyadicCubeParentIter n r) hscale.symm hnot'
    right
    simpa [heq] using hsub

/-- The complex average of an input over a concrete dyadic cell. -/
def lacunaryCZDyadicCubeAverage {d : Nat} (f : Euclidean d → ℂ)
    (q : LacunaryCZDyadicCubeIndex d) : ℂ :=
  (volume (lacunaryCZDyadicCube q)).toReal⁻¹ •
    ∫ x in lacunaryCZDyadicCube q, f x

/-- The mean-zero atom attached to one dyadic cell. -/
def lacunaryCZDyadicCubeBadAtom {d : Nat} (f : Euclidean d → ℂ)
    (q : LacunaryCZDyadicCubeIndex d) : Euclidean d → ℂ :=
  (lacunaryCZDyadicCube q).indicator
    (fun x => f x - lacunaryCZDyadicCubeAverage f q)

theorem volume_lacunaryCZDyadicCube_pos
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    0 < volume (lacunaryCZDyadicCube q) := by
  rw [volume_lacunaryCZDyadicCube]
  apply ENNReal.pow_pos
  exact ENNReal.ofReal_pos.mpr (zpow_pos (by norm_num) _)

theorem volume_lacunaryCZDyadicCube_ne_top
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    volume (lacunaryCZDyadicCube q) ≠ ⊤ := by
  rw [volume_lacunaryCZDyadicCube]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

/-- In positive dimension, a concrete dyadic cell determines both of its
integer grid parameters. -/
theorem lacunaryCZDyadicCube_injective
    {d : Nat} [NeZero d] :
    Function.Injective (lacunaryCZDyadicCube :
      LacunaryCZDyadicCubeIndex d → Set (Euclidean d)) := by
  intro q r h
  have hvol : volume (lacunaryCZDyadicCube q) = volume (lacunaryCZDyadicCube r) :=
    congrArg volume h
  rw [volume_lacunaryCZDyadicCube, volume_lacunaryCZDyadicCube] at hvol
  have hreal := congrArg ENNReal.toReal hvol
  have hqnonneg : 0 ≤ (2 : ℝ) ^ q.scale := (zpow_pos (by norm_num) _).le
  have hrnonneg : 0 ≤ (2 : ℝ) ^ r.scale := (zpow_pos (by norm_num) _).le
  have hpows : ((2 : ℝ) ^ q.scale) ^ d = ((2 : ℝ) ^ r.scale) ^ d := by
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hqnonneg,
      ENNReal.toReal_ofReal hrnonneg] using hreal
  have hsides : (2 : ℝ) ^ q.scale = (2 : ℝ) ^ r.scale :=
    (pow_left_inj₀ hqnonneg hrnonneg (NeZero.ne d)).mp hpows
  have hscale : q.scale = r.scale :=
    zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) hsides
  have hnonempty : (lacunaryCZDyadicCube r).Nonempty := by
    by_contra hempty
    have heq : lacunaryCZDyadicCube r = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    have hpos := volume_lacunaryCZDyadicCube_pos r
    rw [heq] at hpos
    simp at hpos
  have hnot : ¬ Disjoint (lacunaryCZDyadicCube q) (lacunaryCZDyadicCube r) := by
    intro hdis
    rw [h] at hdis
    obtain ⟨x, hx⟩ := hnonempty
    exact Set.disjoint_left.1 hdis hx hx
  exact lacunaryCZDyadicCube_eq_of_same_scale_not_disjoint q r hscale hnot

/-- Every literal dyadic cell is a strict subset of its dyadic parent. -/
theorem lacunaryCZDyadicCube_ssub_parent
    {d : Nat} [NeZero d] (q : LacunaryCZDyadicCubeIndex d) :
    lacunaryCZDyadicCube q ⊂ lacunaryCZDyadicCube (lacunaryCZDyadicCubeParent q) := by
  refine ⟨lacunaryCZDyadicCube_subset_parent q, ?_⟩
  intro hrev
  have heqset : lacunaryCZDyadicCube q =
      lacunaryCZDyadicCube (lacunaryCZDyadicCubeParent q) :=
    Set.Subset.antisymm (lacunaryCZDyadicCube_subset_parent q) hrev
  have heq := lacunaryCZDyadicCube_injective heqset
  have hscale := congrArg LacunaryCZDyadicCubeIndex.scale heq
  dsimp [lacunaryCZDyadicCubeParent] at hscale
  omega

theorem lacunaryCZDyadicCube_nonempty
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    (lacunaryCZDyadicCube q).Nonempty := by
  by_contra hempty
  have heq : lacunaryCZDyadicCube q = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hempty
  have hpos := volume_lacunaryCZDyadicCube_pos q
  rw [heq] at hpos
  simp at hpos

/-- If two intersecting cells have ordered scales, the smaller-scale cell is
contained in the larger-scale one. -/
theorem lacunaryCZDyadicCube_subset_of_scale_le
    {d : Nat} (q r : LacunaryCZDyadicCubeIndex d) (hqr : q.scale ≤ r.scale)
    (hnot : ¬ Disjoint (lacunaryCZDyadicCube q) (lacunaryCZDyadicCube r)) :
    lacunaryCZDyadicCube q ⊆ lacunaryCZDyadicCube r := by
  let n : ℕ := (r.scale - q.scale).toNat
  have hn : q.scale + n = r.scale := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hqr)]
    ring
  have hsub := lacunaryCZDyadicCube_subset_parentIter q n
  have hscale : (lacunaryCZDyadicCubeParentIter n q).scale = r.scale := by
    rw [lacunaryCZDyadicCubeParentIter_scale, hn]
  have hnot' : ¬ Disjoint
      (lacunaryCZDyadicCube (lacunaryCZDyadicCubeParentIter n q))
      (lacunaryCZDyadicCube r) := by
    intro hdisj
    exact hnot (hdisj.mono hsub Subset.rfl)
  have heq : lacunaryCZDyadicCubeParentIter n q = r :=
    lacunaryCZDyadicCube_eq_of_same_scale_not_disjoint
      (lacunaryCZDyadicCubeParentIter n q) r hscale hnot'
  simpa [heq] using hsub

/-- Strict containment of literal dyadic cells strictly raises the scale. -/
theorem lacunaryCZDyadicCube_scale_lt_of_ssub
    {d : Nat} (q r : LacunaryCZDyadicCubeIndex d)
    (hsub : lacunaryCZDyadicCube q ⊂ lacunaryCZDyadicCube r) :
    q.scale < r.scale := by
  have hnot : ¬ Disjoint (lacunaryCZDyadicCube q) (lacunaryCZDyadicCube r) := by
    intro hdis
    obtain ⟨x, hx⟩ := lacunaryCZDyadicCube_nonempty q
    exact Set.disjoint_left.1 hdis hx (hsub.1 hx)
  by_contra hlt
  have hrq : r.scale ≤ q.scale := le_of_not_gt hlt
  have hnotrq : ¬ Disjoint (lacunaryCZDyadicCube r) (lacunaryCZDyadicCube q) := by
    intro hdis
    exact hnot hdis.symm
  have hrev := lacunaryCZDyadicCube_subset_of_scale_le r q hrq hnotrq
  exact hsub.2 hrev

/-- A lower scale cutoff turns the integer dyadic scale into a strict finite
stopping-time rank. -/
theorem lacunaryCZDyadicCube_rank_strict
    {d : Nat} (K : ℤ) (q r : LacunaryCZDyadicCubeIndex d)
    (hq : K ≤ q.scale) (hr : K ≤ r.scale)
    (hsub : lacunaryCZDyadicCube q ⊂ lacunaryCZDyadicCube r) :
    (q.scale - K).toNat < (r.scale - K).toNat := by
  rw [← Int.ofNat_lt, Int.toNat_of_nonneg (sub_nonneg.mpr hq),
    Int.toNat_of_nonneg (sub_nonneg.mpr hr)]
  exact sub_lt_sub_right (lacunaryCZDyadicCube_scale_lt_of_ssub q r hsub) K

/-- A dyadic-cell atom is integrable whenever the input is. -/
theorem integrable_lacunaryCZDyadicCubeBadAtom
    {d : Nat} (f : Euclidean d → ℂ) (q : LacunaryCZDyadicCubeIndex d)
    (hf : Integrable f volume) :
    Integrable (lacunaryCZDyadicCubeBadAtom f q) volume := by
  unfold lacunaryCZDyadicCubeBadAtom
  apply IntegrableOn.integrable_indicator
  · exact hf.integrableOn.sub
      (integrableOn_const (volume_lacunaryCZDyadicCube_ne_top q))
  · exact measurableSet_lacunaryCZDyadicCube q

/-- A dyadic-cell atom has zero total mass. -/
theorem integral_lacunaryCZDyadicCubeBadAtom_eq_zero
    {d : Nat} (f : Euclidean d → ℂ) (q : LacunaryCZDyadicCubeIndex d)
    (hf : Integrable f volume) :
    (∫ x, lacunaryCZDyadicCubeBadAtom f q x) = 0 := by
  let C : Set (Euclidean d) := lacunaryCZDyadicCube q
  let A : ℂ := lacunaryCZDyadicCubeAverage f q
  have hC : MeasurableSet C := measurableSet_lacunaryCZDyadicCube q
  have hvolpos : 0 < volume C := volume_lacunaryCZDyadicCube_pos q
  have hvoltop : volume C ≠ ⊤ := volume_lacunaryCZDyadicCube_ne_top q
  have hV : 0 < (volume C).toReal := ENNReal.toReal_pos hvolpos.ne' hvoltop
  have hfC : IntegrableOn f C volume := hf.integrableOn
  have hAC : IntegrableOn (fun _ : Euclidean d => A) C volume :=
    integrableOn_const hvoltop
  change (∫ x, C.indicator (fun x => f x - A) x) = 0
  rw [integral_indicator hC, integral_sub hfC hAC, setIntegral_const]
  change (∫ x in C, f x) - (volume C).toReal •
      ((volume C).toReal⁻¹ • ∫ x in C, f x) = 0
  rw [← mul_smul, mul_inv_cancel₀ hV.ne', one_smul, sub_self]

/-- The support of a dyadic-cell atom is its generating cell. -/
theorem lacunaryCZDyadicCubeBadAtom_support
    {d : Nat} (f : Euclidean d → ℂ) (q : LacunaryCZDyadicCubeIndex d)
    {x : Euclidean d} (hx : lacunaryCZDyadicCubeBadAtom f q x ≠ 0) :
    x ∈ lacunaryCZDyadicCube q := by
  contrapose! hx
  simp [lacunaryCZDyadicCubeBadAtom, hx]

/-- The lower-left corner of a literal dyadic cell, viewed as its cancellation
centre. -/
def lacunaryCZDyadicCubeCenter {d : Nat}
    (q : LacunaryCZDyadicCubeIndex d) : Euclidean d :=
  WithLp.toLp 2 (fun i =>
    (q.translation i : ℝ) * (2 : ℝ) ^ q.scale)

/-- A convenient enclosing radius for a literal dyadic cell. -/
def lacunaryCZDyadicCubeRadius {d : Nat}
    (q : LacunaryCZDyadicCubeIndex d) : ℝ :=
  (d : ℝ) * (2 : ℝ) ^ q.scale

theorem lacunaryCZDyadicCubeRadius_pos
    {d : Nat} [NeZero d] (q : LacunaryCZDyadicCubeIndex d) :
    0 < lacunaryCZDyadicCubeRadius q := by
  unfold lacunaryCZDyadicCubeRadius
  exact mul_pos (by exact_mod_cast Nat.pos_iff_ne_zero.mpr (NeZero.ne d))
    (zpow_pos (by norm_num) _)

/-- Every point of a dyadic cell lies within its explicit enclosing radius of
the chosen corner. -/
theorem mem_lacunaryCZDyadicCube_dist_center_le_radius
    {d : Nat} [NeZero d] (q : LacunaryCZDyadicCubeIndex d)
    {x : Euclidean d} (hx : x ∈ lacunaryCZDyadicCube q) :
    ‖x - lacunaryCZDyadicCubeCenter q‖ ≤ lacunaryCZDyadicCubeRadius q := by
  let s : ℝ := (2 : ℝ) ^ q.scale
  let c : Euclidean d := lacunaryCZDyadicCubeCenter q
  have hs : 0 < s := by
    dsimp [s]
    exact zpow_pos (by norm_num) _
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  change (WithLp.ofLp x) ∈ Set.pi Set.univ (fun i =>
    Set.Ico ((q.translation i : ℝ) * s)
      (((q.translation i + 1 : ℤ) : ℝ) * s)) at hx
  rw [Set.mem_pi] at hx
  have hcoord (i : Fin d) : (WithLp.ofLp (x - c) i) ^ 2 ≤ s ^ 2 := by
    have hxi := hx i (Set.mem_univ i)
    change (q.translation i : ℝ) * s ≤ WithLp.ofLp x i ∧
      WithLp.ofLp x i < ((q.translation i + 1 : ℤ) : ℝ) * s at hxi
    change (WithLp.ofLp x i - (q.translation i : ℝ) * s) ^ 2 ≤ s ^ 2
    rw [Int.cast_add, Int.cast_one] at hxi
    nlinarith
  have hsum : ‖x - c‖ ^ 2 ≤ (d : ℝ) * s ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i, (x - c).ofLp i ^ 2 ≤ ∑ _i : Fin d, s ^ 2 :=
        Finset.sum_le_sum fun i hi => hcoord i
      _ = (d : ℝ) * s ^ 2 := by simp
  have hrad : (d : ℝ) * s ^ 2 ≤ ((d : ℝ) * s) ^ 2 := by
    nlinarith [sq_nonneg s]
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg d) hs.le)).mp
  change ‖x - c‖ ^ 2 ≤ ((d : ℝ) * s) ^ 2
  exact hsum.trans hrad

/-- The diameter of a literal dyadic cell is bounded by twice the enclosing
radius used for its cancellation atom. -/
theorem lacunaryCZDyadicCube_dist_le_two_radius
    {d : Nat} [NeZero d] (q : LacunaryCZDyadicCubeIndex d)
    {x y : Euclidean d}
    (hx : x ∈ lacunaryCZDyadicCube q) (hy : y ∈ lacunaryCZDyadicCube q) :
    dist x y ≤ 2 * lacunaryCZDyadicCubeRadius q := by
  have hxc := mem_lacunaryCZDyadicCube_dist_center_le_radius q hx
  have hyc := mem_lacunaryCZDyadicCube_dist_center_le_radius q hy
  rw [dist_eq_norm_sub]
  calc
    ‖x - y‖ = ‖(x - lacunaryCZDyadicCubeCenter q) -
        (y - lacunaryCZDyadicCubeCenter q)‖ := by
      congr 1
      abel
    _ ≤ ‖x - lacunaryCZDyadicCubeCenter q‖ +
        ‖y - lacunaryCZDyadicCubeCenter q‖ := norm_sub_le _ _
    _ ≤ lacunaryCZDyadicCubeRadius q + lacunaryCZDyadicCubeRadius q :=
      add_le_add hxc hyc
    _ = 2 * lacunaryCZDyadicCubeRadius q := by ring

/-- The concrete cube atom has the enclosing-ball support condition consumed
by the global cancellation estimates. -/
theorem lacunaryCZDyadicCubeBadAtom_dist_center_le_radius
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ)
    (q : LacunaryCZDyadicCubeIndex d) {x : Euclidean d}
    (hx : lacunaryCZDyadicCubeBadAtom f q x ≠ 0) :
    ‖x - lacunaryCZDyadicCubeCenter q‖ ≤ lacunaryCZDyadicCubeRadius q :=
  mem_lacunaryCZDyadicCube_dist_center_le_radius q
    (lacunaryCZDyadicCubeBadAtom_support f q hx)

/-- The norm of a dyadic-cell average is bounded by the average of the
norm. -/
theorem norm_lacunaryCZDyadicCubeAverage_le_setIntegral_norm
    {d : Nat} (f : Euclidean d → ℂ) (q : LacunaryCZDyadicCubeIndex d)
    (_hf : Integrable f volume) :
    ‖lacunaryCZDyadicCubeAverage f q‖ ≤
      (volume (lacunaryCZDyadicCube q)).toReal⁻¹ *
        ∫ x in lacunaryCZDyadicCube q, ‖f x‖ := by
  let C : Set (Euclidean d) := lacunaryCZDyadicCube q
  have hinv : 0 ≤ (volume C).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hint : ‖∫ x in C, f x‖ ≤ ∫ x in C, ‖f x‖ :=
    norm_integral_le_integral_norm (μ := volume.restrict C) f
  change ‖(volume C).toReal⁻¹ • ∫ x in C, f x‖ ≤
    (volume C).toReal⁻¹ * ∫ x in C, ‖f x‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
  exact mul_le_mul_of_nonneg_left hint hinv

/-- One dyadic-cell atom costs at most twice the `L¹` mass of the input on
its cell. -/
theorem integral_norm_lacunaryCZDyadicCubeBadAtom_le_two_mul_setIntegral_norm
    {d : Nat} (f : Euclidean d → ℂ) (q : LacunaryCZDyadicCubeIndex d)
    (hf : Integrable f volume) :
    (∫ x, ‖lacunaryCZDyadicCubeBadAtom f q x‖) ≤
      2 * ∫ x in lacunaryCZDyadicCube q, ‖f x‖ := by
  let C : Set (Euclidean d) := lacunaryCZDyadicCube q
  let A : ℂ := lacunaryCZDyadicCubeAverage f q
  have hC : MeasurableSet C := measurableSet_lacunaryCZDyadicCube q
  have hvolpos : 0 < volume C := volume_lacunaryCZDyadicCube_pos q
  have hvoltop : volume C ≠ ⊤ := volume_lacunaryCZDyadicCube_ne_top q
  have hV : 0 < (volume C).toReal := ENNReal.toReal_pos hvolpos.ne' hvoltop
  have hfC : IntegrableOn f C volume := hf.integrableOn
  have hAC : IntegrableOn (fun _ : Euclidean d => A) C volume :=
    integrableOn_const hvoltop
  have hsub : IntegrableOn (fun x : Euclidean d => f x - A) C volume :=
    hfC.sub hAC
  have hright : IntegrableOn (fun x : Euclidean d => ‖f x‖ + ‖A‖) C volume :=
    hfC.norm.add hAC.norm
  have hmono : (∫ x in C, ‖f x - A‖) ≤ ∫ x in C, ‖f x‖ + ‖A‖ :=
    integral_mono hsub.norm hright fun x => norm_sub_le _ _
  have havg : ‖A‖ ≤ (volume C).toReal⁻¹ * ∫ x in C, ‖f x‖ := by
    simpa only [A, C] using
      norm_lacunaryCZDyadicCubeAverage_le_setIntegral_norm f q hf
  have hscale : (volume C).toReal * ‖A‖ ≤ ∫ x in C, ‖f x‖ := by
    calc
      (volume C).toReal * ‖A‖ ≤
          (volume C).toReal * ((volume C).toReal⁻¹ * ∫ x in C, ‖f x‖) :=
        mul_le_mul_of_nonneg_left havg ENNReal.toReal_nonneg
      _ = ∫ x in C, ‖f x‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]
  calc
    (∫ x, ‖lacunaryCZDyadicCubeBadAtom f q x‖) = ∫ x in C, ‖f x - A‖ := by
      rw [show (fun x : Euclidean d => ‖lacunaryCZDyadicCubeBadAtom f q x‖) =
          C.indicator (fun x => ‖f x - A‖) by
        funext x
        by_cases hx : x ∈ C <;>
          simp [lacunaryCZDyadicCubeBadAtom, C, A, hx]]
      exact integral_indicator hC
    _ ≤ ∫ x in C, ‖f x‖ + ‖A‖ := hmono
    _ = (∫ x in C, ‖f x‖) + (volume C).toReal * ‖A‖ := by
      rw [integral_add hfC.norm hAC.norm, setIntegral_const]
      simp only [Measure.real, smul_eq_mul]
    _ ≤ (∫ x in C, ‖f x‖) + (∫ x in C, ‖f x‖) :=
      add_le_add_right hscale _
    _ = 2 * ∫ x in C, ‖f x‖ := by ring

/-- Disjoint selected dyadic cells make the `L¹` costs of their atoms add
without loss. -/
theorem sum_integral_norm_lacunaryCZDyadicCubeBadAtom_le_two_mul_integral_norm
    {d : Nat} (f : Euclidean d → ℂ) (U : Finset (LacunaryCZDyadicCubeIndex d))
    (hdisj : (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
      lacunaryCZDyadicCube)
    (hf : Integrable f volume) :
    (∑ q ∈ U, ∫ x, ‖lacunaryCZDyadicCubeBadAtom f q x‖) ≤
      2 * ∫ x, ‖f x‖ := by
  have hsum : (∑ q ∈ U, ∫ x, ‖lacunaryCZDyadicCubeBadAtom f q x‖) ≤
      2 * (∑ q ∈ U, ∫ x in lacunaryCZDyadicCube q, ‖f x‖) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq =>
      integral_norm_lacunaryCZDyadicCubeBadAtom_le_two_mul_setIntegral_norm f q hf
  have hunion :
      (∑ q ∈ U, ∫ x in lacunaryCZDyadicCube q, ‖f x‖) =
        ∫ x in ⋃ q ∈ U, lacunaryCZDyadicCube q, ‖f x‖ := by
    symm
    exact integral_biUnion_finset U
      (fun _ _ => measurableSet_lacunaryCZDyadicCube _) hdisj
      (fun _ _ => hf.norm.integrableOn)
  have hglobal : (∫ x in ⋃ q ∈ U, lacunaryCZDyadicCube q, ‖f x‖) ≤
      ∫ x, ‖f x‖ :=
    setIntegral_le_integral hf.norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  calc
    (∑ q ∈ U, ∫ x, ‖lacunaryCZDyadicCubeBadAtom f q x‖) ≤
        2 * (∑ q ∈ U, ∫ x in lacunaryCZDyadicCube q, ‖f x‖) := hsum
    _ = 2 * ∫ x in ⋃ q ∈ U, lacunaryCZDyadicCube q, ‖f x‖ := by rw [hunion]
    _ ≤ 2 * ∫ x, ‖f x‖ :=
      mul_le_mul_of_nonneg_left hglobal (by norm_num)

/-- The good term for a finite selected family of dyadic cells. -/
def lacunaryCZDyadicCubeGoodPart {d : Nat} (f : Euclidean d → ℂ)
    (U : Finset (LacunaryCZDyadicCubeIndex d)) : Euclidean d → ℂ :=
  fun x => f x - ∑ q ∈ U, lacunaryCZDyadicCubeBadAtom f q x

/-- On a selected cell the good part is its corresponding cell average. -/
theorem lacunaryCZDyadicCubeGoodPart_eq_average_of_mem
    {d : Nat} (f : Euclidean d → ℂ)
    (U : Finset (LacunaryCZDyadicCubeIndex d))
    (hdisj : (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
      lacunaryCZDyadicCube)
    {q : LacunaryCZDyadicCubeIndex d} (hq : q ∈ U) {x : Euclidean d}
    (hx : x ∈ lacunaryCZDyadicCube q) :
    lacunaryCZDyadicCubeGoodPart f U x = lacunaryCZDyadicCubeAverage f q := by
  have hsum : (∑ r ∈ U, lacunaryCZDyadicCubeBadAtom f r x) =
      lacunaryCZDyadicCubeBadAtom f q x := by
    rw [Finset.sum_eq_single q]
    · intro r hr hrq
      have hdis : Disjoint (lacunaryCZDyadicCube q) (lacunaryCZDyadicCube r) :=
        hdisj hq hr hrq.symm
      have hxr : x ∉ lacunaryCZDyadicCube r := by
        intro hxr
        exact Set.disjoint_left.1 hdis hx hxr
      simp only [lacunaryCZDyadicCubeBadAtom, Set.indicator_of_notMem hxr]
    · intro hnot
      exact (hnot hq).elim
  rw [lacunaryCZDyadicCubeGoodPart, hsum]
  simp only [lacunaryCZDyadicCubeBadAtom, Set.indicator_of_mem hx]
  ring

/-- Away from all selected cells, the good part agrees with the input. -/
theorem lacunaryCZDyadicCubeGoodPart_eq_of_not_mem_biUnion
    {d : Nat} (f : Euclidean d → ℂ)
    (U : Finset (LacunaryCZDyadicCubeIndex d)) {x : Euclidean d}
    (hx : x ∉ ⋃ q ∈ U, lacunaryCZDyadicCube q) :
    lacunaryCZDyadicCubeGoodPart f U x = f x := by
  have hsum : (∑ q ∈ U, lacunaryCZDyadicCubeBadAtom f q x) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hxq : x ∉ lacunaryCZDyadicCube q := by
      intro hxq
      apply hx
      exact Set.mem_iUnion₂.mpr ⟨q, hq, hxq⟩
    simp only [lacunaryCZDyadicCubeBadAtom, Set.indicator_of_notMem hxq]
  simp only [lacunaryCZDyadicCubeGoodPart, hsum, sub_zero]

/-- Literal outside and selected-average bounds give the `L∞` bound for the
finite dyadic good part. -/
theorem norm_lacunaryCZDyadicCubeGoodPart_le_of_outside_and_average_bounds
    {d : Nat} (f : Euclidean d → ℂ) (U : Finset (LacunaryCZDyadicCubeIndex d))
    (hdisj : (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
      lacunaryCZDyadicCube)
    (lambda : ℝ)
    (houtside : ∀ x : Euclidean d,
      x ∉ ⋃ q ∈ U, lacunaryCZDyadicCube q → ‖f x‖ ≤ lambda)
    (haverage : ∀ q ∈ U, ‖lacunaryCZDyadicCubeAverage f q‖ ≤ lambda)
    (x : Euclidean d) :
    ‖lacunaryCZDyadicCubeGoodPart f U x‖ ≤ lambda := by
  by_cases hx : x ∈ ⋃ q ∈ U, lacunaryCZDyadicCube q
  · rcases Set.mem_iUnion₂.mp hx with ⟨q, hq, hxq⟩
    rw [lacunaryCZDyadicCubeGoodPart_eq_average_of_mem f U hdisj hq hxq]
    exact haverage q hq
  · rw [lacunaryCZDyadicCubeGoodPart_eq_of_not_mem_biUnion f U hx]
    exact houtside x hx

/-- The finite dyadic good part has `L¹` mass at most three times that of
the input. -/
theorem integral_norm_lacunaryCZDyadicCubeGoodPart_le_three_mul_integral_norm
    {d : Nat} (f : Euclidean d → ℂ) (U : Finset (LacunaryCZDyadicCubeIndex d))
    (hdisj : (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
      lacunaryCZDyadicCube)
    (hf : Integrable f volume) :
    (∫ x, ‖lacunaryCZDyadicCubeGoodPart f U x‖) ≤ 3 * ∫ x, ‖f x‖ := by
  have hgoodint : Integrable (lacunaryCZDyadicCubeGoodPart f U) volume := by
    unfold lacunaryCZDyadicCubeGoodPart
    apply hf.sub
    exact integrable_finsetSum U fun q _ =>
      integrable_lacunaryCZDyadicCubeBadAtom f q hf
  have hsumint : Integrable (fun x : Euclidean d =>
      ∑ q ∈ U, ‖lacunaryCZDyadicCubeBadAtom f q x‖) volume :=
    integrable_finsetSum U fun q _ =>
      (integrable_lacunaryCZDyadicCubeBadAtom f q hf).norm
  have hright : Integrable (fun x : Euclidean d =>
      ‖f x‖ + ∑ q ∈ U, ‖lacunaryCZDyadicCubeBadAtom f q x‖) volume :=
    hf.norm.add hsumint
  have hpoint (x : Euclidean d) :
      ‖lacunaryCZDyadicCubeGoodPart f U x‖ ≤
        ‖f x‖ + ∑ q ∈ U, ‖lacunaryCZDyadicCubeBadAtom f q x‖ := by
    unfold lacunaryCZDyadicCubeGoodPart
    exact (norm_sub_le _ _).trans
      (add_le_add_right (norm_sum_le U fun q => lacunaryCZDyadicCubeBadAtom f q x) _)
  have hmono : (∫ x, ‖lacunaryCZDyadicCubeGoodPart f U x‖) ≤
      ∫ x, ‖f x‖ + ∑ q ∈ U, ‖lacunaryCZDyadicCubeBadAtom f q x‖ :=
    integral_mono hgoodint.norm hright hpoint
  have hbad :=
    sum_integral_norm_lacunaryCZDyadicCubeBadAtom_le_two_mul_integral_norm
      f U hdisj hf
  calc
    (∫ x, ‖lacunaryCZDyadicCubeGoodPart f U x‖) ≤
        ∫ x, ‖f x‖ + ∑ q ∈ U, ‖lacunaryCZDyadicCubeBadAtom f q x‖ := hmono
    _ = (∫ x, ‖f x‖) +
        ∑ q ∈ U, ∫ x, ‖lacunaryCZDyadicCubeBadAtom f q x‖ := by
      rw [integral_add hf.norm hsumint,
        integral_finsetSum U fun q _ =>
          (integrable_lacunaryCZDyadicCubeBadAtom f q hf).norm]
    _ ≤ (∫ x, ‖f x‖) + 2 * ∫ x, ‖f x‖ := add_le_add_right hbad _
    _ = 3 * ∫ x, ‖f x‖ := by ring

/-- Combining the finite `L∞` and `L¹` bounds gives the `L²` estimate needed
by the lacunary endpoint argument. -/
theorem integral_norm_sq_lacunaryCZDyadicCubeGoodPart_le_three_mul_lambda_mul_integral_norm
    {d : Nat} (f : Euclidean d → ℂ) (U : Finset (LacunaryCZDyadicCubeIndex d))
    (hdisj : (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
      lacunaryCZDyadicCube)
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (houtside : ∀ x : Euclidean d,
      x ∉ ⋃ q ∈ U, lacunaryCZDyadicCube q → ‖f x‖ ≤ lambda)
    (haverage : ∀ q ∈ U, ‖lacunaryCZDyadicCubeAverage f q‖ ≤ lambda)
    (hf : Integrable f volume) :
    (∫ x, ‖lacunaryCZDyadicCubeGoodPart f U x‖ ^ 2) ≤
      (3 * lambda) * ∫ x, ‖f x‖ := by
  have hgoodint : Integrable (lacunaryCZDyadicCubeGoodPart f U) volume := by
    unfold lacunaryCZDyadicCubeGoodPart
    apply hf.sub
    exact integrable_finsetSum U fun q _ =>
      integrable_lacunaryCZDyadicCubeBadAtom f q hf
  have hbound (x : Euclidean d) : ‖lacunaryCZDyadicCubeGoodPart f U x‖ ≤ lambda :=
    norm_lacunaryCZDyadicCubeGoodPart_le_of_outside_and_average_bounds
      f U hdisj lambda houtside haverage x
  have hright : Integrable (fun x : Euclidean d =>
      lambda * ‖lacunaryCZDyadicCubeGoodPart f U x‖) volume :=
    hgoodint.norm.const_mul lambda
  have hleft : Integrable (fun x : Euclidean d =>
      ‖lacunaryCZDyadicCubeGoodPart f U x‖ ^ 2) volume := by
    refine hright.mono' (hgoodint.norm.aestronglyMeasurable.pow 2) ?_
    filter_upwards with x
    have hnorm : 0 ≤ ‖lacunaryCZDyadicCubeGoodPart f U x‖ := norm_nonneg _
    have hpoint' : ‖lacunaryCZDyadicCubeGoodPart f U x‖ ^ 2 ≤
        lambda * ‖lacunaryCZDyadicCubeGoodPart f U x‖ := by
      calc
        ‖lacunaryCZDyadicCubeGoodPart f U x‖ ^ 2 =
            ‖lacunaryCZDyadicCubeGoodPart f U x‖ *
              ‖lacunaryCZDyadicCubeGoodPart f U x‖ := by ring
        _ ≤ lambda * ‖lacunaryCZDyadicCubeGoodPart f U x‖ :=
          mul_le_mul_of_nonneg_right (hbound x) hnorm
    simpa only [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (mul_nonneg hlambda hnorm)] using hpoint'
  have hpoint (x : Euclidean d) :
      ‖lacunaryCZDyadicCubeGoodPart f U x‖ ^ 2 ≤
        lambda * ‖lacunaryCZDyadicCubeGoodPart f U x‖ := by
    have hnorm : 0 ≤ ‖lacunaryCZDyadicCubeGoodPart f U x‖ := norm_nonneg _
    calc
      ‖lacunaryCZDyadicCubeGoodPart f U x‖ ^ 2 =
          ‖lacunaryCZDyadicCubeGoodPart f U x‖ *
            ‖lacunaryCZDyadicCubeGoodPart f U x‖ := by ring
      _ ≤ lambda * ‖lacunaryCZDyadicCubeGoodPart f U x‖ :=
        mul_le_mul_of_nonneg_right (hbound x) hnorm
  have hL1 :=
    integral_norm_lacunaryCZDyadicCubeGoodPart_le_three_mul_integral_norm f U hdisj hf
  calc
    (∫ x, ‖lacunaryCZDyadicCubeGoodPart f U x‖ ^ 2) ≤
        ∫ x, lambda * ‖lacunaryCZDyadicCubeGoodPart f U x‖ :=
      integral_mono hleft hright hpoint
    _ = lambda * ∫ x, ‖lacunaryCZDyadicCubeGoodPart f U x‖ := by
      rw [integral_const_mul]
    _ ≤ lambda * (3 * ∫ x, ‖f x‖) :=
      mul_le_mul_of_nonneg_left hL1 hlambda
    _ = (3 * lambda) * ∫ x, ‖f x‖ := by ring

/-- The finite dyadic good--bad decomposition is a pointwise identity. -/
theorem lacunaryCZDyadicCubeGoodPart_add_sum_eq
    {d : Nat} (f : Euclidean d → ℂ) (U : Finset (LacunaryCZDyadicCubeIndex d))
    (x : Euclidean d) :
    f x = lacunaryCZDyadicCubeGoodPart f U x +
      ∑ q ∈ U, lacunaryCZDyadicCubeBadAtom f q x := by
  simp only [lacunaryCZDyadicCubeGoodPart]
  ring

theorem integrable_lacunaryCZDyadicCubeGoodPart
    {d : Nat} (f : Euclidean d → ℂ) (U : Finset (LacunaryCZDyadicCubeIndex d))
    (hf : Integrable f volume) :
    Integrable (lacunaryCZDyadicCubeGoodPart f U) volume := by
  unfold lacunaryCZDyadicCubeGoodPart
  apply hf.sub
  exact integrable_finsetSum _ fun q _ =>
    integrable_lacunaryCZDyadicCubeBadAtom f q hf


/-- Finite stopping-time selection for a laminar family.  A cell is selected
exactly when it is bad and has maximal rank among its bad supersets.  This is
the combinatorial core of a finite dyadic-cube Calderón--Zygmund
decomposition; the subsequent geometric construction instantiates `C` with
dyadic cubes. -/
theorem exists_finset_laminar_maximal_bad_selection
    {X ι : Type*} (I : Finset ι) (C : ι → Set X) (bad : ι → Prop)
    (rank : ι → ℕ)
    (hlaminar : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ Disjoint (C i) (C j) → C i ⊆ C j ∨ C j ⊆ C i)
    (hrank : ∀ i ∈ I, ∀ j ∈ I, C i ⊂ C j → rank i < rank j)
    (hinjective : ∀ i ∈ I, ∀ j ∈ I, C i = C j → i = j) :
    ∃ U : Finset ι, U ⊆ I ∧
      (∀ i ∈ U, bad i) ∧
      (↑U : Set ι).PairwiseDisjoint C ∧
      (∀ i ∈ I, bad i → ∃ j ∈ U, C i ⊆ C j) ∧
      (∀ i ∈ U, ∀ j ∈ I, C i ⊂ C j → ¬ bad j) := by
  classical
  let U : Finset ι := I.filter fun i => bad i ∧
    ∀ j ∈ I, bad j → C i ⊆ C j → rank j ≤ rank i
  have hUsub : U ⊆ I := Finset.filter_subset _ _
  have hUprop {i : ι} (hi : i ∈ U) : bad i ∧
      ∀ j ∈ I, bad j → C i ⊆ C j → rank j ≤ rank i :=
    (Finset.mem_filter.mp hi).2
  refine ⟨U, hUsub, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (hUprop hi).1
  · intro i hi j hj hij
    have hiI : i ∈ I := hUsub hi
    have hjI : j ∈ I := hUsub hj
    have hbadI : bad i := (hUprop hi).1
    have hbadJ : bad j := (hUprop hj).1
    by_contra hdis
    rcases hlaminar i hiI j hjI hij hdis with hsub | hsub
    · have hstrict : C i ⊂ C j := by
        refine ⟨hsub, ?_⟩
        intro hrev
        have heq : C i = C j := Set.Subset.antisymm hsub hrev
        exact hij (hinjective i hiI j hjI heq)
      have hlt : rank i < rank j := hrank i hiI j hjI hstrict
      have hle : rank j ≤ rank i := (hUprop hi).2 j hjI hbadJ hsub
      exact (not_lt_of_ge hle hlt)
    · have hstrict : C j ⊂ C i := by
        refine ⟨hsub, ?_⟩
        intro hrev
        have heq : C j = C i := Set.Subset.antisymm hsub hrev
        exact hij.symm (hinjective j hjI i hiI heq)
      have hlt : rank j < rank i := hrank j hjI i hiI hstrict
      have hle : rank i ≤ rank j := (hUprop hj).2 i hiI hbadI hsub
      exact (not_lt_of_ge hle hlt)
  · intro i hiI hbadI
    let S : Finset ι := I.filter fun j => bad j ∧ C i ⊆ C j
    have hiS : i ∈ S := by
      exact Finset.mem_filter.mpr ⟨hiI, hbadI, subset_rfl⟩
    obtain ⟨j, hjS, hjmax⟩ := S.exists_max_image rank ⟨i, hiS⟩
    have hjdata : j ∈ I ∧ bad j ∧ C i ⊆ C j :=
      Finset.mem_filter.mp hjS
    have hjU : j ∈ U := by
      apply Finset.mem_filter.mpr
      refine ⟨hjdata.1, hjdata.2.1, ?_⟩
      intro k hkI hbadK hjk
      apply hjmax k
      exact Finset.mem_filter.mpr ⟨hkI, hbadK, hjdata.2.2.trans hjk⟩
    exact ⟨j, hjU, hjdata.2.2⟩
  · intro i hi j hjI hstrict hbadJ
    have hiI : i ∈ I := hUsub hi
    have hle : rank j ≤ rank i := (hUprop hi).2 j hjI hbadJ hstrict.1
    have hlt : rank i < rank j := hrank i hiI j hjI hstrict
    exact (not_lt_of_ge hle hlt)

/-- Concrete finite maximal-bad-cell selection in the literal Euclidean
dyadic grid.  A lower scale cutoff supplies the natural finite rank. -/
theorem exists_finset_lacunaryCZDyadic_maximal_bad_selection
    {d : Nat} [NeZero d] (I : Finset (LacunaryCZDyadicCubeIndex d))
    (K : ℤ) (hK : ∀ q ∈ I, K ≤ q.scale)
    (bad : LacunaryCZDyadicCubeIndex d → Prop) :
    ∃ U : Finset (LacunaryCZDyadicCubeIndex d), U ⊆ I ∧
      (∀ q ∈ U, bad q) ∧
      (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
        lacunaryCZDyadicCube ∧
      (∀ q ∈ I, bad q → ∃ r ∈ U,
        lacunaryCZDyadicCube q ⊆ lacunaryCZDyadicCube r) ∧
      (∀ q ∈ U, ∀ r ∈ I,
        lacunaryCZDyadicCube q ⊂ lacunaryCZDyadicCube r → ¬ bad r) := by
  refine exists_finset_laminar_maximal_bad_selection I lacunaryCZDyadicCube bad
    (fun q => (q.scale - K).toNat) ?_ ?_ ?_
  · intro q hq r hr hqr hnot
    exact lacunaryCZDyadicCube_laminar q r hnot
  · intro q hq r hr hsub
    exact lacunaryCZDyadicCube_rank_strict K q r (hK q hq) (hK r hr) hsub
  · intro q hq r hr heq
    exact lacunaryCZDyadicCube_injective heq

/-- The finite stopping predicate used for the literal dyadic
Calderón--Zygmund decomposition. -/
def lacunaryCZDyadicCubeIsBad {d : Nat} (f : Euclidean d → ℂ) (lambda : ℝ)
    (q : LacunaryCZDyadicCubeIndex d) : Prop :=
  lambda * (volume (lacunaryCZDyadicCube q)).toReal <
    ∫ x in lacunaryCZDyadicCube q, ‖f x‖

/-- The complete finite forest supplies the three stopping-time hypotheses:
a lower scale cutoff, coverage of the high level set by bad leaves, and
parent closure of bad cells. -/
private theorem finite_lacunaryCZDyadicCube_stopping_family_of_forest
    {d : Nat} (f : Euclidean d → ℂ) (lambda : ℝ)
    (R : Finset (LacunaryCZDyadicCubeIndex d)) (L : ℤ) (n : Nat)
    (hscale : ∀ q ∈ R, q.scale = L)
    (hroot : ∀ q ∈ R, ¬ lacunaryCZDyadicCubeIsBad f (lambda / 2) q)
    (hcover : ∀ x : Euclidean d, lambda < ‖f x‖ → ∃ q ∈ R,
      x ∈ lacunaryCZDyadicCube q)
    (hleaf : ∀ q ∈ R, ∀ r ∈ lacunaryCZDyadicCubeDescendants q n,
      ∀ x ∈ lacunaryCZDyadicCube r, lambda < ‖f x‖ →
        lacunaryCZDyadicCubeIsBad f (lambda / 2) r) :
    ∃ I : Finset (LacunaryCZDyadicCubeIndex d),
      (∀ q ∈ I, L - n ≤ q.scale) ∧
      (∀ x : Euclidean d, lambda < ‖f x‖ → ∃ q ∈ I,
        x ∈ lacunaryCZDyadicCube q ∧ lacunaryCZDyadicCubeIsBad f (lambda / 2) q) ∧
      (∀ q ∈ I, lacunaryCZDyadicCubeIsBad f (lambda / 2) q →
        lacunaryCZDyadicCubeParent q ∈ I) := by
  refine ⟨lacunaryCZDyadicCubeForest R n, ?_, ?_, ?_⟩
  · exact fun q hq => lacunaryCZDyadicCubeForest_scale_lower R L n hscale hq
  · intro x hx
    obtain ⟨q, hqR, hxq⟩ := hcover x hx
    obtain ⟨r, hr, hxr⟩ := exists_lacunaryCZDyadicCubeDescendant_contains q n hxq
    refine ⟨r, ?_, hxr, hleaf q hqR r hr x hxr hx⟩
    simp only [lacunaryCZDyadicCubeForest]
    exact Finset.mem_biUnion.mpr ⟨q, hqR,
      lacunaryCZDyadicCubeDescendants_subset_tree q n hr⟩
  · exact fun q hq hbad =>
      lacunaryCZDyadicCubeForest_parent_mem_of_not_bad_roots R n
        (lacunaryCZDyadicCubeIsBad f (lambda / 2)) hroot hq hbad

/-- Passing to a dyadic parent multiplies its real volume by `2^d`. -/
theorem volume_lacunaryCZDyadicCubeParent_toReal
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    (volume (lacunaryCZDyadicCube (lacunaryCZDyadicCubeParent q))).toReal =
      (2 : ℝ) ^ d * (volume (lacunaryCZDyadicCube q)).toReal := by
  rw [volume_lacunaryCZDyadicCube, volume_lacunaryCZDyadicCube]
  change (ENNReal.ofReal ((2 : ℝ) ^ (q.scale + 1))).toReal ^ d =
    (2 : ℝ) ^ d * (ENNReal.ofReal ((2 : ℝ) ^ q.scale)).toReal ^ d
  have hside : 0 ≤ (2 : ℝ) ^ q.scale := (zpow_pos (by norm_num) _).le
  have hside' : 0 ≤ (2 : ℝ) ^ (q.scale + 1) := (zpow_pos (by norm_num) _).le
  rw [ENNReal.toReal_ofReal hside', ENNReal.toReal_ofReal hside]
  have hpow : (2 : ℝ) ^ (q.scale + 1) = (2 : ℝ) ^ q.scale * 2 := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [hpow, mul_pow]
  ring

/-- A nonbad parent controls the average on its dyadic child. -/
theorem norm_lacunaryCZDyadicCubeAverage_le_two_pow_dim_mul_of_parent_not_bad
    {d : Nat} (f : Euclidean d → ℂ) (lambda : ℝ)
    (q : LacunaryCZDyadicCubeIndex d) (hf : Integrable f volume)
    (hparent : ¬ lacunaryCZDyadicCubeIsBad f lambda
      (lacunaryCZDyadicCubeParent q)) :
    ‖lacunaryCZDyadicCubeAverage f q‖ ≤ (2 : ℝ) ^ d * lambda := by
  let C := lacunaryCZDyadicCube q
  let P := lacunaryCZDyadicCube (lacunaryCZDyadicCubeParent q)
  have hCpos : 0 < volume C := volume_lacunaryCZDyadicCube_pos q
  have hCtop : volume C ≠ ⊤ := volume_lacunaryCZDyadicCube_ne_top q
  have hCreal : 0 < (volume C).toReal := ENNReal.toReal_pos hCpos.ne' hCtop
  have hsub : C ⊆ P := lacunaryCZDyadicCube_subset_parent q
  have hint : (∫ x in C, ‖f x‖) ≤ ∫ x in P, ‖f x‖ := by
    apply MeasureTheory.setIntegral_mono_set hf.norm.integrableOn
    · filter_upwards with x
      exact norm_nonneg _
    · exact Filter.Eventually.of_forall hsub
  have hP : (∫ x in P, ‖f x‖) ≤ lambda * (volume P).toReal := by
    exact le_of_not_gt hparent
  have havg0 := norm_lacunaryCZDyadicCubeAverage_le_setIntegral_norm f q hf
  have hmul : (volume C).toReal * ‖lacunaryCZDyadicCubeAverage f q‖ ≤
      lambda * (volume P).toReal := by
    calc
      (volume C).toReal * ‖lacunaryCZDyadicCubeAverage f q‖ ≤
          (volume C).toReal *
            ((volume C).toReal⁻¹ * ∫ x in C, ‖f x‖) :=
        mul_le_mul_of_nonneg_left havg0 ENNReal.toReal_nonneg
      _ = ∫ x in C, ‖f x‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hCreal.ne', one_mul]
      _ ≤ ∫ x in P, ‖f x‖ := hint
      _ ≤ lambda * (volume P).toReal := hP
  have hratio : (volume P).toReal = (2 : ℝ) ^ d * (volume C).toReal := by
    dsimp [P, C]
    exact volume_lacunaryCZDyadicCubeParent_toReal q
  rw [hratio] at hmul
  have htarget : (volume C).toReal * ‖lacunaryCZDyadicCubeAverage f q‖ ≤
      (volume C).toReal * ((2 : ℝ) ^ d * lambda) := by
    calc
      (volume C).toReal * ‖lacunaryCZDyadicCubeAverage f q‖ ≤
          lambda * ((2 : ℝ) ^ d * (volume C).toReal) := hmul
      _ = (volume C).toReal * ((2 : ℝ) ^ d * lambda) := by ring
  exact le_of_mul_le_mul_left htarget hCreal

theorem volume_lacunaryCZDyadicCube_toReal
    {d : Nat} (q : LacunaryCZDyadicCubeIndex d) :
    (volume (lacunaryCZDyadicCube q)).toReal = ((2 : ℝ) ^ q.scale) ^ d := by
  rw [volume_lacunaryCZDyadicCube, ENNReal.toReal_pow]
  exact congrArg (fun z : ℝ => z ^ d)
    (ENNReal.toReal_ofReal (zpow_pos (by norm_num) _).le)

/-- The bad-average inequalities of a finite disjoint dyadic family control
its total real volume by the input `L¹` mass. -/
theorem lacunaryCZDyadicCube_selected_real_volume_mass_le_integral_norm
    {d : Nat} (f : Euclidean d → ℂ) (lambda : ℝ)
    (U : Finset (LacunaryCZDyadicCubeIndex d))
    (hdisj : (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
      lacunaryCZDyadicCube)
    (hbad : ∀ q ∈ U,
      lambda * (volume (lacunaryCZDyadicCube q)).toReal ≤
        ∫ x in lacunaryCZDyadicCube q, ‖f x‖)
    (hf : Integrable f volume) :
    lambda * (∑ q ∈ U, (volume (lacunaryCZDyadicCube q)).toReal) ≤
      ∫ x, ‖f x‖ := by
  have hsum : lambda * (∑ q ∈ U, (volume (lacunaryCZDyadicCube q)).toReal) ≤
      ∑ q ∈ U, ∫ x in lacunaryCZDyadicCube q, ‖f x‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq => hbad q hq
  have hunion :
      (∑ q ∈ U, ∫ x in lacunaryCZDyadicCube q, ‖f x‖) =
        ∫ x in ⋃ q ∈ U, lacunaryCZDyadicCube q, ‖f x‖ := by
    symm
    exact integral_biUnion_finset U
      (fun _ _ => measurableSet_lacunaryCZDyadicCube _) hdisj
      (fun _ _ => hf.norm.integrableOn)
  have hglobal : (∫ x in ⋃ q ∈ U, lacunaryCZDyadicCube q, ‖f x‖) ≤
      ∫ x, ‖f x‖ :=
    setIntegral_le_integral hf.norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  calc
    lambda * (∑ q ∈ U, (volume (lacunaryCZDyadicCube q)).toReal) ≤
        ∑ q ∈ U, ∫ x in lacunaryCZDyadicCube q, ‖f x‖ := hsum
    _ = ∫ x in ⋃ q ∈ U, lacunaryCZDyadicCube q, ‖f x‖ := hunion
    _ ≤ ∫ x, ‖f x‖ := hglobal

/-- The selected volume bound in the literal dyadic grid gives the exact
sum of side-length powers needed by the lacunary tail estimates. -/
theorem sum_lacunaryCZDyadicCube_side_pow_le_inv_lambda_mul_integral_norm
    {d : Nat} (f : Euclidean d → ℂ) {lambda : ℝ}
    (hlambda : 0 < lambda) (U : Finset (LacunaryCZDyadicCubeIndex d))
    (hdisj : (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
      lacunaryCZDyadicCube)
    (hbad : ∀ q ∈ U,
      lambda * (volume (lacunaryCZDyadicCube q)).toReal ≤
        ∫ x in lacunaryCZDyadicCube q, ‖f x‖)
    (hf : Integrable f volume) :
    (∑ q ∈ U, ((2 : ℝ) ^ q.scale) ^ d) ≤
      lambda⁻¹ * ∫ x, ‖f x‖ := by
  have hmass :=
    lacunaryCZDyadicCube_selected_real_volume_mass_le_integral_norm
      f lambda U hdisj hbad hf
  have hsumvol : (∑ q ∈ U, (volume (lacunaryCZDyadicCube q)).toReal) =
      ∑ q ∈ U, ((2 : ℝ) ^ q.scale) ^ d := by
    apply Finset.sum_congr rfl
    intro q hq
    exact volume_lacunaryCZDyadicCube_toReal q
  rw [hsumvol] at hmass
  calc
    (∑ q ∈ U, ((2 : ℝ) ^ q.scale) ^ d) =
        lambda⁻¹ * (lambda * (∑ q ∈ U, ((2 : ℝ) ^ q.scale) ^ d)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hlambda.ne', one_mul]
    _ ≤ lambda⁻¹ * ∫ x, ‖f x‖ :=
      mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr hlambda.le)

/-- The same selected-mass estimate for the enclosing radii used by the
global cancellation argument. -/
theorem sum_lacunaryCZDyadicCube_radius_pow_le_dim_pow_mul_inv_lambda_mul_integral_norm
    {d : Nat} (f : Euclidean d → ℂ) {lambda : ℝ}
    (hlambda : 0 < lambda) (U : Finset (LacunaryCZDyadicCubeIndex d))
    (hdisj : (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
      lacunaryCZDyadicCube)
    (hbad : ∀ q ∈ U,
      lambda * (volume (lacunaryCZDyadicCube q)).toReal ≤
        ∫ x in lacunaryCZDyadicCube q, ‖f x‖)
    (hf : Integrable f volume) :
    (∑ q ∈ U, (lacunaryCZDyadicCubeRadius q) ^ d) ≤
      (d : ℝ) ^ d * (lambda⁻¹ * ∫ x, ‖f x‖) := by
  have hside := sum_lacunaryCZDyadicCube_side_pow_le_inv_lambda_mul_integral_norm
    f hlambda U hdisj hbad hf
  calc
    (∑ q ∈ U, (lacunaryCZDyadicCubeRadius q) ^ d) =
        ∑ q ∈ U, (d : ℝ) ^ d * ((2 : ℝ) ^ q.scale) ^ d := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [lacunaryCZDyadicCubeRadius, mul_pow]
    _ = (d : ℝ) ^ d * (∑ q ∈ U, ((2 : ℝ) ^ q.scale) ^ d) := by
      rw [Finset.mul_sum]
    _ ≤ (d : ℝ) ^ d * (lambda⁻¹ * ∫ x, ‖f x‖) :=
      mul_le_mul_of_nonneg_left hside
        (pow_nonneg (Nat.cast_nonneg d) _)

/-- A concrete finite Calderón--Zygmund decomposition in the literal
Euclidean dyadic grid.  The two finite-approximation hypotheses say that all
points above the threshold occur in one of the listed bad cells and that the
parent of every listed bad cell is still in the finite family.  Maximality
then supplies the needed nonbad parent. -/
theorem exists_lacunaryCZDyadicCube_finite_decomposition
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ) (lambda eta : ℝ)
    (hlambda : 0 < lambda) (heta : eta ≤ (2 : ℝ) ^ d * lambda)
    (I : Finset (LacunaryCZDyadicCubeIndex d))
    (K : ℤ) (hK : ∀ q ∈ I, K ≤ q.scale)
    (hpoint : ∀ x : Euclidean d, eta < ‖f x‖ → ∃ q ∈ I,
      x ∈ lacunaryCZDyadicCube q ∧ lacunaryCZDyadicCubeIsBad f lambda q)
    (hparent_mem : ∀ q ∈ I, lacunaryCZDyadicCubeIsBad f lambda q →
      lacunaryCZDyadicCubeParent q ∈ I)
    (hf : Integrable f volume) :
    ∃ U : Finset (LacunaryCZDyadicCubeIndex d), U ⊆ I ∧
      (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
        lacunaryCZDyadicCube ∧
      (∀ q ∈ U, lacunaryCZDyadicCubeIsBad f lambda q) ∧
      (∀ x : Euclidean d,
        x ∉ ⋃ q ∈ U, lacunaryCZDyadicCube q → ‖f x‖ ≤ eta) ∧
      (∀ q ∈ U, ‖lacunaryCZDyadicCubeAverage f q‖ ≤ (2 : ℝ) ^ d * lambda) ∧
      (∀ q ∈ U, Integrable (lacunaryCZDyadicCubeBadAtom f q) volume) ∧
      (∀ q ∈ U, (∫ x, lacunaryCZDyadicCubeBadAtom f q x) = 0) ∧
      (∀ q ∈ U, ∀ x : Euclidean d,
        lacunaryCZDyadicCubeBadAtom f q x ≠ 0 →
          ‖x - lacunaryCZDyadicCubeCenter q‖ ≤ lacunaryCZDyadicCubeRadius q) ∧
      (∀ x : Euclidean d, f x = lacunaryCZDyadicCubeGoodPart f U x +
        ∑ q ∈ U, lacunaryCZDyadicCubeBadAtom f q x) ∧
      Integrable (lacunaryCZDyadicCubeGoodPart f U) volume ∧
      (∫ x, ‖lacunaryCZDyadicCubeGoodPart f U x‖ ^ 2) ≤
        (3 * ((2 : ℝ) ^ d * lambda)) * ∫ x, ‖f x‖ ∧
      (∑ q ∈ U, ∫ x, ‖lacunaryCZDyadicCubeBadAtom f q x‖) ≤
        2 * ∫ x, ‖f x‖ ∧
      (∑ q ∈ U, ((2 : ℝ) ^ q.scale) ^ d) ≤ lambda⁻¹ * ∫ x, ‖f x‖ ∧
      (∑ q ∈ U, (lacunaryCZDyadicCubeRadius q) ^ d) ≤
        (d : ℝ) ^ d * (lambda⁻¹ * ∫ x, ‖f x‖) := by
  obtain ⟨U, hUI, hbad, hdisj, hcover, hmax⟩ :=
    exists_finset_lacunaryCZDyadic_maximal_bad_selection I K hK
      (lacunaryCZDyadicCubeIsBad f lambda)
  have houtside : ∀ x : Euclidean d,
      x ∉ ⋃ q ∈ U, lacunaryCZDyadicCube q → ‖f x‖ ≤ eta := by
    intro x hx
    by_contra hnorm
    have hgt : eta < ‖f x‖ := lt_of_not_ge hnorm
    obtain ⟨q, hqI, hxq, hqbad⟩ := hpoint x hgt
    obtain ⟨r, hrU, hqr⟩ := hcover q hqI hqbad
    apply hx
    exact Set.mem_iUnion₂.mpr ⟨r, hrU, hqr hxq⟩
  have havg : ∀ q ∈ U,
      ‖lacunaryCZDyadicCubeAverage f q‖ ≤ (2 : ℝ) ^ d * lambda := by
    intro q hq
    exact norm_lacunaryCZDyadicCubeAverage_le_two_pow_dim_mul_of_parent_not_bad
      f lambda q hf
        (hmax q hq (lacunaryCZDyadicCubeParent q)
          (hparent_mem q (hUI hq) (hbad q hq))
          (lacunaryCZDyadicCube_ssub_parent q))
  have hbadle : ∀ q ∈ U,
      lambda * (volume (lacunaryCZDyadicCube q)).toReal ≤
        ∫ x in lacunaryCZDyadicCube q, ‖f x‖ := by
    intro q hq
    exact (hbad q hq).le
  have houtside' : ∀ x : Euclidean d,
      x ∉ ⋃ q ∈ U, lacunaryCZDyadicCube q →
        ‖f x‖ ≤ (2 : ℝ) ^ d * lambda := by
    intro x hx
    exact (houtside x hx).trans heta
  have hL2 :=
    integral_norm_sq_lacunaryCZDyadicCubeGoodPart_le_three_mul_lambda_mul_integral_norm
      f U hdisj ((2 : ℝ) ^ d * lambda)
      (mul_nonneg (pow_nonneg (by norm_num) _) hlambda.le)
      houtside' havg hf
  refine ⟨U, hUI, hdisj, hbad, houtside, havg, ?_, ?_, ?_, ?_,
    integrable_lacunaryCZDyadicCubeGoodPart f U hf, hL2, ?_, ?_, ?_⟩
  · intro q hq
    exact integrable_lacunaryCZDyadicCubeBadAtom f q hf
  · intro q hq
    exact integral_lacunaryCZDyadicCubeBadAtom_eq_zero f q hf
  · intro q hq x hx
    exact lacunaryCZDyadicCubeBadAtom_dist_center_le_radius f q hx
  · intro x
    exact lacunaryCZDyadicCubeGoodPart_add_sum_eq f U x
  · exact sum_integral_norm_lacunaryCZDyadicCubeBadAtom_le_two_mul_integral_norm
      f U hdisj hf
  · exact sum_lacunaryCZDyadicCube_side_pow_le_inv_lambda_mul_integral_norm
      f hlambda U hdisj hbadle hf
  · exact
      sum_lacunaryCZDyadicCube_radius_pow_le_dim_pow_mul_inv_lambda_mul_integral_norm
        f hlambda U hdisj hbadle hf

private def lacunaryCZDyadicCubeRootBlock {d : Nat} (L : Nat) (B : ℤ) :
    Finset (LacunaryCZDyadicCubeIndex d) :=
  (Finset.univ : Finset (Fin d → ↥(Finset.Icc (-B) B))).image
    (fun m => ⟨(L : ℤ), fun i => (m i : ℤ)⟩)

private theorem lacunaryCZDyadicCubeRootBlock_scale {d : Nat} (L : Nat) (B : ℤ)
    {q : LacunaryCZDyadicCubeIndex d}
    (hq : q ∈ lacunaryCZDyadicCubeRootBlock L B) : q.scale = L := by
  simp only [lacunaryCZDyadicCubeRootBlock] at hq
  rcases Finset.mem_image.mp hq with ⟨m, hm, heq⟩
  subst q
  rfl

private def lacunaryCZDyadicCubeAt {d : Nat} (L : Nat) (x : Euclidean d) :
    LacunaryCZDyadicCubeIndex d :=
  ⟨(L : ℤ), fun i => ⌊WithLp.ofLp x i / (2 : ℝ) ^ L⌋⟩

private theorem mem_lacunaryCZDyadicCubeAt {d : Nat} (L : Nat) (x : Euclidean d) :
    x ∈ lacunaryCZDyadicCube (lacunaryCZDyadicCubeAt L x) := by
  let s : ℝ := (2 : ℝ) ^ L
  have hs : 0 < s := by
    dsimp [s]
    exact pow_pos (by norm_num) _
  change (WithLp.ofLp x) ∈ Set.pi Set.univ (fun i =>
    Set.Ico ((⌊WithLp.ofLp x i / s⌋ : ℤ) * s)
      (((⌊WithLp.ofLp x i / s⌋ + 1 : ℤ) : ℝ) * s))
  rw [Set.mem_pi]
  intro i hi
  change ((⌊WithLp.ofLp x i / s⌋ : ℤ) : ℝ) * s ≤ WithLp.ofLp x i ∧
    WithLp.ofLp x i < ((⌊WithLp.ofLp x i / s⌋ + 1 : ℤ) : ℝ) * s
  constructor
  · rw [← le_div_iff₀ hs]
    exact Int.floor_le _
  · rw [← div_lt_iff₀ hs]
    simp [Int.cast_add, Int.cast_one, Int.lt_floor_add_one]

private theorem mem_lacunaryCZDyadicCubeRootBlock_of_norm_le
    {d : Nat} (L : Nat) {R : ℝ}
    (hR : 0 ≤ R) (B : ℤ) (hB : R ≤ B)
    {x : Euclidean d} (hx : ‖x‖ ≤ R) :
    lacunaryCZDyadicCubeAt L x ∈ lacunaryCZDyadicCubeRootBlock L B := by
  let s : ℝ := (2 : ℝ) ^ L
  have hs : 0 < s := by
    dsimp [s]
    exact pow_pos (by norm_num) _
  have hsone : 1 ≤ s := by
    dsimp [s]
    exact one_le_pow₀ (by norm_num)
  apply Finset.mem_image.mpr
  let m : Fin d → ↥(Finset.Icc (-B) B) := fun i =>
    ⟨⌊WithLp.ofLp x i / s⌋, ?_⟩
  · refine ⟨m, Finset.mem_univ _, ?_⟩
    rfl
  · rw [Finset.mem_Icc]
    have hcoord : |WithLp.ofLp x i| ≤ R := by
      calc
        |WithLp.ofLp x i| = ‖WithLp.ofLp x i‖ := Real.norm_eq_abs _
        _ ≤ ‖x‖ := PiLp.norm_apply_le x i
        _ ≤ R := hx
    have hlowx : -R ≤ WithLp.ofLp x i := (abs_le.mp hcoord).1
    have huppx : WithLp.ofLp x i ≤ R := (abs_le.mp hcoord).2
    have hlowdiv : (-B : ℝ) ≤ WithLp.ofLp x i / s := by
      rw [le_div_iff₀ hs]
      have hBs : (-B : ℝ) * s ≤ -R := by
        have hnegB : (-B : ℝ) ≤ 0 := by linarith
        nlinarith
      exact hBs.trans hlowx
    have huppdiv : WithLp.ofLp x i / s ≤ B := by
      rw [div_le_iff₀ hs]
      have hBs : R ≤ (B : ℝ) * s := by
        have hBnonneg : 0 ≤ (B : ℝ) := hR.trans hB
        nlinarith
      exact huppx.trans hBs
    constructor
    · rw [Int.le_floor]
      simpa using hlowdiv
    · have hlt : WithLp.ofLp x i / s < (B : ℝ) + 1 :=
        lt_of_le_of_lt huppdiv (by norm_num)
      have hfloorlt : ⌊WithLp.ofLp x i / s⌋ < B + 1 := by
        rw [Int.floor_lt]
        simpa [Int.cast_add, Int.cast_one] using hlt
      omega

private theorem exists_lacunaryCZDyadicCube_coarse_scale
    {d : Nat} [NeZero d] (A mu : ℝ) (hmu : 0 < mu) :
    ∃ L : Nat, A ≤ mu * ((2 : ℝ) ^ L) ^ d := by
  have hlim : Filter.Tendsto (fun L : Nat => (2 : ℝ) ^ L)
      Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent : ∀ᶠ L : Nat in Filter.atTop, A / mu ≤ (2 : ℝ) ^ L :=
    hlim.eventually (Filter.eventually_atTop.mpr
      ⟨A / mu, fun b hb => hb⟩)
  obtain ⟨L, hL⟩ := hevent.exists
  refine ⟨L, ?_⟩
  have hside : 1 ≤ (2 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hsidepow : (2 : ℝ) ^ L ≤ ((2 : ℝ) ^ L) ^ d := by
    simpa using (pow_le_pow_right₀ hside hd)
  have hmul : mu * (A / mu) ≤ mu * (2 : ℝ) ^ L :=
    mul_le_mul_of_nonneg_left hL hmu.le
  have hA : A ≤ mu * (2 : ℝ) ^ L := by
    convert hmul using 1
    field_simp
  exact hA.trans (mul_le_mul_of_nonneg_left hsidepow hmu.le)

private theorem exists_lacunaryCZDyadicCube_fine_depth
    {d : Nat} [NeZero d] (L : Nat) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ n : Nat, 2 * (d : ℝ) * (2 : ℝ) ^ ((L : ℤ) - n) < delta := by
  let C : ℝ := 2 * (d : ℝ)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by norm_num)
      (by exact_mod_cast Nat.pos_iff_ne_zero.mpr (NeZero.ne d))
  have hlim : Filter.Tendsto (fun m : Nat => (1 / 2 : ℝ) ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hevent : ∀ᶠ m : Nat in Filter.atTop, (1 / 2 : ℝ) ^ m < delta / C := by
    simpa using hlim.eventually (Iio_mem_nhds (div_pos hdelta hC))
  obtain ⟨m, hm⟩ := hevent.exists
  refine ⟨L + m, ?_⟩
  have hCm : C * (1 / 2 : ℝ) ^ m < delta := by
    calc
      C * (1 / 2 : ℝ) ^ m < C * (delta / C) :=
        mul_lt_mul_of_pos_left hm hC
      _ = delta := by field_simp
  change C * (2 : ℝ) ^ ((L : ℤ) - ((L + m : Nat) : ℤ)) < delta
  rw [show (L : ℤ) - ((L + m : Nat) : ℤ) = -(m : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast]
  simpa [one_div, inv_pow] using hCm

private theorem lacunaryCZDyadicCubeRootBlock_not_bad
    {d : Nat} (f : Euclidean d → ℂ) (mu : ℝ) (hf : Integrable f volume)
    (L : Nat) (B : ℤ)
    (hlarge : (∫ x, ‖f x‖) ≤ mu * ((2 : ℝ) ^ L) ^ d)
    {q : LacunaryCZDyadicCubeIndex d}
    (hq : q ∈ lacunaryCZDyadicCubeRootBlock L B) :
    ¬ lacunaryCZDyadicCubeIsBad f mu q := by
  intro hbad
  have hset : (∫ x in lacunaryCZDyadicCube q, ‖f x‖) ≤ ∫ x, ‖f x‖ :=
    setIntegral_le_integral hf.norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  have hscale : q.scale = L := lacunaryCZDyadicCubeRootBlock_scale L B hq
  have hvol : (volume (lacunaryCZDyadicCube q)).toReal = ((2 : ℝ) ^ L) ^ d := by
    rw [volume_lacunaryCZDyadicCube_toReal q, hscale]
    simp
  apply (not_lt_of_ge ?_) hbad
  rw [hvol]
  exact hset.trans hlarge

private theorem lacunaryCZDyadicCube_leaf_isBad_of_uniform_control
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ) (lambda delta : ℝ)
    (hlambda : 0 < lambda) (hf : Integrable f volume)
    (huc : ∀ ⦃a b : Euclidean d⦄, dist a b < delta →
      dist (f a) (f b) < lambda / 4)
    (r : LacunaryCZDyadicCubeIndex d) {x : Euclidean d}
    (hx : x ∈ lacunaryCZDyadicCube r) (hhigh : lambda < ‖f x‖)
    (hdiam : 2 * (d : ℝ) * (2 : ℝ) ^ r.scale < delta) :
    lacunaryCZDyadicCubeIsBad f (lambda / 2) r := by
  let C : Set (Euclidean d) := lacunaryCZDyadicCube r
  let c : ℝ := 3 * lambda / 4
  have hpoint : ∀ y ∈ C, c ≤ ‖f y‖ := by
    intro y hy
    have hdist : dist y x < delta := by
      calc
        dist y x ≤ 2 * lacunaryCZDyadicCubeRadius r :=
          lacunaryCZDyadicCube_dist_le_two_radius r hy hx
        _ = 2 * (d : ℝ) * (2 : ℝ) ^ r.scale := by
          simp only [lacunaryCZDyadicCubeRadius]
          ring
        _ < delta := hdiam
    have hdiff : ‖f y - f x‖ < lambda / 4 := by
      simpa only [dist_eq_norm_sub] using huc hdist
    have htri := norm_le_norm_add_norm_sub (f y) (f x)
    dsimp [c]
    linarith
  have hconst : Integrable (fun _ : Euclidean d => c) (volume.restrict C) := by
    exact integrableOn_const (volume_lacunaryCZDyadicCube_ne_top r)
  have hnorm : Integrable (fun y : Euclidean d => ‖f y‖) (volume.restrict C) :=
    hf.norm.integrableOn
  have hAE : (fun _ : Euclidean d => c) ≤ᵐ[volume.restrict C] fun y => ‖f y‖ := by
    filter_upwards [ae_restrict_mem (measurableSet_lacunaryCZDyadicCube r)] with y hy
    exact hpoint y hy
  have hint := integral_mono_ae hconst hnorm hAE
  have hvol : 0 < (volume C).toReal :=
    ENNReal.toReal_pos (volume_lacunaryCZDyadicCube_pos r).ne'
      (volume_lacunaryCZDyadicCube_ne_top r)
  change (lambda / 2) * (volume C).toReal < ∫ y in C, ‖f y‖
  calc
    (lambda / 2) * (volume C).toReal < c * (volume C).toReal := by
      apply mul_lt_mul_of_pos_right _ hvol
      dsimp [c]
      linarith
    _ = ∫ y in C, c := by
      rw [setIntegral_const]
      simp only [smul_eq_mul]
      rw [Measure.real]
      ring
    _ ≤ ∫ y in C, ‖f y‖ := by
      exact hint

/-- A direct finite Calderón--Zygmund decomposition for a continuous,
compactly supported input.  The stopping cubes are constructed internally:
large finite grid roots are nonbad at `lambda / 2`, and a sufficiently fine
finite descendant tree captures the level set above `lambda`. -/
theorem exists_lacunaryCZDyadicCube_continuous_decay_decomposition
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ) (lambda : ℝ)
    (hlambda : 0 < lambda) (hcont : Continuous f) (hf : Integrable f volume)
    (hzero : Filter.Tendsto f (Filter.cocompact (Euclidean d)) (nhds 0)) :
    ∃ U : Finset (LacunaryCZDyadicCubeIndex d),
      (↑U : Set (LacunaryCZDyadicCubeIndex d)).PairwiseDisjoint
        lacunaryCZDyadicCube ∧
      (∀ q ∈ U, lacunaryCZDyadicCubeIsBad f (lambda / 2) q) ∧
      (∀ x : Euclidean d,
        x ∉ ⋃ q ∈ U, lacunaryCZDyadicCube q → ‖f x‖ ≤ lambda) ∧
      (∀ q ∈ U, ‖lacunaryCZDyadicCubeAverage f q‖ ≤
        (2 : ℝ) ^ d * (lambda / 2)) ∧
      (∀ x : Euclidean d, ‖lacunaryCZDyadicCubeGoodPart f U x‖ ≤
        (2 : ℝ) ^ d * (lambda / 2)) ∧
      (∀ q ∈ U, Integrable (lacunaryCZDyadicCubeBadAtom f q) volume) ∧
      (∀ q ∈ U, (∫ x, lacunaryCZDyadicCubeBadAtom f q x) = 0) ∧
      (∀ q ∈ U, ∀ x : Euclidean d,
        lacunaryCZDyadicCubeBadAtom f q x ≠ 0 →
          ‖x - lacunaryCZDyadicCubeCenter q‖ ≤ lacunaryCZDyadicCubeRadius q) ∧
      (∀ x : Euclidean d, f x = lacunaryCZDyadicCubeGoodPart f U x +
        ∑ q ∈ U, lacunaryCZDyadicCubeBadAtom f q x) ∧
      Integrable (lacunaryCZDyadicCubeGoodPart f U) volume ∧
      (∫ x, ‖lacunaryCZDyadicCubeGoodPart f U x‖ ^ 2) ≤
        (3 * ((2 : ℝ) ^ d * (lambda / 2))) * ∫ x, ‖f x‖ ∧
      (∑ q ∈ U, ∫ x, ‖lacunaryCZDyadicCubeBadAtom f q x‖) ≤
        2 * ∫ x, ‖f x‖ ∧
      (∑ q ∈ U, ((2 : ℝ) ^ q.scale) ^ d) ≤
        (lambda / 2)⁻¹ * ∫ x, ‖f x‖ ∧
      (∑ q ∈ U, (lacunaryCZDyadicCubeRadius q) ^ d) ≤
        (d : ℝ) ^ d * ((lambda / 2)⁻¹ * ∫ x, ‖f x‖) := by
  obtain ⟨R, hRpos, hR⟩ : ∃ R : ℝ, 0 < R ∧
      ∀ x : Euclidean d, lambda < ‖f x‖ → ‖x‖ ≤ R := by
    have hevent : ∀ᶠ x : Euclidean d in Filter.cocompact (Euclidean d),
        f x ∈ Metric.ball 0 lambda :=
      hzero.eventually (Metric.ball_mem_nhds _ hlambda)
    rcases Filter.mem_cocompact.mp hevent with ⟨K, hKcompact, hK⟩
    have hsub : {x : Euclidean d | lambda < ‖f x‖} ⊆ K := by
      intro x hx
      by_contra hxK
      have hxball := hK hxK
      change f x ∈ Metric.ball 0 lambda at hxball
      rw [Metric.mem_ball, dist_zero_right] at hxball
      exact (not_lt_of_ge hx.le) hxball
    have hKbounded := hKcompact.isBounded
    rw [isBounded_iff_forall_norm_le] at hKbounded
    rcases hKbounded with ⟨C, hC⟩
    refine ⟨max C 0 + 1,
      add_pos_of_nonneg_of_pos (le_max_right _ _) zero_lt_one, ?_⟩
    intro x hx
    exact (hC x (hsub hx)).trans (by linarith [le_max_left C 0])
  let B : ℤ := ⌈R⌉ + 1
  have hRB : R ≤ B := by
    dsimp [B]
    exact (Int.le_ceil R).trans (by norm_num)
  obtain ⟨L, hL⟩ := exists_lacunaryCZDyadicCube_coarse_scale (d := d)
    (∫ x, ‖f x‖) (lambda / 2) (half_pos hlambda)
  let Roots : Finset (LacunaryCZDyadicCubeIndex d) :=
    lacunaryCZDyadicCubeRootBlock L B
  have hrootscale : ∀ q ∈ Roots, q.scale = L := by
    intro q hq
    exact lacunaryCZDyadicCubeRootBlock_scale L B hq
  have hroot : ∀ q ∈ Roots, ¬ lacunaryCZDyadicCubeIsBad f (lambda / 2) q := by
    intro q hq
    exact lacunaryCZDyadicCubeRootBlock_not_bad f (lambda / 2) hf L B hL hq
  have hcover : ∀ x : Euclidean d, lambda < ‖f x‖ → ∃ q ∈ Roots,
      x ∈ lacunaryCZDyadicCube q := by
    intro x hx
    have hxR : ‖x‖ ≤ R := hR x hx
    refine ⟨lacunaryCZDyadicCubeAt L x, ?_, mem_lacunaryCZDyadicCubeAt L x⟩
    exact mem_lacunaryCZDyadicCubeRootBlock_of_norm_le L hRpos.le B hRB hxR
  have hUC : UniformContinuous f :=
    hcont.uniformContinuous_of_tendsto_cocompact hzero
  obtain ⟨delta, hdelta, hdeltaUC⟩ :=
    (Metric.uniformContinuous_iff.mp hUC) (lambda / 4) (by linarith)
  obtain ⟨n, hn⟩ := exists_lacunaryCZDyadicCube_fine_depth (d := d) L hdelta
  have hleaf : ∀ q ∈ Roots, ∀ r ∈ lacunaryCZDyadicCubeDescendants q n,
      ∀ x ∈ lacunaryCZDyadicCube r, lambda < ‖f x‖ →
        lacunaryCZDyadicCubeIsBad f (lambda / 2) r := by
    intro q hq r hr x hxr hx
    have hrs : r.scale = q.scale - n :=
      lacunaryCZDyadicCubeDescendant_scale q n hr
    have hdiam : 2 * (d : ℝ) * (2 : ℝ) ^ r.scale < delta := by
      rw [hrs, hrootscale q hq]
      exact hn
    exact lacunaryCZDyadicCube_leaf_isBad_of_uniform_control f lambda delta hlambda hf
      hdeltaUC r hxr hx hdiam
  obtain ⟨I, hK, hpoint, hparent⟩ :=
    finite_lacunaryCZDyadicCube_stopping_family_of_forest f lambda Roots (L : ℤ) n
      hrootscale hroot hcover hleaf
  have heta : lambda ≤ (2 : ℝ) ^ d * (lambda / 2) := by
    have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ d := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd)
    calc
      lambda = 2 * (lambda / 2) := by ring
      _ ≤ (2 : ℝ) ^ d * (lambda / 2) :=
        mul_le_mul_of_nonneg_right hpow (by linarith)
  obtain ⟨U, hUI, hdisj, hbad, houtside, havg, hatomint, hzero, hsupp,
    hsum, hgoodint, hL2, hL1, hside, hradius⟩ :=
    exists_lacunaryCZDyadicCube_finite_decomposition f (lambda / 2) lambda
      (half_pos hlambda) heta I ((L : ℤ) - n) hK hpoint hparent hf
  have hgoodbound : ∀ x : Euclidean d,
      ‖lacunaryCZDyadicCubeGoodPart f U x‖ ≤ (2 : ℝ) ^ d * (lambda / 2) := by
    intro x
    exact norm_lacunaryCZDyadicCubeGoodPart_le_of_outside_and_average_bounds
      f U hdisj ((2 : ℝ) ^ d * (lambda / 2))
      (fun y hy => (houtside y hy).trans heta) havg x
  exact ⟨U, hdisj, hbad, houtside, havg, hgoodbound, hatomint, hzero, hsupp,
    hsum, hgoodint, hL2, hL1, hside, hradius⟩

/-- The complex average of an input over one selected dyadic ball. -/
def lacunaryCZBallAverage {d : Nat} (f : Euclidean d → ℂ)
    (a : Euclidean d × ℤ) : ℂ :=
  (volume (lacunaryCZBall a)).toReal⁻¹ •
    ∫ x in lacunaryCZBall a, f x

/-- The literal mean-zero atom associated with one selected dyadic ball. -/
def lacunaryCZBadAtom {d : Nat} (f : Euclidean d → ℂ)
    (a : Euclidean d × ℤ) : Euclidean d → ℂ :=
  (lacunaryCZBall a).indicator
    (fun x => f x - lacunaryCZBallAverage f a)

/-- A bad atom is supported in its selected dyadic ball. -/
theorem lacunaryCZBadAtom_support
    {d : Nat} (f : Euclidean d → ℂ) (a : Euclidean d × ℤ)
    {x : Euclidean d} (hx : lacunaryCZBadAtom f a x ≠ 0) :
    x ∈ lacunaryCZBall a := by
  contrapose! hx
  simp [lacunaryCZBadAtom, hx]

/-- The selected atom is integrable whenever the original input is. -/
theorem integrable_lacunaryCZBadAtom
    {d : Nat} (f : Euclidean d → ℂ) (a : Euclidean d × ℤ)
    (hf : Integrable f volume) :
    Integrable (lacunaryCZBadAtom f a) volume := by
  unfold lacunaryCZBadAtom
  apply IntegrableOn.integrable_indicator
  · exact hf.integrableOn.sub (integrableOn_const measure_ball_lt_top.ne)
  · exact Metric.isOpen_ball.measurableSet

/-- The bad atom has zero total mass.  Positivity of the Euclidean ball
measure is the only point where a nonzero ambient dimension is used. -/
theorem integral_lacunaryCZBadAtom_eq_zero
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ) (a : Euclidean d × ℤ)
    (hf : Integrable f volume) :
    (∫ x, lacunaryCZBadAtom f a x) = 0 := by
  let B : Set (Euclidean d) := lacunaryCZBall a
  let A : ℂ := lacunaryCZBallAverage f a
  have hB : MeasurableSet B := by
    exact Metric.isOpen_ball.measurableSet
  have hr : 0 < (2 : ℝ) ^ a.2 := zpow_pos (by norm_num) _
  have hvolpos : 0 < volume B := by
    exact Metric.measure_ball_pos volume a.1 hr
  have hvoltop : volume B ≠ ⊤ := by
    exact measure_ball_lt_top.ne
  have hV : 0 < (volume B).toReal := ENNReal.toReal_pos hvolpos.ne' hvoltop
  have hfB : IntegrableOn f B volume := hf.integrableOn
  have hAB : IntegrableOn (fun _ : Euclidean d => A) B volume := by
    exact integrableOn_const hvoltop
  change (∫ x, B.indicator (fun x => f x - A) x) = 0
  rw [integral_indicator hB, integral_sub hfB hAB, setIntegral_const]
  change (∫ x in B, f x) - (volume B).toReal •
      ((volume B).toReal⁻¹ • ∫ x in B, f x) = 0
  rw [← mul_smul, mul_inv_cancel₀ hV.ne', one_smul, sub_self]

/-- The good term for a finite selected family is defined by removing the
literal finite sum of its bad atoms. -/
def lacunaryCZGoodPart {d : Nat} (f : Euclidean d → ℂ)
    (U : Finset (Euclidean d × ℤ)) : Euclidean d → ℂ :=
  fun x => f x - ∑ a ∈ U, lacunaryCZBadAtom f a x

/-- The norm of the selected-ball average is bounded by the average of the
norm.  This is the scalar estimate behind the `L¹` control of a bad atom. -/
theorem norm_lacunaryCZBallAverage_le_setIntegral_norm
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ) (a : Euclidean d × ℤ)
    (_hf : Integrable f volume) :
    ‖lacunaryCZBallAverage f a‖ ≤
      (volume (lacunaryCZBall a)).toReal⁻¹ *
        ∫ x in lacunaryCZBall a, ‖f x‖ := by
  let B : Set (Euclidean d) := lacunaryCZBall a
  have hr : 0 < (2 : ℝ) ^ a.2 := zpow_pos (by norm_num) _
  have hvolpos : 0 < volume B := Metric.measure_ball_pos volume a.1 hr
  have hvoltop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hinv : 0 ≤ (volume B).toReal⁻¹ := inv_nonneg.mpr (ENNReal.toReal_nonneg)
  have hint : ‖∫ x in B, f x‖ ≤ ∫ x in B, ‖f x‖ :=
    norm_integral_le_integral_norm (μ := volume.restrict B) f
  change ‖(volume B).toReal⁻¹ • ∫ x in B, f x‖ ≤
    (volume B).toReal⁻¹ * ∫ x in B, ‖f x‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
  exact mul_le_mul_of_nonneg_left hint hinv

/-- One canonical bad atom costs at most twice the `L¹` mass of the input on
its selected ball. -/
theorem integral_norm_lacunaryCZBadAtom_le_two_mul_setIntegral_norm
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ) (a : Euclidean d × ℤ)
    (hf : Integrable f volume) :
    (∫ x, ‖lacunaryCZBadAtom f a x‖) ≤
      2 * ∫ x in lacunaryCZBall a, ‖f x‖ := by
  let B : Set (Euclidean d) := lacunaryCZBall a
  let A : ℂ := lacunaryCZBallAverage f a
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hr : 0 < (2 : ℝ) ^ a.2 := zpow_pos (by norm_num) _
  have hvolpos : 0 < volume B := Metric.measure_ball_pos volume a.1 hr
  have hvoltop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hV : 0 < (volume B).toReal := ENNReal.toReal_pos hvolpos.ne' hvoltop
  have hfB : IntegrableOn f B volume := hf.integrableOn
  have hAB : IntegrableOn (fun _ : Euclidean d => A) B volume :=
    integrableOn_const hvoltop
  have hsub : IntegrableOn (fun x : Euclidean d => f x - A) B volume :=
    hfB.sub hAB
  have hright : IntegrableOn (fun x : Euclidean d => ‖f x‖ + ‖A‖) B volume :=
    hfB.norm.add hAB.norm
  have hmono : (∫ x in B, ‖f x - A‖) ≤
      ∫ x in B, ‖f x‖ + ‖A‖ := by
    exact integral_mono hsub.norm hright fun x => norm_sub_le _ _
  have havg : ‖A‖ ≤ (volume B).toReal⁻¹ * ∫ x in B, ‖f x‖ := by
    simpa only [A, B] using
      norm_lacunaryCZBallAverage_le_setIntegral_norm f a hf
  have hscale : (volume B).toReal * ‖A‖ ≤ ∫ x in B, ‖f x‖ := by
    calc
      (volume B).toReal * ‖A‖ ≤
          (volume B).toReal *
            ((volume B).toReal⁻¹ * ∫ x in B, ‖f x‖) :=
        mul_le_mul_of_nonneg_left havg ENNReal.toReal_nonneg
      _ = ∫ x in B, ‖f x‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]
  calc
    (∫ x, ‖lacunaryCZBadAtom f a x‖) = ∫ x in B, ‖f x - A‖ := by
      rw [show (fun x : Euclidean d => ‖lacunaryCZBadAtom f a x‖) =
          B.indicator (fun x => ‖f x - A‖) by
        funext x
        by_cases hx : x ∈ B <;> simp [lacunaryCZBadAtom, B, A, hx]]
      exact integral_indicator hB
    _ ≤ ∫ x in B, ‖f x‖ + ‖A‖ := hmono
    _ = (∫ x in B, ‖f x‖) + (volume B).toReal * ‖A‖ := by
      rw [integral_add hfB.norm hAB.norm, setIntegral_const]
      simp only [Measure.real, smul_eq_mul]
    _ ≤ (∫ x in B, ‖f x‖) + (∫ x in B, ‖f x‖) :=
      add_le_add_right hscale _
    _ = 2 * ∫ x in B, ‖f x‖ := by ring

/-- Disjoint selected balls make the `L¹` costs of the canonical bad atoms
add without loss. -/
theorem sum_integral_norm_lacunaryCZBadAtom_le_two_mul_integral_norm
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ)
    (U : Finset (Euclidean d × ℤ))
    (hdisj : (↑U : Set (Euclidean d × ℤ)).PairwiseDisjoint lacunaryCZBall)
    (hf : Integrable f volume) :
    (∑ a ∈ U, ∫ x, ‖lacunaryCZBadAtom f a x‖) ≤
      2 * ∫ x, ‖f x‖ := by
  have hsum : (∑ a ∈ U, ∫ x, ‖lacunaryCZBadAtom f a x‖) ≤
      2 * (∑ a ∈ U, ∫ x in lacunaryCZBall a, ‖f x‖) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha =>
      integral_norm_lacunaryCZBadAtom_le_two_mul_setIntegral_norm f a hf
  have hunion :
      (∑ a ∈ U, ∫ x in lacunaryCZBall a, ‖f x‖) =
        ∫ x in ⋃ a ∈ U, lacunaryCZBall a, ‖f x‖ := by
    symm
    exact integral_biUnion_finset U
      (fun _ _ => Metric.isOpen_ball.measurableSet) hdisj
      (fun _ _ => hf.norm.integrableOn)
  have hglobal : (∫ x in ⋃ a ∈ U, lacunaryCZBall a, ‖f x‖) ≤
      ∫ x, ‖f x‖ :=
    setIntegral_le_integral hf.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  calc
    (∑ a ∈ U, ∫ x, ‖lacunaryCZBadAtom f a x‖) ≤
        2 * (∑ a ∈ U, ∫ x in lacunaryCZBall a, ‖f x‖) := hsum
    _ = 2 * ∫ x in ⋃ a ∈ U, lacunaryCZBall a, ‖f x‖ := by rw [hunion]
    _ ≤ 2 * ∫ x, ‖f x‖ :=
      mul_le_mul_of_nonneg_left hglobal (by norm_num)

/-- On one selected ball the good part is exactly the corresponding ball
average.  Pairwise disjointness is used only to kill the other atoms. -/
theorem lacunaryCZGoodPart_eq_ballAverage_of_mem
    {d : Nat} (f : Euclidean d → ℂ)
    (U : Finset (Euclidean d × ℤ))
    (hdisj : (↑U : Set (Euclidean d × ℤ)).PairwiseDisjoint lacunaryCZBall)
    {a : Euclidean d × ℤ} (ha : a ∈ U) {x : Euclidean d}
    (hx : x ∈ lacunaryCZBall a) :
    lacunaryCZGoodPart f U x = lacunaryCZBallAverage f a := by
  have hsum : (∑ b ∈ U, lacunaryCZBadAtom f b x) = lacunaryCZBadAtom f a x := by
    rw [Finset.sum_eq_single a]
    · intro b hb hba
      have hdis : Disjoint (lacunaryCZBall a) (lacunaryCZBall b) :=
        hdisj ha hb hba.symm
      have hxb : x ∉ lacunaryCZBall b := by
        intro hxb
        exact Set.disjoint_left.1 hdis hx hxb
      simp only [lacunaryCZBadAtom, Set.indicator_of_notMem hxb]
    · intro hnot
      exact (hnot ha).elim
  rw [lacunaryCZGoodPart, hsum]
  simp only [lacunaryCZBadAtom, Set.indicator_of_mem hx]
  ring

/-- Away from all selected balls, the good part agrees with the input. -/
theorem lacunaryCZGoodPart_eq_of_not_mem_biUnion
    {d : Nat} (f : Euclidean d → ℂ)
    (U : Finset (Euclidean d × ℤ)) {x : Euclidean d}
    (hx : x ∉ ⋃ a ∈ U, lacunaryCZBall a) :
    lacunaryCZGoodPart f U x = f x := by
  have hsum : (∑ a ∈ U, lacunaryCZBadAtom f a x) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hxa : x ∉ lacunaryCZBall a := by
      intro hxa
      apply hx
      exact Set.mem_iUnion₂.mpr ⟨a, ha, hxa⟩
    simp only [lacunaryCZBadAtom, Set.indicator_of_notMem hxa]
  simp only [lacunaryCZGoodPart, hsum, sub_zero]

/-- Literal outside and selected-average bounds give the `L∞` bound for the
finite good part.  A maximal dyadic-cube selection supplies precisely these
two hypotheses. -/
theorem norm_lacunaryCZGoodPart_le_of_outside_and_average_bounds
    {d : Nat} (f : Euclidean d → ℂ) (U : Finset (Euclidean d × ℤ))
    (hdisj : (↑U : Set (Euclidean d × ℤ)).PairwiseDisjoint lacunaryCZBall)
    (lambda : ℝ)
    (houtside : ∀ x : Euclidean d,
      x ∉ ⋃ a ∈ U, lacunaryCZBall a → ‖f x‖ ≤ lambda)
    (haverage : ∀ a ∈ U, ‖lacunaryCZBallAverage f a‖ ≤ lambda)
    (x : Euclidean d) :
    ‖lacunaryCZGoodPart f U x‖ ≤ lambda := by
  by_cases hx : x ∈ ⋃ a ∈ U, lacunaryCZBall a
  · rcases Set.mem_iUnion₂.mp hx with ⟨a, ha, hxa⟩
    rw [lacunaryCZGoodPart_eq_ballAverage_of_mem f U hdisj ha hxa]
    exact haverage a ha
  · rw [lacunaryCZGoodPart_eq_of_not_mem_biUnion f U hx]
    exact houtside x hx

/-- The good part has `L¹` mass at most three times that of the input.  The
constant is deliberately explicit: one copy of `f` and the two copies paid
by the canonical bad atoms. -/
theorem integral_norm_lacunaryCZGoodPart_le_three_mul_integral_norm
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ)
    (U : Finset (Euclidean d × ℤ))
    (hdisj : (↑U : Set (Euclidean d × ℤ)).PairwiseDisjoint lacunaryCZBall)
    (hf : Integrable f volume) :
    (∫ x, ‖lacunaryCZGoodPart f U x‖) ≤ 3 * ∫ x, ‖f x‖ := by
  have hgoodint : Integrable (lacunaryCZGoodPart f U) volume := by
    unfold lacunaryCZGoodPart
    apply hf.sub
    exact integrable_finsetSum U fun a _ => integrable_lacunaryCZBadAtom f a hf
  have hsumint : Integrable (fun x : Euclidean d =>
      ∑ a ∈ U, ‖lacunaryCZBadAtom f a x‖) volume :=
    integrable_finsetSum U fun a _ => (integrable_lacunaryCZBadAtom f a hf).norm
  have hright : Integrable (fun x : Euclidean d =>
      ‖f x‖ + ∑ a ∈ U, ‖lacunaryCZBadAtom f a x‖) volume :=
    hf.norm.add hsumint
  have hpoint (x : Euclidean d) :
      ‖lacunaryCZGoodPart f U x‖ ≤
        ‖f x‖ + ∑ a ∈ U, ‖lacunaryCZBadAtom f a x‖ := by
    unfold lacunaryCZGoodPart
    exact (norm_sub_le _ _).trans
      (add_le_add_right (norm_sum_le U fun a => lacunaryCZBadAtom f a x) _)
  have hmono : (∫ x, ‖lacunaryCZGoodPart f U x‖) ≤
      ∫ x, ‖f x‖ + ∑ a ∈ U, ‖lacunaryCZBadAtom f a x‖ :=
    integral_mono hgoodint.norm hright hpoint
  have hbad :=
    sum_integral_norm_lacunaryCZBadAtom_le_two_mul_integral_norm f U hdisj hf
  calc
    (∫ x, ‖lacunaryCZGoodPart f U x‖) ≤
        ∫ x, ‖f x‖ + ∑ a ∈ U, ‖lacunaryCZBadAtom f a x‖ := hmono
    _ = (∫ x, ‖f x‖) +
        ∑ a ∈ U, ∫ x, ‖lacunaryCZBadAtom f a x‖ := by
      rw [integral_add hf.norm hsumint,
        integral_finsetSum U fun a _ => (integrable_lacunaryCZBadAtom f a hf).norm]
    _ ≤ (∫ x, ‖f x‖) + 2 * ∫ x, ‖f x‖ :=
      add_le_add_right hbad _
    _ = 3 * ∫ x, ‖f x‖ := by ring

/-- Combining the literal `L∞` good-part bound with its finite `L¹` bound
gives the `L²` estimate required by the lacunary endpoint. -/
theorem integral_norm_sq_lacunaryCZGoodPart_le_three_mul_lambda_mul_integral_norm
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ)
    (U : Finset (Euclidean d × ℤ))
    (hdisj : (↑U : Set (Euclidean d × ℤ)).PairwiseDisjoint lacunaryCZBall)
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (houtside : ∀ x : Euclidean d,
      x ∉ ⋃ a ∈ U, lacunaryCZBall a → ‖f x‖ ≤ lambda)
    (haverage : ∀ a ∈ U, ‖lacunaryCZBallAverage f a‖ ≤ lambda)
    (hf : Integrable f volume) :
    (∫ x, ‖lacunaryCZGoodPart f U x‖ ^ 2) ≤
      (3 * lambda) * ∫ x, ‖f x‖ := by
  have hgoodint : Integrable (lacunaryCZGoodPart f U) volume := by
    unfold lacunaryCZGoodPart
    apply hf.sub
    exact integrable_finsetSum U fun a _ => integrable_lacunaryCZBadAtom f a hf
  have hbound (x : Euclidean d) : ‖lacunaryCZGoodPart f U x‖ ≤ lambda :=
    norm_lacunaryCZGoodPart_le_of_outside_and_average_bounds f U hdisj lambda
      houtside haverage x
  have hright : Integrable (fun x : Euclidean d =>
      lambda * ‖lacunaryCZGoodPart f U x‖) volume :=
    hgoodint.norm.const_mul lambda
  have hleft : Integrable (fun x : Euclidean d =>
      ‖lacunaryCZGoodPart f U x‖ ^ 2) volume := by
    refine hright.mono' (hgoodint.norm.aestronglyMeasurable.pow 2) ?_
    filter_upwards with x
    have hnorm : 0 ≤ ‖lacunaryCZGoodPart f U x‖ := norm_nonneg _
    have hpoint' : ‖lacunaryCZGoodPart f U x‖ ^ 2 ≤
        lambda * ‖lacunaryCZGoodPart f U x‖ := by
      calc
        ‖lacunaryCZGoodPart f U x‖ ^ 2 =
            ‖lacunaryCZGoodPart f U x‖ * ‖lacunaryCZGoodPart f U x‖ := by ring
        _ ≤ lambda * ‖lacunaryCZGoodPart f U x‖ :=
          mul_le_mul_of_nonneg_right (hbound x) hnorm
    simpa only [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (mul_nonneg hlambda hnorm)] using hpoint'
  have hpoint (x : Euclidean d) :
      ‖lacunaryCZGoodPart f U x‖ ^ 2 ≤
        lambda * ‖lacunaryCZGoodPart f U x‖ := by
    have hnorm : 0 ≤ ‖lacunaryCZGoodPart f U x‖ := norm_nonneg _
    calc
      ‖lacunaryCZGoodPart f U x‖ ^ 2 =
          ‖lacunaryCZGoodPart f U x‖ * ‖lacunaryCZGoodPart f U x‖ := by ring
      _ ≤ lambda * ‖lacunaryCZGoodPart f U x‖ :=
        mul_le_mul_of_nonneg_right (hbound x) hnorm
  have hL1 :=
    integral_norm_lacunaryCZGoodPart_le_three_mul_integral_norm f U hdisj hf
  calc
    (∫ x, ‖lacunaryCZGoodPart f U x‖ ^ 2) ≤
        ∫ x, lambda * ‖lacunaryCZGoodPart f U x‖ :=
      integral_mono hleft hright hpoint
    _ = lambda * ∫ x, ‖lacunaryCZGoodPart f U x‖ := by
      rw [integral_const_mul]
    _ ≤ lambda * (3 * ∫ x, ‖f x‖) :=
      mul_le_mul_of_nonneg_left hL1 hlambda
    _ = (3 * lambda) * ∫ x, ‖f x‖ := by ring

/-- The finite good--bad decomposition is a pointwise identity. -/
theorem lacunaryCZGoodPart_add_sum_eq
    {d : Nat} (f : Euclidean d → ℂ) (U : Finset (Euclidean d × ℤ))
    (x : Euclidean d) :
    f x = lacunaryCZGoodPart f U x +
      ∑ a ∈ U, lacunaryCZBadAtom f a x := by
  simp only [lacunaryCZGoodPart]
  ring

/-- The good term remains integrable on a finite selected family. -/
theorem integrable_lacunaryCZGoodPart
    {d : Nat} (f : Euclidean d → ℂ) (U : Finset (Euclidean d × ℤ))
    (hf : Integrable f volume) :
    Integrable (lacunaryCZGoodPart f U) volume := by
  unfold lacunaryCZGoodPart
  apply hf.sub
  exact integrable_finsetSum _ fun a _ => integrable_lacunaryCZBadAtom f a hf

/-- The bad-average inequalities of a finite disjoint family force the
selected total mass to be controlled by the input `L¹` mass.  This is the
measure-theoretic half of the finite Calderón--Zygmund selection. -/
theorem lacunaryCZ_selected_mass_le_lintegral
    {d : Nat} (f : Euclidean d → ℂ) (lambda : ℝ)
    (U : Finset (Euclidean d × ℤ))
    (hdisj : (↑U : Set (Euclidean d × ℤ)).PairwiseDisjoint lacunaryCZBall)
    (hbad : ∀ a ∈ U,
      ENNReal.ofReal lambda * volume (lacunaryCZBall a) ≤
        ∫⁻ x in lacunaryCZBall a, ENNReal.ofReal ‖f x‖) :
    ENNReal.ofReal lambda * (∑ a ∈ U, volume (lacunaryCZBall a)) ≤
      ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  have hpoint (a : Euclidean d × ℤ) (ha : a ∈ U) :
      ENNReal.ofReal lambda * volume (lacunaryCZBall a) ≤
        ∫⁻ x in lacunaryCZBall a, ENNReal.ofReal ‖f x‖ := hbad a ha
  have hsum :
      ENNReal.ofReal lambda * (∑ a ∈ U, volume (lacunaryCZBall a)) ≤
        ∑ a ∈ U, ∫⁻ x in lacunaryCZBall a, ENNReal.ofReal ‖f x‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha => hpoint a ha
  have hunion :
      (∑ a ∈ U, ∫⁻ x in lacunaryCZBall a, ENNReal.ofReal ‖f x‖) =
        ∫⁻ x in ⋃ a ∈ U, lacunaryCZBall a, ENNReal.ofReal ‖f x‖ := by
    symm
    exact lintegral_biUnion_finset hdisj
      (fun _ _ => Metric.isOpen_ball.measurableSet) _
  calc
    ENNReal.ofReal lambda * (∑ a ∈ U, volume (lacunaryCZBall a)) ≤
        ∑ a ∈ U, ∫⁻ x in lacunaryCZBall a, ENNReal.ofReal ‖f x‖ := hsum
    _ = ∫⁻ x in ⋃ a ∈ U, lacunaryCZBall a, ENNReal.ofReal ‖f x‖ := hunion
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (μ := volume)
          (f := fun x : Euclidean d => ENNReal.ofReal ‖f x‖)
          (subset_univ (⋃ a ∈ U, lacunaryCZBall a)))

/-- Real-valued version of the selected mass estimate.  It is convenient
when the Calderón data are later paired with the real `L²` good bound. -/
theorem lacunaryCZ_selected_real_volume_mass_le_integral_norm
    {d : Nat} (f : Euclidean d → ℂ) (lambda : ℝ)
    (U : Finset (Euclidean d × ℤ))
    (hdisj : (↑U : Set (Euclidean d × ℤ)).PairwiseDisjoint lacunaryCZBall)
    (hbad : ∀ a ∈ U,
      lambda * (volume (lacunaryCZBall a)).toReal ≤
        ∫ x in lacunaryCZBall a, ‖f x‖)
    (hf : Integrable f volume) :
    lambda * (∑ a ∈ U, (volume (lacunaryCZBall a)).toReal) ≤
      ∫ x, ‖f x‖ := by
  have hsum : lambda * (∑ a ∈ U, (volume (lacunaryCZBall a)).toReal) ≤
      ∑ a ∈ U, ∫ x in lacunaryCZBall a, ‖f x‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha => hbad a ha
  have hunion :
      (∑ a ∈ U, ∫ x in lacunaryCZBall a, ‖f x‖) =
        ∫ x in ⋃ a ∈ U, lacunaryCZBall a, ‖f x‖ := by
    symm
    exact integral_biUnion_finset U
      (fun _ _ => Metric.isOpen_ball.measurableSet) hdisj
      (fun _ _ => hf.norm.integrableOn)
  have hglobal : (∫ x in ⋃ a ∈ U, lacunaryCZBall a, ‖f x‖) ≤
      ∫ x, ‖f x‖ :=
    setIntegral_le_integral hf.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  calc
    lambda * (∑ a ∈ U, (volume (lacunaryCZBall a)).toReal) ≤
        ∑ a ∈ U, ∫ x in lacunaryCZBall a, ‖f x‖ := hsum
    _ = ∫ x in ⋃ a ∈ U, lacunaryCZBall a, ‖f x‖ := hunion
    _ ≤ ∫ x, ‖f x‖ := hglobal

/-- The selected real-volume bound controls the sum of the physical radius
powers, with the exact fixed unit-ball constant left visible. -/
theorem sum_lacunaryCZ_radius_pow_le_inv_lambda_unitBall_mul_integral_norm
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ) {lambda : ℝ}
    (hlambda : 0 < lambda) (U : Finset (Euclidean d × ℤ))
    (hdisj : (↑U : Set (Euclidean d × ℤ)).PairwiseDisjoint lacunaryCZBall)
    (hbad : ∀ a ∈ U,
      lambda * (volume (lacunaryCZBall a)).toReal ≤
        ∫ x in lacunaryCZBall a, ‖f x‖)
    (hf : Integrable f volume) :
    (∑ a ∈ U, ((2 : ℝ) ^ a.2) ^ d) ≤
      (lambda * (volume (Metric.ball (0 : Euclidean d) 1)).toReal)⁻¹ *
        ∫ x, ‖f x‖ := by
  let V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal
  have hV : 0 < V := by
    dsimp [V]
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos volume (0 : Euclidean d) (by norm_num)).ne'
      measure_ball_lt_top.ne
  have hsumvol : (∑ a ∈ U, (volume (lacunaryCZBall a)).toReal) =
      V * (∑ a ∈ U, ((2 : ℝ) ^ a.2) ^ d) := by
    simp_rw [volume_lacunaryCZBall_toReal_eq_radius_pow_mul_unitBall]
    calc
      (∑ a ∈ U, ((2 : ℝ) ^ a.2) ^ d *
          (volume (Metric.ball (0 : Euclidean d) 1)).toReal) =
          ∑ a ∈ U, (volume (Metric.ball (0 : Euclidean d) 1)).toReal *
            ((2 : ℝ) ^ a.2) ^ d := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
      _ = V * (∑ a ∈ U, ((2 : ℝ) ^ a.2) ^ d) := by
        simp only [V, Finset.mul_sum]
  have hmass :=
    lacunaryCZ_selected_real_volume_mass_le_integral_norm f lambda U hdisj hbad hf
  have hmass' : (lambda * V) * (∑ a ∈ U, ((2 : ℝ) ^ a.2) ^ d) ≤
      ∫ x, ‖f x‖ := by
    rw [hsumvol] at hmass
    simpa only [mul_assoc] using hmass
  have hcoef : 0 < lambda * V := mul_pos hlambda hV
  calc
    (∑ a ∈ U, ((2 : ℝ) ^ a.2) ^ d) =
        (lambda * V)⁻¹ *
          ((lambda * V) * (∑ a ∈ U, ((2 : ℝ) ^ a.2) ^ d)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hcoef.ne', one_mul]
    _ ≤ (lambda * V)⁻¹ * ∫ x, ‖f x‖ :=
      mul_le_mul_of_nonneg_left hmass' (inv_nonneg.mpr hcoef.le)

/-- The fourfold exceptional set of a finite selected family has the
classical weak-`L¹` bound.  The factor is kept as the exact Euclidean volume
factor, rather than hidden in a generic doubling constant. -/
theorem lacunaryCZ_enlarged_exceptional_measure_le
    {d : Nat} [NeZero d] (f : Euclidean d → ℂ) (lambda : ℝ)
    (U : Finset (Euclidean d × ℤ))
    (hdisj : (↑U : Set (Euclidean d × ℤ)).PairwiseDisjoint lacunaryCZBall)
    (hbad : ∀ a ∈ U,
      ENNReal.ofReal lambda * volume (lacunaryCZBall a) ≤
        ∫⁻ x in lacunaryCZBall a, ENNReal.ofReal ‖f x‖) :
    ENNReal.ofReal lambda * volume
        (⋃ a ∈ U, lacunaryCZBallEnlarged a) ≤
      (ENNReal.ofReal (4 : ℝ)) ^ d * ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  have hmeasure : volume (⋃ a ∈ U, lacunaryCZBallEnlarged a) ≤
      ∑ a ∈ U, volume (lacunaryCZBallEnlarged a) :=
    measure_biUnion_finset_le U lacunaryCZBallEnlarged
  have hmass := lacunaryCZ_selected_mass_le_lintegral f lambda U hdisj hbad
  calc
    ENNReal.ofReal lambda * volume
        (⋃ a ∈ U, lacunaryCZBallEnlarged a) ≤
        ENNReal.ofReal lambda *
          (∑ a ∈ U, volume (lacunaryCZBallEnlarged a)) :=
      by
        simpa only [mul_comm] using
          (mul_le_mul_left hmeasure (ENNReal.ofReal lambda))
    _ = ENNReal.ofReal lambda *
          (∑ a ∈ U, (ENNReal.ofReal (4 : ℝ)) ^ d *
            volume (lacunaryCZBall a)) := by
          simp_rw [volume_lacunaryCZBall_enlarged]
    _ = (ENNReal.ofReal (4 : ℝ)) ^ d *
          (ENNReal.ofReal lambda *
            ∑ a ∈ U, volume (lacunaryCZBall a)) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ ≤ (ENNReal.ofReal (4 : ℝ)) ^ d *
          ∫⁻ x, ENNReal.ofReal ‖f x‖ :=
      by
        simpa only [mul_comm] using
          (mul_le_mul_left hmass ((ENNReal.ofReal (4 : ℝ)) ^ d))

end

end LeanSpherical.HarmonicAnalysis
