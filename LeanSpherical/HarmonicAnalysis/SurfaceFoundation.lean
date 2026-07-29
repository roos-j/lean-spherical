/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceMeasure

/-!
# Concrete facts about the Euclidean surface measure

This file records elementary, theorem-backed properties of the concrete
measure `unitSurfaceMeasure`.  They supply the normalization and the
`L∞` endpoint that are used independently of stationary phase in the
spherical maximal argument.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- In every positive dimension, the concrete surface measure has positive
total mass. -/
theorem unitSurfaceMeasure_univ_pos {d : ℕ} (hd : 0 < d) :
    0 < unitSurfaceMeasure d univ := by
  rw [Measure.measure_univ_pos]
  unfold unitSurfaceMeasure
  let i : Fin d := ⟨0, hd⟩
  letI : Nonempty (Fin d) := ⟨i⟩
  exact Measure.toSphere_ne_zero (volume : Measure (Euclidean d))

/-- The normalizing mass of the unit sphere is positive in every positive
dimension. -/
theorem surfaceMass_pos {d : ℕ} (hd : 0 < d) : 0 < surfaceMass d := by
  unfold surfaceMass
  exact ENNReal.toReal_pos (ne_of_gt (unitSurfaceMeasure_univ_pos hd))
    (measure_ne_top _ _)

/-- The normalizing mass can be inverted in every positive dimension. -/
theorem surfaceMass_ne_zero {d : ℕ} (hd : 0 < d) : surfaceMass d ≠ 0 :=
  ne_of_gt (surfaceMass_pos hd)

/-- The concrete surface average is translation covariant. -/
theorem sphericalAverage_translate (d : ℕ) (f : Euclidean d → ℂ) (r : ℝ)
    (a x : Euclidean d) :
    sphericalAverage d (fun y => f (a + y)) r x = sphericalAverage d f r (a + x) := by
  unfold sphericalAverage
  apply integral_congr_ae
  filter_upwards with ω
  simp only [add_assoc]

/-- Spherical averaging commutes with simultaneous Euclidean dilations of the
input and radius. -/
theorem sphericalAverage_dilate (d : ℕ) (f : Euclidean d → ℂ) (a r : ℝ)
    (x : Euclidean d) :
    sphericalAverage d (fun y => f (a • y)) r x =
      sphericalAverage d f (a * r) (a • x) := by
  unfold sphericalAverage
  apply integral_congr_ae
  filter_upwards with ω
  simp only [smul_add, smul_smul]

/-- The mass-normalized spherical average has the same simultaneous dilation
covariance. -/
theorem normalizedSphericalAverage_dilate (d : ℕ) (f : Euclidean d → ℂ)
    (a r : ℝ) (x : Euclidean d) :
    normalizedSphericalAverage d (fun y => f (a • y)) r x =
      normalizedSphericalAverage d f (a * r) (a • x) := by
  unfold normalizedSphericalAverage
  rw [sphericalAverage_dilate]

/-- Dilation identifies the literal compact-radius maximal norm on `[1, 2]`
with the corresponding norm on `[a, 2a]`. -/
theorem iSup_ennreal_norm_sphericalAverage_dilate_local
    {d : ℕ} (f : Euclidean d → ℂ) {a : ℝ} (ha : 0 < a) (x : Euclidean d) :
    (⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal ‖sphericalAverage d (fun y => f (a • y)) r.1 x‖) =
      ⨆ s : Icc a (a * 2),
        ENNReal.ofReal ‖sphericalAverage d f s.1 (a • x)‖ := by
  apply le_antisymm
  · apply iSup_le
    intro r
    let s : Icc a (a * 2) := ⟨a * r.1,
      by simpa using mul_le_mul_of_nonneg_left r.2.1 ha.le,
      by
        calc
          a * r.1 ≤ a * 2 := mul_le_mul_of_nonneg_left r.2.2 ha.le
          _ = a * 2 := rfl⟩
    rw [sphericalAverage_dilate d f a r.1 x]
    exact le_iSup (fun s : Icc a (a * 2) =>
      ENNReal.ofReal ‖sphericalAverage d f s.1 (a • x)‖) s
  · apply iSup_le
    intro s
    let r : Icc (1 : ℝ) 2 := ⟨s.1 / a,
      (le_div_iff₀ ha).2 (by simpa using s.2.1),
      (div_le_iff₀ ha).2 (by simpa [mul_comm] using s.2.2)⟩
    have hmul : a * r.1 = s.1 := by
      dsimp only [r]
      field_simp
    calc
      ENNReal.ofReal ‖sphericalAverage d f s.1 (a • x)‖ =
          ENNReal.ofReal ‖sphericalAverage d (fun y => f (a • y)) r.1 x‖ := by
        rw [sphericalAverage_dilate d f a r.1 x, hmul]
      _ ≤ ⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal ‖sphericalAverage d (fun y => f (a • y)) r.1 x‖ :=
        le_iSup (fun r : Icc (1 : ℝ) 2 =>
          ENNReal.ofReal ‖sphericalAverage d (fun y => f (a • y)) r.1 x‖) r

/-- The same local-radius dilation identity for the mass-normalized spherical
averages used in Stein's theorem. -/
theorem iSup_ennreal_norm_normalizedSphericalAverage_dilate_local
    {d : ℕ} (f : Euclidean d → ℂ) {a : ℝ} (ha : 0 < a) (x : Euclidean d) :
    (⨆ r : Icc (1 : ℝ) 2,
      ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖) =
      ⨆ s : Icc a (a * 2),
        ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 (a • x)‖ := by
  apply le_antisymm
  · apply iSup_le
    intro r
    let s : Icc a (a * 2) := ⟨a * r.1,
      by simpa using mul_le_mul_of_nonneg_left r.2.1 ha.le,
      by
        calc
          a * r.1 ≤ a * 2 := mul_le_mul_of_nonneg_left r.2.2 ha.le
          _ = a * 2 := rfl⟩
    rw [normalizedSphericalAverage_dilate d f a r.1 x]
    exact le_iSup (fun s : Icc a (a * 2) =>
      ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 (a • x)‖) s
  · apply iSup_le
    intro s
    let r : Icc (1 : ℝ) 2 := ⟨s.1 / a,
      (le_div_iff₀ ha).2 (by simpa using s.2.1),
      (div_le_iff₀ ha).2 (by simpa [mul_comm] using s.2.2)⟩
    have hmul : a * r.1 = s.1 := by
      dsimp only [r]
      field_simp
    calc
      ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 (a • x)‖ =
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖ := by
        rw [normalizedSphericalAverage_dilate d f a r.1 x, hmul]
      _ ≤ ⨆ r : Icc (1 : ℝ) 2,
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖ :=
        le_iSup (fun r : Icc (1 : ℝ) 2 =>
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖) r

/-- The positive-radius normalized maximal function is the supremum of its
literal dyadic radius blocks. -/
theorem normalizedSphericalMaximal_eq_iSup_dyadic_radius_blocks
    {d : ℕ} (f : Euclidean d → ℂ) (x : Euclidean d) :
    normalizedSphericalMaximal d f x =
      ⨆ k : ℤ, ⨆ r : Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)),
        ENNReal.ofReal ‖normalizedSphericalAverage d f r.1 x‖ := by
  unfold normalizedSphericalMaximal
  apply le_antisymm
  · apply iSup_le
    intro t
    obtain ⟨k, hk⟩ := exists_mem_Ico_zpow t.2 (by norm_num : (1 : ℝ) < 2)
    let r : Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) := ⟨t.1, hk.1, hk.2.le⟩
    exact le_iSup_of_le k
      (le_iSup (fun r : Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) =>
        ENNReal.ofReal ‖normalizedSphericalAverage d f r.1 x‖) r)
  · apply iSup_le
    intro k
    apply iSup_le
    intro r
    have hr : 0 < r.1 :=
      lt_of_lt_of_le (zpow_pos (by norm_num : (0 : ℝ) < 2) k) r.2.1
    exact le_iSup (fun t : Ioi (0 : ℝ) =>
      ENNReal.ofReal ‖normalizedSphericalAverage d f t.1 x‖) ⟨r.1, hr⟩

/-- After splitting radii into dyadic blocks, every block is exactly a unit
radius block applied to the correspondingly dilated input. -/
theorem normalizedSphericalMaximal_eq_iSup_dyadic_local
    {d : ℕ} (f : Euclidean d → ℂ) (x : Euclidean d) :
    normalizedSphericalMaximal d f x =
      ⨆ k : ℤ, ⨆ r : Icc (1 : ℝ) 2,
        ENNReal.ofReal ‖normalizedSphericalAverage d
          (fun y => f (((2 : ℝ) ^ k) • y)) r.1 (((2 : ℝ) ^ k)⁻¹ • x)‖ := by
  rw [normalizedSphericalMaximal_eq_iSup_dyadic_radius_blocks]
  apply iSup_congr
  intro k
  let a : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by
    dsimp [a]
    exact zpow_pos (by norm_num) _
  have hscale : a * 2 = (2 : ℝ) ^ (k + 1) := by
    dsimp [a]
    calc
      (2 : ℝ) ^ k * 2 = (2 : ℝ) ^ k * (2 : ℝ) ^ (1 : ℤ) := by norm_num
      _ = (2 : ℝ) ^ (k + 1) := (zpow_add₀ (by norm_num) k 1).symm
  have hlocal :=
    iSup_ennreal_norm_normalizedSphericalAverage_dilate_local f ha (a⁻¹ • x)
  rw [hscale] at hlocal
  simpa only [a, smul_smul, mul_inv_cancel₀ ha.ne', one_smul] using hlocal.symm

/-- Positive dilation conjugates the literal normalized maximal function to
itself. -/
theorem normalizedSphericalMaximal_dilate
    {d : ℕ} (f : Euclidean d → ℂ) {a : ℝ} (ha : 0 < a) (x : Euclidean d) :
    normalizedSphericalMaximal d (fun y => f (a • y)) x =
      normalizedSphericalMaximal d f (a • x) := by
  unfold normalizedSphericalMaximal
  apply le_antisymm
  · apply iSup_le
    intro r
    let s : Ioi (0 : ℝ) := ⟨a * r.1, mul_pos ha r.2⟩
    rw [normalizedSphericalAverage_dilate]
    exact le_iSup (fun s : Ioi (0 : ℝ) =>
      ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 (a • x)‖) s
  · apply iSup_le
    intro s
    let r : Ioi (0 : ℝ) := ⟨s.1 / a, div_pos s.2 ha⟩
    have hmul : a * r.1 = s.1 := by
      dsimp only [r]
      field_simp
    calc
      ENNReal.ofReal ‖normalizedSphericalAverage d f s.1 (a • x)‖ =
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖ := by
        rw [normalizedSphericalAverage_dilate d f a r.1 x, hmul]
      _ ≤ ⨆ r : Ioi (0 : ℝ),
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖ :=
        le_iSup (fun r : Ioi (0 : ℝ) =>
          ENNReal.ofReal ‖normalizedSphericalAverage d (fun y => f (a • y)) r.1 x‖) r

/-- The concrete normalized maximal function is subadditive on continuous
inputs. -/
theorem normalizedSphericalMaximal_add_le
    {d : ℕ} (f g : Euclidean d → ℂ) (hf : Continuous f) (hg : Continuous g)
    (x : Euclidean d) :
    normalizedSphericalMaximal d (f + g) x ≤
      normalizedSphericalMaximal d f x + normalizedSphericalMaximal d g x := by
  unfold normalizedSphericalMaximal
  apply iSup_le
  intro r
  have hint (h : Euclidean d → ℂ) (hh : Continuous h) : Integrable
      (fun ω : sphere (0 : Euclidean d) 1 => h (x + r.1 • (ω : Euclidean d)))
      (unitSurfaceMeasure d) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hh.comp
        ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => x).add
          ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => r.1).smul
            continuous_subtype_val))
    · exact HasCompactSupport.of_compactSpace _
  have havg : normalizedSphericalAverage d (f + g) r.1 x =
      normalizedSphericalAverage d f r.1 x + normalizedSphericalAverage d g r.1 x := by
    unfold normalizedSphericalAverage sphericalAverage
    change (surfaceMass d : ℂ)⁻¹ *
        ∫ ω : sphere (0 : Euclidean d) 1,
          (f (x + r.1 • (ω : Euclidean d)) + g (x + r.1 • (ω : Euclidean d)))
          ∂unitSurfaceMeasure d = _
    rw [MeasureTheory.integral_add (hint f hf) (hint g hg), mul_add]
  rw [havg]
  calc
    ENNReal.ofReal ‖normalizedSphericalAverage d f r.1 x +
        normalizedSphericalAverage d g r.1 x‖ ≤
        ENNReal.ofReal (‖normalizedSphericalAverage d f r.1 x‖ +
          ‖normalizedSphericalAverage d g r.1 x‖) :=
      ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖normalizedSphericalAverage d f r.1 x‖ +
        ENNReal.ofReal ‖normalizedSphericalAverage d g r.1 x‖ := by
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    _ ≤ normalizedSphericalMaximal d f x + normalizedSphericalMaximal d g x := by
      gcongr
      · exact normalizedSphericalAverage_le_normalizedSphericalMaximal d f r.1 r.2 x
      · exact normalizedSphericalAverage_le_normalizedSphericalMaximal d g r.1 r.2 x

/-- The Fourier phase is homogeneous in the frequency variable. -/
theorem surfacePhase_smul (d : ℕ) (a : ℝ) (ξ : Euclidean d)
    (ω : sphere (0 : Euclidean d) 1) :
    surfacePhase d (a • ξ) ω = (a : ℂ) * surfacePhase d ξ ω := by
  simp only [surfacePhase, inner_smul_right]
  push_cast
  ring

/-- Scaling the frequency only scales the phase inside the concrete
Fourier--Stieltjes integral. -/
theorem surfaceFourier_smul (d : ℕ) (a : ℝ) (ξ : Euclidean d) :
    surfaceFourier d (a • ξ) =
      ∫ ω : sphere (0 : Euclidean d) 1,
        Complex.exp ((a : ℂ) * surfacePhase d ξ ω) ∂unitSurfaceMeasure d := by
  unfold surfaceFourier
  apply integral_congr_ae
  filter_upwards with ω
  rw [surfacePhase_smul]

/-- The normalized average fixes every function at radius zero. -/
theorem normalizedSphericalAverage_zero {d : ℕ} (hd : 0 < d)
    (f : Euclidean d → ℂ) (x : Euclidean d) :
    normalizedSphericalAverage d f 0 x = f x := by
  rw [normalizedSphericalAverage, sphericalAverage_zero]
  change (↑(surfaceMass d) : ℂ)⁻¹ * ((↑(surfaceMass d) : ℂ) * f x) = f x
  have hmass : (↑(surfaceMass d) : ℂ) ≠ 0 := by
    exact_mod_cast surfaceMass_ne_zero hd
  rw [← mul_assoc, inv_mul_cancel₀ hmass, one_mul]

/-- The unnormalized average of a constant is its surface mass times that
constant. -/
theorem sphericalAverage_const (d : ℕ) (c : ℂ) (r : ℝ) (x : Euclidean d) :
    sphericalAverage d (fun _ => c) r x = (surfaceMass d : ℂ) * c := by
  simp [sphericalAverage, surfaceMass]

/-- The normalized average preserves constants in every positive dimension. -/
theorem normalizedSphericalAverage_const {d : ℕ} (hd : 0 < d) (c : ℂ)
    (r : ℝ) (x : Euclidean d) :
    normalizedSphericalAverage d (fun _ => c) r x = c := by
  rw [normalizedSphericalAverage, sphericalAverage_const]
  simp [surfaceMass_ne_zero hd]

/-- The elementary `L∞` bound for the unnormalized spherical average. -/
theorem norm_sphericalAverage_le_surfaceMass_mul (d : ℕ) (f : Euclidean d → ℂ)
    (r : ℝ) (x : Euclidean d) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ‖sphericalAverage d f r x‖ ≤ C * surfaceMass d := by
  unfold sphericalAverage
  apply norm_integral_le_of_norm_le_const
  filter_upwards with ω
  exact hC _

/-- The normalized spherical average is an `L∞` contraction. -/
theorem norm_normalizedSphericalAverage_le {d : ℕ} (hd : 0 < d)
    (f : Euclidean d → ℂ) (r : ℝ) (x : Euclidean d) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) :
    ‖normalizedSphericalAverage d f r x‖ ≤ C := by
  have hmass_pos : 0 < surfaceMass d := surfaceMass_pos hd
  have hmass_nonneg : 0 ≤ surfaceMass d := hmass_pos.le
  calc
    ‖normalizedSphericalAverage d f r x‖ =
        (surfaceMass d)⁻¹ * ‖sphericalAverage d f r x‖ := by
      rw [normalizedSphericalAverage, norm_mul]
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hmass_nonneg]
    _ ≤ (surfaceMass d)⁻¹ * (C * surfaceMass d) := by
      exact mul_le_mul_of_nonneg_left
        (norm_sphericalAverage_le_surfaceMass_mul d f r x hC)
        (inv_nonneg.mpr hmass_nonneg)
    _ = C := by
      calc
        (surfaceMass d)⁻¹ * (C * surfaceMass d) =
            C * ((surfaceMass d)⁻¹ * surfaceMass d) := by ring
        _ = C := by rw [inv_mul_cancel₀ (surfaceMass_ne_zero hd), mul_one]

/-- The normalized spherical maximal function satisfies the pointwise `L∞`
bound inherited from the concrete average. -/
theorem normalizedSphericalMaximal_le_of_norm_le {d : ℕ} (hd : 0 < d)
    (f : Euclidean d → ℂ) (x : Euclidean d) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) :
    normalizedSphericalMaximal d f x ≤ ENNReal.ofReal C := by
  unfold normalizedSphericalMaximal
  apply iSup_le
  intro r
  exact ENNReal.ofReal_le_ofReal
    (norm_normalizedSphericalAverage_le hd f r x hC)

end

end LeanSpherical.HarmonicAnalysis
