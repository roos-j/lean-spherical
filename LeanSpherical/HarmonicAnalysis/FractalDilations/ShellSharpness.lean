/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.ShellBump
import LeanSpherical.HarmonicAnalysis.FractalDilations.ShellVolume
import LeanSpherical.HarmonicAnalysis.FractalDilations.SharpnessNormalization

/-!
# The spherical-cap sharpness test

This module turns the smooth squared-radius bump from `ShellBump` into the
usual cap obstruction.  The geometric support estimate is kept separate from
the eventual small-scale power comparison, so that every analytic estimate is
available in a directly reusable form.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The support strip of a squared-radius shell lies in an ordinary thin
annulus. -/
theorem squared_shell_subset_thin_annulus
    {d : ℕ} {r δ : ℝ} (hrone : 1 ≤ r) (hδ : 0 < δ) :
    {y : Euclidean d | |‖y‖ ^ 2 - r ^ 2| < 2 * δ} ⊆
      ball (0 : Euclidean d) (r + 2 * δ) \
        closedBall (0 : Euclidean d) (r - 2 * δ) := by
  intro y hy
  have hynonneg : 0 ≤ ‖y‖ := norm_nonneg y
  have hupper : ‖y‖ < r + 2 * δ := by
    by_contra hnot
    have htr : r + 2 * δ ≤ ‖y‖ := le_of_not_gt hnot
    have hfirst : 2 * δ ≤ ‖y‖ - r := by linarith
    have hsecond : 1 ≤ ‖y‖ + r := by linarith
    have hproduct : (2 * δ) * 1 ≤ (‖y‖ - r) * (‖y‖ + r) :=
      mul_le_mul hfirst hsecond zero_le_one (by linarith)
    have hmain : 2 * δ ≤ ‖y‖ ^ 2 - r ^ 2 := by
      convert hproduct using 1 <;> ring
    have habs : 2 * δ ≤ |‖y‖ ^ 2 - r ^ 2| := hmain.trans (le_abs_self _)
    exact (not_le_of_gt hy) habs
  have hlower : r - 2 * δ < ‖y‖ := by
    by_contra hnot
    have htr : ‖y‖ ≤ r - 2 * δ := le_of_not_gt hnot
    have hfirst : 2 * δ ≤ r - ‖y‖ := by linarith
    have hsecond : 1 ≤ r + ‖y‖ := by linarith
    have hproduct : (2 * δ) * 1 ≤ (r - ‖y‖) * (r + ‖y‖) :=
      mul_le_mul hfirst hsecond zero_le_one (by linarith)
    have hmain : 2 * δ ≤ r ^ 2 - ‖y‖ ^ 2 := by
      convert hproduct using 1 <;> ring
    have hnonpos : ‖y‖ ^ 2 - r ^ 2 ≤ 0 := by linarith
    have habs : 2 * δ ≤ |‖y‖ ^ 2 - r ^ 2| := by
      rw [abs_of_nonpos hnonpos]
      linarith
    exact (not_le_of_gt hy) habs
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_zero_right]
    exact hupper
  · rw [mem_closedBall, dist_zero_right]
    exact not_le.mpr hlower

/-- The `Lᵖ` norm of a bounded squared-radius shell is controlled by the
volume of its containing thin annulus. -/
theorem eLpNorm_squared_shell_test_le_annulus
    {d : ℕ} {r δ p : ℝ} (hrone : 1 ≤ r) (hδ : 0 < δ) (hp : 0 < p)
    (f : SchwartzMap (Euclidean d) ℂ)
    (hzero : ∀ y : Euclidean d, 2 * δ ≤ |‖y‖ ^ 2 - r ^ 2| → f y = 0)
    (hbound : ∀ y : Euclidean d, ‖f y‖ ≤ 1) :
    eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤
      volume (ball (0 : Euclidean d) (r + 2 * δ) \
        closedBall (0 : Euclidean d) (r - 2 * δ)) ^ p⁻¹ := by
  let A : Set (Euclidean d) :=
    ball (0 : Euclidean d) (r + 2 * δ) \
      closedBall (0 : Euclidean d) (r - 2 * δ)
  have hAmeas : MeasurableSet A :=
    (isOpen_ball.measurableSet.diff measurableSet_closedBall)
  change eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤ volume A ^ p⁻¹
  calc
    eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤
        eLpNorm (A.indicator fun _ : Euclidean d => (1 : ℂ)) (ENNReal.ofReal p) volume := by
      apply eLpNorm_mono
      intro y
      by_cases hy : y ∈ A
      · rw [Set.indicator_of_mem hy, norm_one]
        exact hbound y
      · rw [Set.indicator_of_notMem hy]
        have hnot : ¬ |‖y‖ ^ 2 - r ^ 2| < 2 * δ := by
          intro hstrip
          exact hy (squared_shell_subset_thin_annulus hrone hδ hstrip)
        rw [hzero y (le_of_not_gt hnot)]
    _ = volume A ^ p⁻¹ := by
      rw [eLpNorm_indicator_const hAmeas
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
      simp only [enorm_one, one_mul, ENNReal.toReal_ofReal hp.le, one_div]

/-- Combining the elementary annulus-volume bound with the support estimate
gives the explicit input estimate used by the cap test. -/
theorem eLpNorm_squared_shell_test_le_thin_annulus_bound
    (d : ℕ) {r δ p : ℝ}
    (hrone : 1 ≤ r) (hrtwo : r ≤ 2) (hδ : 0 < δ) (hδquarter : δ ≤ 1 / 4)
    (hp : 0 < p) (f : SchwartzMap (Euclidean d) ℂ)
    (hzero : ∀ y : Euclidean d, 2 * δ ≤ |‖y‖ ^ 2 - r ^ 2| → f y = 0)
    (hbound : ∀ y : Euclidean d, ‖f y‖ ≤ 1) :
    eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
        volume (ball (0 : Euclidean d) 1)) ^ p⁻¹ := by
  refine (eLpNorm_squared_shell_test_le_annulus hrone hδ hp f hzero hbound).trans ?_
  exact ENNReal.rpow_le_rpow
    (volume_thin_annulus_le d hrone hrtwo hδ hδquarter) (inv_nonneg.mpr hp.le)

/-- The two scale powers in the cap example separate below a sufficiently
small shell thickness.  This is the real-valued form of the comparison; the
next lemma transfers it to `ENNReal` norms. -/
theorem exists_small_squared_shell_gap_real
    {d : ℕ} (hd : 0 < d) {p q C : ℝ}
    (hC : 0 < C) (hp : 0 < p) (hq : 0 < q)
    (hbad : (d : ℝ) * q⁻¹ < p⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      C * (((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
        (volume (ball (0 : Euclidean d) 1)).toReal) ^ p⁻¹ <
      (((δ / 8) ^ d) * (volume (ball (0 : Euclidean d) 1)).toReal) ^ q⁻¹ := by
  let V : ℝ := (volume (ball (0 : Euclidean d) 1)).toReal
  let K : ℝ := 4 * (d : ℝ) * 3 ^ (d - 1)
  have hV : 0 < V := volume_unit_ball_toReal_pos hd
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hB : 0 < (8⁻¹ : ℝ) ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹ := by positivity
  obtain ⟨δ, hδ, hδquarter, hsep⟩ := exists_small_rpow_separation
    (a := (d : ℝ) * q⁻¹) (b := p⁻¹)
    (A := (K * V) ^ p⁻¹)
    (B := (8⁻¹ : ℝ) ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹)
    (C := C) hB hbad
  refine ⟨δ, hδ, hδquarter.le, ?_⟩
  have hleft : C * (K * δ * V) ^ p⁻¹ =
      (C * (K * V) ^ p⁻¹) * δ ^ p⁻¹ := by
    have hrewrite : K * δ * V = (K * V) * δ := by ring
    rw [hrewrite, Real.mul_rpow (mul_nonneg hK.le hV.le) hδ.le]
    ring
  have hright : (((δ / 8) ^ d) * V) ^ q⁻¹ =
      ((8⁻¹ : ℝ) ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹) * δ ^ ((d : ℝ) * q⁻¹) := by
    have hδ8 : 0 ≤ δ / 8 := by positivity
    calc
      (((δ / 8) ^ d) * V) ^ q⁻¹ =
          ((δ / 8) ^ d) ^ q⁻¹ * V ^ q⁻¹ := by
        rw [Real.mul_rpow (pow_nonneg hδ8 _) hV.le]
      _ = (δ / 8) ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ8]
      _ = (δ ^ ((d : ℝ) * q⁻¹) *
          (8⁻¹ : ℝ) ^ ((d : ℝ) * q⁻¹)) * V ^ q⁻¹ := by
        rw [show δ / 8 = δ * (8⁻¹ : ℝ) by ring,
          Real.mul_rpow hδ.le (by positivity)]
      _ = ((8⁻¹ : ℝ) ^ ((d : ℝ) * q⁻¹) * V ^ q⁻¹) *
          δ ^ ((d : ℝ) * q⁻¹) := by ring
  change C * (K * δ * V) ^ p⁻¹ < (((δ / 8) ^ d) * V) ^ q⁻¹
  rw [hleft, hright]
  exact hsep

/-- `ENNReal` form of the small-shell separation, tailored to the input and
output norms in the cap test. -/
theorem exists_small_squared_shell_gap
    {d : ℕ} (hd : 0 < d) {p q C : ℝ}
    (hC : 0 < C) (hp : 0 < p) (hq : 0 < q)
    (hbad : (d : ℝ) * q⁻¹ < p⁻¹) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      ENNReal.ofReal C *
        (ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
          volume (ball (0 : Euclidean d) 1)) ^ p⁻¹ <
      volume (ball (0 : Euclidean d) (δ / 8)) ^ q⁻¹ := by
  let V : ℝ := (volume (ball (0 : Euclidean d) 1)).toReal
  let K : ℝ := 4 * (d : ℝ) * 3 ^ (d - 1)
  obtain ⟨δ, hδ, hδquarter, hreal⟩ :=
    exists_small_squared_shell_gap_real hd hC hp hq hbad
  have hK : 0 < K := by
    dsimp [K]
    have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hKδ : 0 ≤ K * δ := mul_nonneg hK.le hδ.le
  have hunit_top : volume (ball (0 : Euclidean d) 1) ≠ (⊤ : ENNReal) :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := (1 : ℝ))).ne
  let X : ENNReal := ENNReal.ofReal C *
    (ENNReal.ofReal (K * δ) * volume (ball (0 : Euclidean d) 1)) ^ p⁻¹
  let Y : ENNReal := volume (ball (0 : Euclidean d) (δ / 8)) ^ q⁻¹
  have hbase_top : ENNReal.ofReal (K * δ) * volume (ball (0 : Euclidean d) 1) ≠
      (⊤ : ENNReal) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunit_top
  have hXtop : X ≠ (⊤ : ENNReal) := by
    dsimp [X]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le) hbase_top)
  have hYtop : Y ≠ (⊤ : ENNReal) := by
    dsimp [Y]
    exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hq.le)
      (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := δ / 8)).ne
  refine ⟨δ, hδ, hδquarter, ?_⟩
  change X < Y
  apply (ENNReal.toReal_lt_toReal hXtop hYtop).mp
  have hleft : X.toReal = C * (K * δ * V) ^ p⁻¹ := by
    dsimp [X]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le,
      ← ENNReal.toReal_rpow, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hKδ]
  have hright : Y.toReal = (((δ / 8) ^ d) * V) ^ q⁻¹ := by
    dsimp [Y]
    rw [← ENNReal.toReal_rpow,
      volume_ball_toReal d (δ / 8) (by positivity)]
  change X.toReal < Y.toReal
  rw [hleft, hright]
  change C * (K * δ * V) ^ p⁻¹ < (((δ / 8) ^ d) * V) ^ q⁻¹ at hreal
  exact hreal

/-- The smooth thickened-sphere (or spherical-cap) example rules out the
strict region `d / q < 1 / p`. -/
theorem fractalSphericalUnbounded_of_spherical_cap
    {d : ℕ} (hd : 2 ≤ d)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hbad : (d : ℝ) * q⁻¹ < p⁻¹) :
    FractalSphericalUnbounded d E p q := by
  have hd0 : 0 < d := by omega
  have hEpos : E ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one (hE hr).1
  apply fractalSphericalUnbounded_of_large_ratio
  intro C hC
  obtain ⟨r, hr⟩ := hEne
  have hrone : 1 ≤ r := (hE hr).1
  have hrtwo : r ≤ 2 := (hE hr).2
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrone
  obtain ⟨δ, hδ, hδquarter, hgap⟩ :=
    exists_small_squared_shell_gap hd0 hC hp hq hbad
  have hδone : δ ≤ 1 := by linarith
  obtain ⟨f, hfone, hfzero, hfbound⟩ :=
    exists_schwartz_squared_shell_test (d := d) hrpos hrtwo hδ hδone
  let A : ENNReal :=
    (ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
      volume (ball (0 : Euclidean d) 1)) ^ p⁻¹
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd0
  have hKδ : 0 < (4 * (d : ℝ) * 3 ^ (d - 1)) * δ := by positivity
  have hbasepos : 0 < ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
      volume (ball (0 : Euclidean d) 1) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hKδ).ne'
      (Metric.measure_ball_pos volume (0 : Euclidean d) (by norm_num)).ne'
  have hbasetop : ENNReal.ofReal ((4 * (d : ℝ) * 3 ^ (d - 1)) * δ) *
      volume (ball (0 : Euclidean d) 1) ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Euclidean d)) (r := (1 : ℝ))).ne
  refine ⟨f, A, ?_, ?_, ?_, ?_⟩
  · dsimp [A]
    exact (ENNReal.rpow_pos hbasepos hbasetop).ne'
  · dsimp [A]
    exact ENNReal.rpow_ne_top_of_ne_zero hbasepos.ne' hbasetop
  · dsimp [A]
    exact eLpNorm_squared_shell_test_le_thin_annulus_bound d hrone hrtwo hδ hδquarter
      hp f hfzero hfbound
  · calc
      ENNReal.ofReal C * A < volume (ball (0 : Euclidean d) (δ / 8)) ^ q⁻¹ := by
        simpa only [A] using hgap
      _ ≤ eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume :=
        volume_ball_rpow_le_eLpNorm_fractalSphericalMaximalReal_of_squared_shell
          hd0 E hEpos f hr (by linarith [hrone]) hrtwo hδ.le hδone hfone hq

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
