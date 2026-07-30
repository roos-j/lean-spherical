/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.ClusterAverageLower
import LeanSpherical.HarmonicAnalysis.FractalDilations.ClusterOutputGeometry
import LeanSpherical.HarmonicAnalysis.FractalDilations.SharpnessNormLower
import LeanSpherical.HarmonicAnalysis.FractalDilations.SharpnessNormalization

/-!
# Analytic clustered-radius sharpness test

This file assembles the curved tube bump, cap lower bound, and finite output
slab union.  The remaining scale comparison is deliberately separated from
this geometric-analytic construction.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Metric Set ENNReal

noncomputable section

/-- The clustered-radius construction supplies one Schwartz input with the
standard cap-tube input envelope and a lower bound on the whole finite union
of output slabs. -/
theorem exists_cluster_schwartz_test_with_bounds (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ENNReal, 0 < C ∧ C ≠ ⊤ ∧ ∀
      {E : Set ℝ} {r δ σ p q : ℝ} {s : Finset ℝ},
      (1 ≤ r) → r ≤ 2 → 0 < δ → δ ≤ 1 / 20 →
      0 < σ → σ ≤ 1 → δ ≤ σ ^ 2 →
      StrictlySeparated s (δ / 2) → (↑s : Set ℝ) ⊆ E → E ⊆ Ioi (0 : ℝ) → E ⊆ Icc (0 : ℝ) 2 →
      (∀ t ∈ s, |t - r| * σ ^ 2 ≤ δ) → 0 < p → 1 ≤ q →
      ∃ f : SchwartzMap (Euclidean (n + 1)) ℂ,
        eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
          (C * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n)) ^ p⁻¹ ∧
        ENNReal.ofReal (c * σ ^ n) *
            volume (clusterOutputRegion n r δ σ s) ^ (1 / q) ≤
          eLpNorm (fractalSphericalMaximalReal (n + 1) E f)
            (ENNReal.ofReal q) volume := by
  obtain ⟨c, hcpos, hcap⟩ :=
    exists_power_lower_re_normalizedSphericalAverage_of_small_output n
  obtain ⟨C₀, hC₀top, hvolume⟩ := exists_volume_squaredSphericalCapTube_le_power n
  let C : ENNReal := C₀ + 1
  have hCpos : 0 < C := by
    have hone : (1 : ENNReal) ≤ C := by
      dsimp [C]
      exact le_add_of_nonneg_left (show (0 : ENNReal) ≤ C₀ by exact bot_le)
    exact lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hone
  have hCtop : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.add_ne_top.mpr ⟨hC₀top, ENNReal.one_ne_top⟩
  have hCmono : C₀ ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (show (0 : ENNReal) ≤ 1 by norm_num)
  refine ⟨c, hcpos, C, hCpos, hCtop, ?_⟩
  intro E r δ σ p q s hrone hrtwo hδ hδsmall hσ hσone hδσ hsep hsE hEpos hEbound hshort hp hq
  have hδquarter : δ ≤ 1 / 4 := by linarith
  obtain ⟨f, hf_one, hf_zero, hf_nonneg, hf_imag, hf_bound⟩ :=
    exists_schwartz_sphericalCapTube_test hrone hrtwo hδ hδquarter hσ
  refine ⟨f, ?_, ?_⟩
  · calc
      eLpNorm (f : Euclidean (n + 1) → ℂ) (ENNReal.ofReal p) volume ≤
          volume (squaredSphericalCapTube n r (10 * δ) (2 * σ)) ^ p⁻¹ :=
        eLpNorm_schwartz_sphericalCapTube_le hp f hf_zero hf_bound
      _ ≤ (C * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n)) ^ p⁻¹ := by
        have hcoeff :
            C₀ * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n) ≤
              C * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (mul_le_mul_right
              (mul_le_mul_right hCmono (ENNReal.ofReal (10 * δ)))
              (ENNReal.ofReal ((2 * σ) ^ n)))
        exact ENNReal.rpow_le_rpow
          ((hvolume r (10 * δ) (2 * σ) hrone hrtwo (by positivity)
            (by linarith) (by positivity)).trans hcoeff)
          (inv_nonneg.mpr hp.le)
  · let U : Set (Euclidean (n + 1)) := clusterOutputRegion n r δ σ s
    have hU : MeasurableSet U := by
      dsimp [U, clusterOutputRegion]
      exact MeasurableSet.biUnion s.countable_toSet (fun t ht =>
        measurableSet_centeredHorizontalSlab n (δ / (128 * σ)) (δ / 128) (r - t))
    have ha : 0 ≤ c * σ ^ n := by positivity
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have hmax_nonneg (x : Euclidean (n + 1)) :
        0 ≤ fractalSphericalMaximalReal (n + 1) E f x := by
      unfold fractalSphericalMaximalReal
      exact ENNReal.toReal_nonneg
    have hlower (x : Euclidean (n + 1)) (hx : x ∈ U) :
        c * σ ^ n ≤ fractalSphericalMaximalReal (n + 1) E f x := by
      rcases Set.mem_iUnion.mp hx with ⟨t, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨ht, hx⟩
      obtain ⟨hxhor, hxvert⟩ :=
        norm_and_abs_sub_center_le_of_mem_centeredHorizontalSlab hx
      have htbound : t ∈ Icc (0 : ℝ) 2 := hEbound (hsE ht)
      have havg : c * σ ^ n ≤
          (LeanSpherical.HarmonicAnalysis.normalizedSphericalAverage (n + 1)
            (f : Euclidean (n + 1) → ℂ) t x).re :=
        hcap hrone hrtwo htbound.1 htbound.2 hδ hδσ hσ hσone
          (hshort t ht) f hf_one hf_nonneg x hxhor hxvert
      exact havg.trans
        (re_normalizedSphericalAverage_le_fractalSphericalMaximalReal
          (by omega) E hEpos f (hsE ht) x)
    change ENNReal.ofReal (c * σ ^ n) * volume U ^ (1 / q) ≤
      eLpNorm (fractalSphericalMaximalReal (n + 1) E f) (ENNReal.ofReal q) volume
    exact ENNReal.ofReal_mul_volume_rpow_le_eLpNorm_of_lower_bound
      U hU ha hqpos _ hmax_nonneg (fun x hx => hlower x hx)

/-- A scalar gap for the two envelopes of the clustered test normalizes to
failure of every strong-type bound.  This is the analytic interface used by
the upper-spectrum packing argument: all of the remaining work is the
one-variable comparison of the displayed input and output scales. -/
theorem fractalSphericalUnbounded_of_cluster_scale_gaps
    {n : ℕ} {E : Set ℝ} {p q : ℝ}
    (hp : 0 < p) (hq : 1 ≤ q)
    (hgap : ∀ c : ℝ, 0 < c → ∀ K : ENNReal, 0 < K → K ≠ ⊤ → ∀ D : ℝ, 0 < D →
      ∃ r δ σ : ℝ, ∃ s : Finset ℝ,
        1 ≤ r ∧ r ≤ 2 ∧ 0 < δ ∧ δ ≤ 1 / 20 ∧
        0 < σ ∧ σ ≤ 1 ∧ δ ≤ σ ^ 2 ∧
        StrictlySeparated s (δ / 2) ∧ (↑s : Set ℝ) ⊆ E ∧
        E ⊆ Ioi (0 : ℝ) ∧ E ⊆ Icc (0 : ℝ) 2 ∧
        (∀ t ∈ s, |t - r| * σ ^ 2 ≤ δ) ∧
        ENNReal.ofReal D *
            (K * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n)) ^ p⁻¹ <
          ENNReal.ofReal (c * σ ^ n) *
            volume (clusterOutputRegion n r δ σ s) ^ (1 / q)) :
    FractalSphericalUnbounded (n + 1) E p q := by
  obtain ⟨c, hc, K, hK, hKtop, htest⟩ :=
    exists_cluster_schwartz_test_with_bounds n
  apply fractalSphericalUnbounded_of_large_ratio
  intro D hD
  obtain ⟨r, δ, σ, s, hrone, hrtwo, hδ, hδsmall, hσ, hσone, hδσ,
    hsep, hsE, hEpos, hEbound, hshort, hscalar⟩ :=
    hgap c hc K hK hKtop D hD
  obtain ⟨f, hfinput, hfoutput⟩ :=
    htest hrone hrtwo hδ hδsmall hσ hσone hδσ hsep hsE hEpos hEbound hshort
      hp hq
  let A : ENNReal :=
    (K * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n)) ^ p⁻¹
  have hbase_pos :
      0 < K * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n) := by
    positivity
  have hbase_top :
      K * ENNReal.ofReal (10 * δ) * ENNReal.ofReal ((2 * σ) ^ n) ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hKtop ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact (ENNReal.rpow_pos hbase_pos hbase_top).ne'
  have hAtop : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le) hbase_top
  refine ⟨f, A, hA0, hAtop, ?_, ?_⟩
  · simpa only [A] using hfinput
  · exact hscalar.trans_le hfoutput

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
