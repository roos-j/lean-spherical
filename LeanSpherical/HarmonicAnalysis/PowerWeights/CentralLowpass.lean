/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.HardyLittlewoodMaximal
import LeanSpherical.HarmonicAnalysis.PowerWeights.NearOrigin

/-!
# Central-annulus bounds for the low relative-frequency operator

The local weighted argument has one genuinely singular spatial region: near
the origin a negative power weight cannot be compared above with Lebesgue
measure.  For data supported away from that region, every nonzero dyadic-ball
average at a nearby point has a fixed minimum radius, hence is controlled by
the unweighted `L¹` norm.  Away from the origin the power weight is bounded
above by a constant, and the ordinary dyadic Hardy--Littlewood theorem takes
over.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Outside a fixed closed ball, a nonpositive radial power is bounded above
by its value at the radius of that ball. -/
theorem powerWeightedVolume_restrict_compl_closedBall_le_outerPower_smul
    {d : ℕ} {α R : ℝ} (hα : α ≤ 0) (hR : 0 < R) :
    (powerWeightedVolume d α).restrict (Metric.closedBall (0 : Euclidean d) R)ᶜ ≤
      ((ENNReal.ofReal R) ^ α) •
        volume.restrict (Metric.closedBall (0 : Euclidean d) R)ᶜ := by
  let B : Set (Euclidean d) := (Metric.closedBall (0 : Euclidean d) R)ᶜ
  have hB : MeasurableSet B := measurableSet_closedBall.compl
  calc
    (powerWeightedVolume d α).restrict B =
        (volume.restrict B).withDensity (radialPowerWeight d α) := by
      rw [powerWeightedVolume, restrict_withDensity hB]
    _ ≤ (volume.restrict B).withDensity
        (fun _ : Euclidean d => (ENNReal.ofReal R) ^ α) := by
      apply withDensity_mono
      filter_upwards [ae_restrict_mem hB] with x hx
      have hxclosed : x ∉ Metric.closedBall (0 : Euclidean d) R := by
        simpa only [B, mem_compl_iff] using hx
      have hx' : ¬ ‖x‖ ≤ R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hxclosed
      have hRnorm : R ≤ ‖x‖ := (lt_of_not_ge hx').le
      have hnorm : 0 < ‖x‖ := lt_of_lt_of_le hR hRnorm
      rw [radialPowerWeight, ENNReal.ofReal_rpow_of_pos hnorm,
        ENNReal.ofReal_rpow_of_pos hR]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos hR hRnorm hα)
    _ = ((ENNReal.ofReal R) ^ α) • volume.restrict B :=
      withDensity_const _

/-- A dyadic ball maximal function at a point in the closed ball of radius
`a` is controlled by the global unweighted `L¹` mass when the input vanishes
on the open ball of radius `a + b`.  The fixed radius `b` is the geometric
separation between the observation region and the support. -/
theorem dyadicBallMaximalRaw_le_global_lintegral_of_support_away
    {d : ℕ} [NeZero d] {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 < b)
    (f : Euclidean d → ℂ)
    (hf : ∀ y : Euclidean d, y ∈ Metric.ball (0 : Euclidean d) (a + b) → f y = 0)
    {x : Euclidean d} (hx : x ∈ Metric.closedBall (0 : Euclidean d) a) :
    dyadicBallMaximalRaw d f x ≤
      (volume (Metric.ball (0 : Euclidean d) b))⁻¹ *
        ∫⁻ y, ENNReal.ofReal ‖f y‖ ∂volume := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp
    (Nat.pos_of_ne_zero (NeZero.ne d))
  change (⨆ n : ℤ,
    (volume (Metric.ball x ((2 : ℝ) ^ n)))⁻¹ *
      ∫⁻ y in Metric.ball x ((2 : ℝ) ^ n), ENNReal.ofReal ‖f y‖ ∂volume) ≤ _
  refine iSup_le fun n => ?_
  let r : ℝ := (2 : ℝ) ^ n
  have hr : 0 < r := by
    dsimp only [r]
    positivity
  by_cases hrb : r ≤ b
  · have hsub : Metric.ball x r ⊆ Metric.ball (0 : Euclidean d) (a + b) := by
      apply Metric.ball_subset_ball'
      have hxa : dist x (0 : Euclidean d) ≤ a := by
        simpa only [Metric.mem_closedBall] using hx
      dsimp only [r] at hrb ⊢
      linarith
    have hzero :
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖f y‖ ∂volume) = 0 := by
      calc
        (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖f y‖ ∂volume) =
            ∫⁻ _y in Metric.ball x r, (0 : ENNReal) ∂volume := by
              apply setLIntegral_congr_fun measurableSet_ball
              intro y hy
              change ENNReal.ofReal ‖f y‖ = 0
              rw [hf y (hsub hy)]
              simp
        _ = 0 := by simp
    simp only [r] at hzero ⊢
    rw [hzero]
    simp
  · have hbr : b ≤ r := (lt_of_not_ge hrb).le
    have hvol : volume (Metric.ball (0 : Euclidean d) b) ≤
        volume (Metric.ball x r) := by
      calc
        volume (Metric.ball (0 : Euclidean d) b) = volume (Metric.ball x b) := by
          rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
        _ ≤ volume (Metric.ball x r) :=
          measure_mono (Metric.ball_subset_ball hbr)
    have hdenom : (volume (Metric.ball x r))⁻¹ ≤
        (volume (Metric.ball (0 : Euclidean d) b))⁻¹ :=
      ENNReal.inv_le_inv.mpr hvol
    have hlin : (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖f y‖ ∂volume) ≤
        ∫⁻ y, ENNReal.ofReal ‖f y‖ ∂volume :=
      by
        simpa using (lintegral_mono_set (μ := volume)
          (f := fun y : Euclidean d => ENNReal.ofReal ‖f y‖)
          (subset_univ (Metric.ball x r)))
    change (volume (Metric.ball x r))⁻¹ *
      (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖f y‖ ∂volume) ≤ _
    calc
      (volume (Metric.ball x r))⁻¹ *
          (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖f y‖ ∂volume) ≤
          (volume (Metric.ball (0 : Euclidean d) b))⁻¹ *
            (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖f y‖ ∂volume) :=
        by
          simpa only [mul_comm] using
            (mul_le_mul_right hdenom
              (∫⁻ y in Metric.ball x r, ENNReal.ofReal ‖f y‖ ∂volume))
      _ ≤ (volume (Metric.ball (0 : Euclidean d) b))⁻¹ *
          ∫⁻ y, ENNReal.ofReal ‖f y‖ ∂volume :=
        by
          simpa only [mul_comm] using
            (mul_le_mul_right hlin (volume (Metric.ball (0 : Euclidean d) b))⁻¹)

/-- The unweighted dyadic maximal estimate in `eLpNorm` form on Schwartz
inputs.  This is used both in the central weighted reduction and in the
all-radius restricted lowpass term. -/
theorem dyadicBallMaximal_eLpNorm_volume_le
    {d : ℕ} (hd : 0 < d) {p : ℝ} (hp : 1 < p)
    (f : SchwartzMap (Euclidean d) ℂ) :
    eLpNorm (dyadicBallMaximal d (f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (|dyadicHardyLittlewoodMaximalLpBound hd hp| + 1) *
        eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume := by
  let q : ENNReal := ENNReal.ofReal p
  let F : Euclidean d → ℂ := f
  let M : Euclidean d → ℝ := dyadicBallMaximal d F
  letI : Fact (1 ≤ q) := ⟨by
    dsimp only [q]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le⟩
  have hf : MemLp F q volume := by
    dsimp only [F, q]
    exact f.memLp _ volume
  have hM : MemLp M q volume := by
    dsimp only [M, F, q]
    exact (dyadic_hardy_littlewood_maximal_strong_type_schwartz hd hp).choose_spec.2 f |>.1
  have hclass :
      dyadicHardyLittlewoodMaximalLp hd hp (hf.toLp F) = hM.toLp M := by
    apply Lp.ext
    filter_upwards [dyadicHardyLittlewoodMaximalLp_agrees_schwartz_ae hd hp f,
      hM.coeFn_toLp] with x hx hMx
    exact hx.trans hMx.symm
  have hCnonneg : 0 ≤ |dyadicHardyLittlewoodMaximalLpBound hd hp| + 1 := by
    positivity
  have hCbound : dyadicHardyLittlewoodMaximalLpBound hd hp ≤
      |dyadicHardyLittlewoodMaximalLpBound hd hp| + 1 := by
    exact (le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)
  have hreal : (eLpNorm M q volume).toReal ≤
      (|dyadicHardyLittlewoodMaximalLpBound hd hp| + 1) *
        (eLpNorm F q volume).toReal := by
    calc
      (eLpNorm M q volume).toReal = ‖hM.toLp M‖ := (Lp.norm_toLp M hM).symm
      _ = ‖dyadicHardyLittlewoodMaximalLp hd hp (hf.toLp F)‖ := by rw [hclass]
      _ ≤ dyadicHardyLittlewoodMaximalLpBound hd hp * ‖hf.toLp F‖ :=
        dyadicHardyLittlewoodMaximalLp_norm_le hd hp (hf.toLp F)
      _ ≤ (|dyadicHardyLittlewoodMaximalLpBound hd hp| + 1) * ‖hf.toLp F‖ := by
        exact mul_le_mul_of_nonneg_right hCbound (norm_nonneg (hf.toLp F))
      _ = (|dyadicHardyLittlewoodMaximalLpBound hd hp| + 1) *
          (eLpNorm F q volume).toReal := by rw [Lp.norm_toLp F hf]
  have hMtop : eLpNorm M q volume < ∞ := hM.eLpNorm_lt_top
  have hftop : eLpNorm F q volume < ∞ := hf.eLpNorm_lt_top
  have hrighttop : ENNReal.ofReal
      (|dyadicHardyLittlewoodMaximalLpBound hd hp| + 1) * eLpNorm F q volume < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hftop
  change eLpNorm M q volume ≤ ENNReal.ofReal
      (|dyadicHardyLittlewoodMaximalLpBound hd hp| + 1) * eLpNorm F q volume
  apply (ENNReal.toReal_le_toReal hMtop.ne hrighttop.ne).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCnonneg]
  exact hreal

/-- A compactly supported input has its unweighted `Lᵖ` seminorm controlled
by the power-weighted one.  This is the direct `Lᵖ` counterpart of the `L¹`
estimate in `NearOrigin`. -/
private theorem outerPower_rpow_mul_eLpNorm_volume_le_weighted
    {d : ℕ} {p α S : ℝ} (hp : 1 < p) (hα : α ≤ 0) (hS : 0 < S)
    (f : SchwartzMap (Euclidean d) ℂ)
    (hfsupp : ∀ x : Euclidean d,
      x ∉ Metric.closedBall (0 : Euclidean d) S → f x = 0) :
    ((ENNReal.ofReal S) ^ α) ^ p⁻¹ *
        eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤
      eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α) := by
  let B : Set (Euclidean d) := Metric.closedBall 0 S
  let c : ENNReal := (ENNReal.ofReal S) ^ α
  have hB : MeasurableSet B := measurableSet_closedBall
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hcpos : 0 < c := by
    dsimp [c]
    exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hS) ENNReal.ofReal_ne_top
  have hmeasure : c • volume.restrict B ≤ powerWeightedVolume d α := by
    simpa only [c, B] using
      outerPower_smul_volume_restrict_closedBall_le_powerWeightedVolume hα hS
  have hlocal : c ^ p⁻¹ *
      eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) (volume.restrict B) ≤
      eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α) := by
    have h := eLpNorm_mono_measure (p := ENNReal.ofReal p)
      (f : Euclidean d → ℂ) hmeasure
    rw [eLpNorm_smul_measure_of_ne_zero hcpos.ne' (f : Euclidean d → ℂ)
      (ENNReal.ofReal p) (volume.restrict B)] at h
    simpa [ENNReal.smul_def, ENNReal.toReal_ofReal hp0.le, one_div] using h
  have hf_indicator : B.indicator (f : Euclidean d → ℂ) = (f : Euclidean d → ℂ) := by
    funext x
    by_cases hx : x ∈ B
    · simp [hx]
    · simp [hx, hfsupp x hx]
  have hrestrict :
      eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume =
        eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) (volume.restrict B) := by
    calc
      eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume =
          eLpNorm (B.indicator (f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume :=
        congrArg (fun g : Euclidean d → ℂ => eLpNorm g (ENNReal.ofReal p) volume)
          hf_indicator |>.symm
      _ = eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) (volume.restrict B) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hB
  calc
    c ^ p⁻¹ * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume =
        c ^ p⁻¹ * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
          (volume.restrict B) := by rw [hrestrict]
    _ ≤ eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
        (powerWeightedVolume d α) := hlocal

/-- Solving the compact-support weighted `L¹` estimate for the unweighted
norm.  The coefficient is explicit and finite for every fixed positive
support radius. -/
private theorem eLpNorm_one_volume_le_weighted_of_ball_support
    {d : ℕ} {p α S : ℝ} (hp : 1 < p) (hα : α ≤ 0) (hS : 0 < S)
    (f : SchwartzMap (Euclidean d) ℂ)
    (hfsupp : ∀ x : Euclidean d,
      x ∉ Metric.closedBall (0 : Euclidean d) S → f x = 0) :
    eLpNorm (f : Euclidean d → ℂ) 1 volume ≤
      (((ENNReal.ofReal S) ^ α) ^ p⁻¹)⁻¹ *
        (volume (Metric.closedBall (0 : Euclidean d) S)) ^ (1 - p⁻¹) *
          eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
            (powerWeightedVolume d α) := by
  let c : ENNReal := (ENNReal.ofReal S) ^ α
  have hcpos : 0 < c := by
    dsimp [c]
    exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hS) ENNReal.ofReal_ne_top
  have hctop : c ≠ ∞ := by
    dsimp [c]
    exact ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr hS).ne'
      ENNReal.ofReal_ne_top
  have hcpowpos : 0 < c ^ p⁻¹ := ENNReal.rpow_pos hcpos hctop
  have hcpowtop : c ^ p⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hcpos.ne' hctop
  have hbase := outerPower_rpow_mul_eLpNorm_one_volume_le_weighted
    hp hα hS f hfsupp
  calc
    eLpNorm (f : Euclidean d → ℂ) 1 volume =
        (c ^ p⁻¹)⁻¹ * (c ^ p⁻¹ * eLpNorm (f : Euclidean d → ℂ) 1 volume) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hcpowpos.ne' hcpowtop]
      simp
    _ ≤ (c ^ p⁻¹)⁻¹ *
        (eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
          (powerWeightedVolume d α) *
          (volume (Metric.closedBall (0 : Euclidean d) S)) ^ (1 - p⁻¹)) := by
      exact mul_le_mul_right hbase _
    _ = (((ENNReal.ofReal S) ^ α) ^ p⁻¹)⁻¹ *
        (volume (Metric.closedBall (0 : Euclidean d) S)) ^ (1 - p⁻¹) *
          eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
            (powerWeightedVolume d α) := by
      dsimp [c]
      ring

/-- On data supported in the literal central annulus `1 ≤ ‖x‖ ≤ 2`, the
dyadic Hardy--Littlewood maximal function is bounded on every nonpositive
locally integrable power weight.  The near-origin part uses the fixed-radius
`L¹` estimate above; its complement is reduced to the unweighted maximal
theorem by the exterior weight comparison. -/
theorem exists_dyadicBallMaximal_central_annulus_power_weighted_bound
    {d : ℕ} (hd : 1 ≤ d) {p α : ℝ} (hp : 1 < p)
    (hαlower : 1 - (d : ℝ) < α) (hα : α ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d, ‖x‖ < 1 → f x = 0) →
      (∀ x : Euclidean d, 2 < ‖x‖ → f x = 0) →
      MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) (powerWeightedVolume d α) →
        MemLp (dyadicBallMaximal d (f : Euclidean d → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume d α) ∧
        eLpNorm (dyadicBallMaximal d (f : Euclidean d → ℂ)) (ENNReal.ofReal p)
          (powerWeightedVolume d α) ≤
          ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
            (powerWeightedVolume d α) := by
  have hd0 : 0 < d := by omega
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hαint : -(d : ℝ) < α := by linarith
  have hpInvLe : p⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hp0).mpr hp.le
  have hpInvNN : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hOneSubInvNN : 0 ≤ 1 - p⁻¹ := sub_nonneg.mpr hpInvLe
  let μ : Measure (Euclidean d) := powerWeightedVolume d α
  let B : Set (Euclidean d) := Metric.closedBall 0 (1 / 2 : ℝ)
  let U : Set (Euclidean d) := Bᶜ
  let A : ENNReal := (volume (Metric.ball (0 : Euclidean d) (1 / 2 : ℝ)))⁻¹
  let cIn : ENNReal := ((ENNReal.ofReal (2 : ℝ)) ^ α) ^ p⁻¹
  let wOut : ENNReal := (ENNReal.ofReal (1 / 2 : ℝ)) ^ α
  let cOut : ENNReal := ((ENNReal.ofReal (1 / 2 : ℝ)) ^ α) ^ p⁻¹
  let V₁ : ENNReal := μ B
  let V₂ : ENNReal := volume (Metric.closedBall (0 : Euclidean d) (2 : ℝ))
  let D₁ : ENNReal := cIn⁻¹ * V₂ ^ (1 - p⁻¹)
  let H : ENNReal := ENNReal.ofReal
    (|dyadicHardyLittlewoodMaximalLpBound hd0 hp| + 1)
  let Knear : ENNReal := A * D₁ * V₁ ^ p⁻¹
  let Kouter : ENNReal := cOut * H * cIn⁻¹
  let K : ENNReal := Knear + Kouter
  letI : IsFiniteMeasureOnCompacts μ := by
    dsimp only [μ]
    exact powerWeightedVolume_isFiniteMeasureOnCompacts hd hαint
  have hBmeas : MeasurableSet B := by
    dsimp only [B]
    exact measurableSet_closedBall
  have hUmeas : MeasurableSet U := hBmeas.compl
  have hV₁top : V₁ < ∞ := by
    dsimp only [V₁, B]
    exact measure_closedBall_lt_top
  have hV₂top : V₂ < ∞ := by
    dsimp only [V₂]
    exact measure_closedBall_lt_top
  have hballpos : 0 < volume (Metric.ball (0 : Euclidean d) (1 / 2 : ℝ)) := by
    exact Metric.measure_ball_pos volume 0 (by norm_num)
  have hAtop : A < ∞ := by
    dsimp only [A]
    exact ENNReal.inv_lt_top.mpr hballpos
  have hcInBasePos : 0 < (ENNReal.ofReal (2 : ℝ)) ^ α :=
    ENNReal.rpow_pos (by norm_num) ENNReal.ofReal_ne_top
  have hcInBaseTop : (ENNReal.ofReal (2 : ℝ)) ^ α ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) ENNReal.ofReal_ne_top
  have hcInPos : 0 < cIn := by
    dsimp only [cIn]
    exact ENNReal.rpow_pos hcInBasePos hcInBaseTop
  have hcInTop : cIn ≠ ∞ := by
    dsimp only [cIn]
    exact ENNReal.rpow_ne_top_of_ne_zero hcInBasePos.ne' hcInBaseTop
  have hcOutBasePos : 0 < (ENNReal.ofReal (1 / 2 : ℝ)) ^ α :=
    ENNReal.rpow_pos (by norm_num) ENNReal.ofReal_ne_top
  have hcOutBaseTop : (ENNReal.ofReal (1 / 2 : ℝ)) ^ α ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) ENNReal.ofReal_ne_top
  have hcOutTop : cOut ≠ ∞ := by
    dsimp only [cOut]
    exact ENNReal.rpow_ne_top_of_ne_zero hcOutBasePos.ne' hcOutBaseTop
  have hV₁powtop : V₁ ^ p⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hpInvNN hV₁top.ne
  have hV₂powtop : V₂ ^ (1 - p⁻¹) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hOneSubInvNN hV₂top.ne
  have hcInInvTop : cIn⁻¹ < ∞ :=
    ENNReal.inv_lt_top.mpr hcInPos
  have hD₁top : D₁ < ∞ := by
    dsimp only [D₁]
    exact ENNReal.mul_lt_top hcInInvTop (lt_top_iff_ne_top.mpr hV₂powtop)
  have hHtop : H < ∞ := by
    dsimp only [H]
    exact ENNReal.ofReal_lt_top
  have hKnearTop : Knear < ∞ := by
    dsimp only [Knear]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hAtop hD₁top)
      (lt_top_iff_ne_top.mpr hV₁powtop)
  have hKouterTop : Kouter < ∞ := by
    dsimp only [Kouter]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hcOutTop) hHtop)
      hcInInvTop
  have hKtop : K < ∞ := by
    dsimp only [K]
    exact ENNReal.add_lt_top.mpr ⟨hKnearTop, hKouterTop⟩
  let C : ℝ := K.toReal + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro f hfinner hfouter hfp
  letI : NeZero d := ⟨by omega⟩
  let M : Euclidean d → ℝ := dyadicBallMaximal d (f : Euclidean d → ℂ)
  let Mr : Euclidean d → ENNReal := dyadicBallMaximalRaw d (f : Euclidean d → ℂ)
  let L₁ : ENNReal := eLpNorm (f : Euclidean d → ℂ) 1 volume
  let W : ENNReal := eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) μ
  have hfsupp : ∀ x : Euclidean d, x ∉ Metric.closedBall (0 : Euclidean d) 2 → f x = 0 := by
    intro x hx
    apply hfouter x
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact lt_of_not_ge hx
  have hL₁ : L₁ ≤ D₁ * W := by
    dsimp only [L₁, D₁, V₂, cIn, W, μ]
    simpa only [mul_assoc] using
      eLpNorm_one_volume_le_weighted_of_ball_support hp hα (by norm_num) f hfsupp
  have hinput : cIn * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤ W := by
    dsimp only [cIn, W, μ]
    simpa only using
      outerPower_rpow_mul_eLpNorm_volume_le_weighted hp hα (by norm_num) f hfsupp
  have hinput' : eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume ≤ cIn⁻¹ * W := by
    calc
      eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume =
          cIn⁻¹ * (cIn * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcInPos.ne' hcInTop]
        simp
      _ ≤ cIn⁻¹ * W := mul_le_mul_right hinput _
  have hrawnear (x : Euclidean d) (hx : x ∈ B) : Mr x ≤ A * L₁ := by
    have hzero : ∀ y : Euclidean d, y ∈ Metric.ball (0 : Euclidean d) 1 → f y = 0 := by
      intro y hy
      apply hfinner y
      simpa only [Metric.mem_ball, dist_zero_right] using hy
    simpa only [Mr, A, L₁, eLpNorm_one_eq_lintegral_enorm, ofReal_norm] using
      dyadicBallMaximalRaw_le_global_lintegral_of_support_away
        (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
        (f : Euclidean d → ℂ) (by simpa only [add_halves] using hzero) hx
  have hnear : eLpNorm (B.indicator M) (ENNReal.ofReal p) μ ≤
      A * L₁ * V₁ ^ p⁻¹ := by
    calc
      eLpNorm (B.indicator M) (ENNReal.ofReal p) μ ≤
          eLpNorm (B.indicator Mr) (ENNReal.ofReal p) μ := by
        apply eLpNorm_mono_enorm
        intro x
        by_cases hx : x ∈ B
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          change ‖(dyadicBallMaximalRaw d (f : Euclidean d → ℂ) x).toReal‖ₑ ≤
            ‖dyadicBallMaximalRaw d (f : Euclidean d → ℂ) x‖ₑ
          rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, enorm_eq_self]
          exact ENNReal.ofReal_toReal_le
        · simp [hx]
      _ ≤ eLpNorm (B.indicator (fun _ : Euclidean d => A * L₁))
          (ENNReal.ofReal p) μ := by
        apply eLpNorm_mono_enorm
        intro x
        by_cases hx : x ∈ B
        · simp only [Set.indicator_of_mem hx, enorm_eq_self]
          exact hrawnear x hx
        · simp [hx]
      _ = A * L₁ * V₁ ^ p⁻¹ := by
        rw [eLpNorm_indicator_const hBmeas
          (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
        dsimp only [V₁]
        simp only [ENNReal.toReal_ofReal hp0.le, enorm_eq_self, one_div]
  have hnearW : eLpNorm (B.indicator M) (ENNReal.ofReal p) μ ≤ Knear * W := by
    calc
      eLpNorm (B.indicator M) (ENNReal.ofReal p) μ ≤ A * L₁ * V₁ ^ p⁻¹ := hnear
      _ ≤ (A * (D₁ * W)) * V₁ ^ p⁻¹ := by
        exact mul_le_mul_left (mul_le_mul_right hL₁ A) _
      _ = Knear * W := by
        dsimp only [Knear]
        ring
  have hMvol : MemLp M (ENNReal.ofReal p) volume := by
    dsimp only [M]
    exact (dyadic_hardy_littlewood_maximal_strong_type_schwartz hd0 hp).choose_spec.2 f |>.1
  have hmeasureOut : μ.restrict U ≤ wOut • volume.restrict U := by
    dsimp only [μ, U, B, wOut]
    simpa only using
      powerWeightedVolume_restrict_compl_closedBall_le_outerPower_smul
        (d := d) hα (show 0 < (1 / 2 : ℝ) by norm_num)
  have houter : eLpNorm (U.indicator M) (ENNReal.ofReal p) μ ≤
      cOut * eLpNorm M (ENNReal.ofReal p) volume := by
    calc
      eLpNorm (U.indicator M) (ENNReal.ofReal p) μ =
          eLpNorm M (ENNReal.ofReal p) (μ.restrict U) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hUmeas
      _ ≤ eLpNorm M (ENNReal.ofReal p) (wOut • volume.restrict U) :=
        eLpNorm_mono_measure M hmeasureOut
      _ = cOut * eLpNorm M (ENNReal.ofReal p) (volume.restrict U) := by
        rw [eLpNorm_smul_measure_of_ne_zero]
        · dsimp only [wOut, cOut]
          simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0.le, one_div, smul_eq_mul]
        · exact hcOutBasePos.ne'
      _ ≤ cOut * eLpNorm M (ENNReal.ofReal p) volume := by
        exact mul_le_mul_right (eLpNorm_restrict_le M (ENNReal.ofReal p) volume U) _
  have hMvolume : eLpNorm M (ENNReal.ofReal p) volume ≤ H *
      eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume := by
    dsimp only [M, H]
    exact dyadicBallMaximal_eLpNorm_volume_le hd0 hp f
  have houterW : eLpNorm (U.indicator M) (ENNReal.ofReal p) μ ≤ Kouter * W := by
    calc
      eLpNorm (U.indicator M) (ENNReal.ofReal p) μ ≤
          cOut * eLpNorm M (ENNReal.ofReal p) volume := houter
      _ ≤ cOut * (H * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume) := by
        exact mul_le_mul_right hMvolume _
      _ ≤ cOut * (H * (cIn⁻¹ * W)) := by
        exact mul_le_mul_right (mul_le_mul_right hinput' H) cOut
      _ = Kouter * W := by
        dsimp only [Kouter]
        ring
  have hμac : μ ≪ volume := by
    dsimp only [μ, powerWeightedVolume]
    exact withDensity_absolutelyContinuous volume (radialPowerWeight d α)
  have hMmeas : AEStronglyMeasurable M μ :=
    hMvol.aestronglyMeasurable.mono_ac hμac
  letI : IsFiniteMeasure (μ.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hV₁top⟩
  have hrawtop (x : Euclidean d) (hx : x ∈ B) : Mr x < ∞ := by
    have hL₁top : L₁ < ∞ := by
      dsimp only [L₁]
      exact (f.memLp 1 volume).eLpNorm_lt_top
    exact (hrawnear x hx).trans_lt (ENNReal.mul_lt_top hAtop hL₁top)
  have hbound (x : Euclidean d) (hx : x ∈ B) :
      ‖M x‖ ≤ (A * L₁).toReal := by
    have hrighttop : A * L₁ < ∞ := by
      dsimp only [L₁]
      exact ENNReal.mul_lt_top hAtop (f.memLp 1 volume).eLpNorm_lt_top
    calc
      ‖M x‖ = (Mr x).toReal := by
        dsimp only [M, Mr, dyadicBallMaximal]
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ (A * L₁).toReal :=
        (ENNReal.toReal_le_toReal (hrawtop x hx).ne hrighttop.ne).mpr (hrawnear x hx)
  have hboundae : ∀ᵐ x ∂μ.restrict B, ‖M x‖ ≤ (A * L₁).toReal :=
    (ae_restrict_iff' hBmeas).mpr (Filter.Eventually.of_forall fun x hx => hbound x hx)
  have hBmemRest : MemLp M (ENNReal.ofReal p) (μ.restrict B) :=
    MemLp.of_bound hMmeas.restrict (A * L₁).toReal hboundae
  have hBmem : MemLp (B.indicator M) (ENNReal.ofReal p) μ :=
    (memLp_indicator_iff_restrict hBmeas).mpr hBmemRest
  have hUmemRest : MemLp M (ENNReal.ofReal p) (μ.restrict U) := by
    have hscaled : MemLp M (ENNReal.ofReal p) (wOut • volume.restrict U) := by
      exact (hMvol.restrict U).smul_measure hcOutBaseTop
    exact hscaled.mono_measure hmeasureOut
  have hUmem : MemLp (U.indicator M) (ENNReal.ofReal p) μ :=
    (memLp_indicator_iff_restrict hUmeas).mpr hUmemRest
  have hsplit : M = B.indicator M + U.indicator M := by
    funext x
    by_cases hx : x ∈ B
    · simp [hx, U]
    · have hxU : x ∈ U := by simpa only [U, mem_compl_iff] using hx
      simp [hx, hxU]
  have hMmem : MemLp M (ENNReal.ofReal p) μ := by
    rw [hsplit]
    exact hBmem.add hUmem
  have hnormK : eLpNorm M (ENNReal.ofReal p) μ ≤ K * W := by
    calc
      eLpNorm M (ENNReal.ofReal p) μ =
          eLpNorm (B.indicator M + U.indicator M) (ENNReal.ofReal p) μ := by
        rw [← hsplit]
      _ ≤ eLpNorm (B.indicator M) (ENNReal.ofReal p) μ +
          eLpNorm (U.indicator M) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le hBmem.aestronglyMeasurable hUmem.aestronglyMeasurable
          (by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal hp.le)
      _ ≤ Knear * W + Kouter * W := add_le_add hnearW houterW
      _ = K * W := by
        dsimp only [K]
        ring
  have hKleC : K ≤ ENNReal.ofReal C := by
    calc
      K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hKtop.ne).symm
      _ ≤ ENNReal.ofReal C := by
        apply ENNReal.ofReal_le_ofReal
        dsimp only [C]
        linarith [ENNReal.toReal_nonneg (a := K)]
  refine ⟨?_, ?_⟩
  · simpa only [M, μ] using hMmem
  · change eLpNorm M (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C * W
    exact hnormK.trans (by
      simpa only [mul_comm] using mul_le_mul_right hKleC W)

/-- The compact relative-frequency lowpass maximal function obeys the same
central-annulus weighted estimate.  This is a thin transfer from the dyadic
ball theorem through the public kernel majorant. -/
theorem exists_relativeLowpassMaximal_central_annulus_power_weighted_bound
    {d : ℕ} (hd : 1 ≤ d) {p α : ℝ} (hp : 1 < p)
    (hαlower : 1 - (d : ℝ) < α) (hα : α ≤ 0)
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφzero : ∀ ξ : Euclidean d, 2 ≤ ‖ξ‖ → φ ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euclidean d) ℂ,
      (∀ x : Euclidean d, ‖x‖ < 1 → f x = 0) →
      (∀ x : Euclidean d, 2 < ‖x‖ → f x = 0) →
      MemLp (f : Euclidean d → ℂ) (ENNReal.ofReal p) (powerWeightedVolume d α) →
        MemLp (relativeLowpassMaximal d φ f) (ENNReal.ofReal p)
          (powerWeightedVolume d α) ∧
        eLpNorm (relativeLowpassMaximal d φ f) (ENNReal.ofReal p)
          (powerWeightedVolume d α) ≤
          ENNReal.ofReal C * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
            (powerWeightedVolume d α) := by
  obtain ⟨D, hD, hdyadic⟩ :=
    exists_dyadicBallMaximal_central_annulus_power_weighted_bound hd hp hαlower hα
  obtain ⟨K, hK, hmajor⟩ := exists_relative_lowpass_kernel_majorant φ hφzero
  refine ⟨K * D + 1, by positivity, ?_⟩
  intro f hfinner hfouter hfp
  obtain ⟨hMmem, hMnorm⟩ := hdyadic f hfinner hfouter hfp
  have hμac : powerWeightedVolume d α ≪ volume := by
    simpa only [powerWeightedVolume] using
      withDensity_absolutelyContinuous volume (radialPowerWeight d α)
  have hRmeas : AEStronglyMeasurable (relativeLowpassMaximal d φ f)
      (powerWeightedVolume d α) :=
    (relativeLowpassMaximal_aestronglyMeasurable φ hφzero f).mono_ac hμac
  have hRnonneg (x : Euclidean d) : 0 ≤ relativeLowpassMaximal d φ f x := by
    unfold relativeLowpassMaximal
    exact ENNReal.toReal_nonneg
  have hMnonneg (x : Euclidean d) :
      0 ≤ dyadicBallMaximal d (f : Euclidean d → ℂ) x := by
    unfold dyadicBallMaximal
    exact ENNReal.toReal_nonneg
  have hpoint (x : Euclidean d) :
      ‖relativeLowpassMaximal d φ f x‖ ≤
        K * ‖dyadicBallMaximal d (f : Euclidean d → ℂ) x‖ := by
    calc
      ‖relativeLowpassMaximal d φ f x‖ = relativeLowpassMaximal d φ f x := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hRnonneg x)]
      _ ≤ K * dyadicBallMaximal d (f : Euclidean d → ℂ) x := hmajor f x
      _ = K * ‖dyadicBallMaximal d (f : Euclidean d → ℂ) x‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hMnonneg x)]
  have hpointProd (x : Euclidean d) :
      ‖relativeLowpassMaximal d φ f x‖ ≤
        ‖K * dyadicBallMaximal d (f : Euclidean d → ℂ) x‖ := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (hRnonneg x),
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hK.le (hMnonneg x))]
    exact hmajor f x
  have hRmem : MemLp (relativeLowpassMaximal d φ f) (ENNReal.ofReal p)
      (powerWeightedVolume d α) :=
    (hMmem.const_mul K).mono hRmeas (Filter.Eventually.of_forall hpointProd)
  refine ⟨hRmem, ?_⟩
  calc
    eLpNorm (relativeLowpassMaximal d φ f) (ENNReal.ofReal p)
        (powerWeightedVolume d α) ≤
        ENNReal.ofReal K * eLpNorm (dyadicBallMaximal d (f : Euclidean d → ℂ))
          (ENNReal.ofReal p) (powerWeightedVolume d α) :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (Filter.Eventually.of_forall hpoint) (ENNReal.ofReal p)
    _ ≤ ENNReal.ofReal K *
        (ENNReal.ofReal D * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
          (powerWeightedVolume d α)) := mul_le_mul_right hMnorm _
    _ = ENNReal.ofReal (K * D) * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
          (powerWeightedVolume d α) := by
      rw [ENNReal.ofReal_mul hK.le]
      ring
    _ ≤ ENNReal.ofReal (K * D + 1) *
        eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
          (powerWeightedVolume d α) := by
      simpa only [mul_comm] using
        mul_le_mul_right
          (ENNReal.ofReal_le_ofReal (by linarith : K * D ≤ K * D + 1))
          (eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p)
            (powerWeightedVolume d α))

end

end LeanSpherical.HarmonicAnalysis
