/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.RelativeDyadicMovingL2Core

/-!
# Global relative dyadic moving multiplier estimates

This module assembles finite relative dyadic radius-block estimates into the
corresponding global maximal estimate. The frequency-local and compact-data
arguments live in the core module.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory FourierTransform Metric Set
open scoped BigOperators BoundedContinuousFunction FourierTransform
/-- Uniform `L²` control of every finite collection of nonnegative dyadic
radius blocks passes to the increasing exhaustion by `[-n,n]`. -/
theorem lintegral_iSup_finset_Icc_sq_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : ℤ → α → ℝ)
    (hu_meas : ∀ k, Measurable (u k))
    (hu_nonneg : ∀ k x, 0 ≤ u k x)
    {B : ℝ}
    (hbound : ∀ (K : Finset ℤ) (hK : K.Nonempty),
      MemLp (fun x => K.sup' hK (fun k => u k x)) 2 μ ∧
      (∫ x, ‖K.sup' hK (fun k => u k x)‖ ^ 2 ∂μ) ≤ B) :
    (∫⁻ x, ⨆ n : ℕ,
      ENNReal.ofReal
        (((Finset.Icc (-((n : ℤ))) (n : ℤ)).sup'
          (by refine ⟨0, ?_⟩; simp) (fun k => u k x)) ^ 2) ∂μ) ≤
      ENNReal.ofReal B := by
  let K : ℕ → Finset ℤ := fun n => Finset.Icc (-((n : ℤ))) (n : ℤ)
  have hKnonempty (n : ℕ) : (K n).Nonempty := by
    refine ⟨0, ?_⟩
    simp [K]
  let v : ℕ → α → ℝ := fun n x =>
    (K n).sup' (hKnonempty n) (fun k => u k x)
  have hv_meas (n : ℕ) : Measurable (v n) := by
    have hsup_apply : ((K n).sup' (hKnonempty n) u : α → ℝ) = v n := by
      funext x
      exact Finset.sup'_apply (hKnonempty n) u x
    rw [← hsup_apply]
    exact Finset.measurable_sup' (hKnonempty n) (fun k _ => hu_meas k)
  have hv_nonneg (n : ℕ) (x : α) : 0 ≤ v n x := by
    obtain ⟨k, hk, hmax⟩ :=
      (K n).exists_mem_eq_sup' (hKnonempty n) (fun k => u k x)
    change 0 ≤ (K n).sup' (hKnonempty n) (fun k => u k x)
    rw [hmax]
    exact hu_nonneg k x
  have hK_mono (n m : ℕ) (hnm : n ≤ m) : K n ⊆ K m := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    constructor <;> omega
  have hv_mono : Monotone v := by
    intro n m hnm
    intro x
    change (K n).sup' (hKnonempty n) (fun k => u k x) ≤
      (K m).sup' (hKnonempty m) (fun k => u k x)
    exact Finset.sup'_mono _ (hK_mono n m hnm) (hKnonempty n)
  have hF_meas (n : ℕ) : Measurable (fun x => ENNReal.ofReal ((v n x) ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp ((hv_meas n).pow_const 2)
  have hF_mono : Monotone (fun n : ℕ => fun x => ENNReal.ofReal ((v n x) ^ 2)) := by
    intro n m hnm
    intro x
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (hv_nonneg n x) (hv_mono hnm x) 2
  have hF_bound (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal ((v n x) ^ 2) ∂μ) ≤ ENNReal.ofReal B := by
    have hv_mem := (hbound (K n) (hKnonempty n)).1
    have hv_int : Integrable (fun x => (v n x) ^ 2) μ := by
      have h := (memLp_two_iff_integrable_sq_norm hv_mem.1).1 hv_mem
      convert h using 1
      funext x
      change (v n x) ^ 2 =
        ‖(K n).sup' (hKnonempty n) (fun k => u k x)‖ ^ 2
      rw [show v n x = (K n).sup' (hKnonempty n) (fun k => u k x) by rfl,
        Real.norm_of_nonneg (hv_nonneg n x)]
    calc
      (∫⁻ x, ENNReal.ofReal ((v n x) ^ 2) ∂μ) =
          ENNReal.ofReal (∫ x, (v n x) ^ 2 ∂μ) := by
            symm
            exact ofReal_integral_eq_lintegral_ofReal hv_int
              (Filter.Eventually.of_forall fun x => sq_nonneg (v n x))
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (by
        calc
          (∫ x, (v n x) ^ 2 ∂μ) =
              ∫ x, ‖(K n).sup' (hKnonempty n) (fun k => u k x)‖ ^ 2 ∂μ := by
                apply integral_congr_ae
                filter_upwards with x
                rw [show v n x = (K n).sup' (hKnonempty n) (fun k => u k x) by rfl,
                  Real.norm_of_nonneg (hv_nonneg n x)]
          _ ≤ B := (hbound (K n) (hKnonempty n)).2)
  change (∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal ((v n x) ^ 2) ∂μ) ≤ ENNReal.ofReal B
  rw [MeasureTheory.lintegral_iSup hF_meas hF_mono]
  exact iSup_le hF_bound

/-- On a compact radius interval, the ordinary norm is bounded by the
corresponding ENNReal radius supremum. -/
theorem norm_fourierInv_relative_dyadic_bandpass_le_iSup_radius_block
    {d : Nat} (phi theta f : SchwartzMap (Euclidean (d + 1)) ℂ)
    (htheta : HasCompactSupport (theta : Euclidean (d + 1) → ℂ)) (j : Nat)
    {a b : ℝ} (hab : a ≤ b) (r : Icc a b) (x : Euclidean (d + 1)) :
    ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
      surfaceFourier (d + 1) (-r.1 • xi) *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
          phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) * theta xi *
        𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ≤
      (⨆ s : Icc a b, ENNReal.ofReal
        ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
          surfaceFourier (d + 1) (-s.1 • xi) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (s.1 • xi)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (s.1 • xi))) * theta xi *
            𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖).toReal := by
  let F : ℝ → Euclidean (d + 1) → ℂ := fun s x =>
    𝓕⁻ (fun xi : Euclidean (d + 1) =>
      surfaceFourier (d + 1) (-s • xi) *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (s • xi)) -
          phi (((2 : ℝ) ^ j)⁻¹ • (s • xi))) * theta xi *
        𝓕 (f : Euclidean (d + 1) → ℂ) xi) x
  have hjoint := continuous_and_hasDerivAt_fourierInv_relative_dyadic_bandpass
    phi theta f htheta j
  have hFcont : Continuous (Function.uncurry F) := by
    simpa only [F] using hjoint.1
  have hnorm : Continuous (fun s : ℝ => ‖F s x‖) :=
    (hFcont.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x))).norm
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hab) hnorm.continuousOn
  have hsup :
      (⨆ s : Icc a b, ENNReal.ofReal ‖F s.1 x‖) =
        ENNReal.ofReal ‖F s0 x‖ := by
    apply le_antisymm
    · apply iSup_le
      intro s
      exact ENNReal.ofReal_le_ofReal (hmax s.2)
    · exact le_iSup (fun s : Icc a b => ENNReal.ofReal ‖F s.1 x‖) ⟨s0, hs0⟩
  change ‖F r.1 x‖ ≤ _
  rw [hsup, ENNReal.toReal_ofReal (norm_nonneg _)]
  exact hmax r.2

/-- The literal moving relative-dyadic multiplier is pointwise dominated by
the increasing exhaustion of its finite dyadic radius blocks. -/
theorem raw_relative_dyadic_bandpass_square_le_iSup_finset_Icc_radius_blocks
    {d : Nat} (phi f : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (j : Nat) :
    let Q : Euclidean (d + 1) → ENNReal := fun x =>
      ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal
        (‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
          surfaceFourier (d + 1) (-r.1 • xi) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
            𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ^ 2)
    let u : ℤ → Euclidean (d + 1) → ℝ := fun k x =>
      (⨆ r : Icc ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k), ENNReal.ofReal
        ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
          surfaceFourier (d + 1) (-r.1 • xi) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
            (phi (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • xi) -
              phi (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • xi)) *
            𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖).toReal
    let K : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) N
    let T : ℕ → Euclidean (d + 1) → ℝ := fun N x =>
      (K N).sup' (by
        dsimp only [K]
        refine ⟨0, ?_⟩
        simp only [Finset.mem_Icc]
        omega) (fun k => u k x)
    ∀ x, Q x ≤ ⨆ N : ℕ, ENNReal.ofReal ((T N x) ^ 2) := by
  classical
  choose theta htheta htheta_compact using fun k : ℤ =>
    exists_compactlySupported_schwartzMap_scaled_sub phi hphi_zero
      ((2 : ℝ) ^ ((j : ℤ) + 3 - k))
      ((2 : ℝ) ^ ((j : ℤ) - 2 - k))
      (zpow_pos (by norm_num) _)
      (zpow_pos (by norm_num) _)
      ((zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).monotone (by omega))
  let v : ℤ → Euclidean (d + 1) → ℝ := fun k x =>
    (⨆ r : Icc ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k), ENNReal.ofReal
      ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
        surfaceFourier (d + 1) (-r.1 • xi) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) * theta k xi *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖).toReal
  have huv (k : ℤ) : v k = fun x =>
      (⨆ r : Icc ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k), ENNReal.ofReal
        ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
          surfaceFourier (d + 1) (-r.1 • xi) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
            (phi (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • xi) -
              phi (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • xi)) *
            𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖).toReal := by
    funext x
    dsimp only [v]
    simp_rw [htheta k]
  intro Q u K T x
  apply iSup_le
  intro r
  obtain ⟨k, hk⟩ := exists_mem_Ico_zpow r.2 (by norm_num : (1 : ℝ) < 2)
  let N : ℕ := k.natAbs
  have hkN : k ∈ Finset.Icc (-(N : ℤ)) N := by
    simp only [Finset.mem_Icc]
    dsimp only [N]
    omega
  have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hrblock : r.1 ∈ Icc ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k) := by
    constructor
    · exact hk.1
    · rw [← hpow]
      exact hk.2.le
  have hraw_eq :
      (fun xi : Euclidean (d + 1) =>
        surfaceFourier (d + 1) (-r.1 • xi) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi) =
      fun xi =>
        surfaceFourier (d + 1) (-r.1 • xi) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) * theta k xi *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi := by
    funext xi
    rw [htheta k xi]
    exact relative_dyadic_bandpass_mul_fat_cutoff
      (phi := phi) (j := j) (k := k) (r := r.1) hphi_one hphi_zero
      (by rw [hpow]; exact hrblock) xi
      (surfaceFourier (d + 1) (-r.1 • xi))
      (𝓕 (f : Euclidean (d + 1) → ℂ))
  have hblock_le :
      ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
        surfaceFourier (d + 1) (-r.1 • xi) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) * theta k xi *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ≤ v k x := by
    have h := norm_fourierInv_relative_dyadic_bandpass_le_iSup_radius_block
      phi (theta k) f (htheta_compact k) j
      (a := (2 : ℝ) ^ k) (b := 2 * (2 : ℝ) ^ k)
      (by linarith [zpow_pos (by norm_num : (0 : ℝ) < 2) k])
      ⟨r.1, hrblock⟩ x
    exact h
  have hle :
      ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
        surfaceFourier (d + 1) (-r.1 • xi) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ≤
        (Finset.Icc (-(N : ℤ)) N).sup' (by simp) (fun i => v i x) := by
    rw [hraw_eq]
    exact hblock_le.trans (Finset.le_sup' (fun i => v i x) hkN)
  have hle' :
      ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
        surfaceFourier (d + 1) (-r.1 • xi) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ≤
        (Finset.Icc (-(N : ℤ)) N).sup' (by simp)
          (fun i =>
            (⨆ s : Icc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i), ENNReal.ofReal
              ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
                surfaceFourier (d + 1) (-s.1 • xi) *
                  (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (s.1 • xi)) -
                    phi (((2 : ℝ) ^ j)⁻¹ • (s.1 • xi))) *
                  (phi (((2 : ℝ) ^ ((j : ℤ) + 3 - i))⁻¹ • xi) -
                    phi (((2 : ℝ) ^ ((j : ℤ) - 2 - i))⁻¹ • xi)) *
                  𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖).toReal) := by
    simpa only [huv] using hle
  have hTnonneg : 0 ≤ T N x := (norm_nonneg _).trans hle'
  exact le_iSup_of_le N (ENNReal.ofReal_le_ofReal
    ((sq_le_sq₀ (norm_nonneg _) hTnonneg).mpr hle'))

/- The lower-integral estimate below is deliberately stated directly for the
literal raw supremum.  The only point lost by `toReal` is excluded almost
everywhere by finiteness of the squared lower integral. -/
theorem memLp_two_toReal_iSup_ennreal_norm_of_sq_lintegral
    {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (F : ι → α → E)
    (hQmeas : Measurable (fun x =>
      ⨆ i : ι, ENNReal.ofReal (‖F i x‖ ^ 2)))
    (hTmeas : AEMeasurable (fun x =>
      (⨆ i : ι, ENNReal.ofReal ‖F i x‖).toReal) μ)
    {B : ℝ} (hB : 0 ≤ B)
    (hQlin : (∫⁻ x, ⨆ i : ι, ENNReal.ofReal (‖F i x‖ ^ 2) ∂μ) ≤
      ENNReal.ofReal B) :
    MemLp (fun x => (⨆ i : ι, ENNReal.ofReal ‖F i x‖).toReal) 2 μ ∧
      (∫ x, ‖(⨆ i : ι, ENNReal.ofReal ‖F i x‖).toReal‖ ^ 2 ∂μ) ≤ B := by
  let Q : α → ENNReal := fun x => ⨆ i : ι, ENNReal.ofReal (‖F i x‖ ^ 2)
  let T : α → ℝ := fun x => (⨆ i : ι, ENNReal.ofReal ‖F i x‖).toReal
  let G : α → ℝ := fun x => (Q x).toReal.sqrt
  have hQmeas' : Measurable Q := by
    simpa only [Q] using hQmeas
  have hQlin' : (∫⁻ x, Q x ∂μ) ≤ ENNReal.ofReal B := by
    simpa only [Q] using hQlin
  have hQint_ne_top : (∫⁻ x, Q x ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQlin'
  have hQae : ∀ᵐ x ∂μ, Q x < ⊤ := ae_lt_top hQmeas' hQint_ne_top
  have hG := memLp_two_toReal_sqrt_of_measurable_lintegral Q hQmeas' hB hQlin'
  have hTmeas' : AEMeasurable T μ := by
    simpa only [T] using hTmeas
  have hTnonneg (x : α) : 0 ≤ T x := by
    dsimp only [T]
    exact ENNReal.toReal_nonneg
  have hGnonneg (x : α) : 0 ≤ G x := by
    dsimp only [G]
    exact Real.sqrt_nonneg _
  have hTG : ∀ᵐ x ∂μ, ‖T x‖ ≤ G x := by
    filter_upwards [hQae] with x hx
    have hQfinite : Q x ≠ ⊤ := ne_of_lt hx
    have hnorm (i : ι) : ‖F i x‖ ≤ G x := by
      change ‖F i x‖ ≤ (Q x).toReal.sqrt
      apply (Real.le_sqrt (norm_nonneg _) ENNReal.toReal_nonneg).2
      calc
        ‖F i x‖ ^ 2 = (ENNReal.ofReal (‖F i x‖ ^ 2)).toReal := by
          rw [ENNReal.toReal_ofReal (sq_nonneg _)]
        _ ≤ (Q x).toReal :=
          (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hQfinite).2
            (le_iSup (fun i : ι => ENNReal.ofReal (‖F i x‖ ^ 2)) i)
    have hraw : (⨆ i : ι, ENNReal.ofReal ‖F i x‖) ≤ ENNReal.ofReal (G x) := by
      apply iSup_le
      intro i
      exact ENNReal.ofReal_le_ofReal (hnorm i)
    have hrawfinite : (⨆ i : ι, ENNReal.ofReal ‖F i x‖) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hraw
    rw [Real.norm_of_nonneg (hTnonneg x)]
    change (⨆ i : ι, ENNReal.ofReal ‖F i x‖).toReal ≤ G x
    calc
      (⨆ i : ι, ENNReal.ofReal ‖F i x‖).toReal ≤
          (ENNReal.ofReal (G x)).toReal :=
        (ENNReal.toReal_le_toReal hrawfinite ENNReal.ofReal_ne_top).2 hraw
      _ = G x := ENNReal.toReal_ofReal (hGnonneg x)
  have hTmem : MemLp T 2 μ := hG.1.mono' hTmeas'.aestronglyMeasurable hTG
  have hTint : Integrable (fun x => ‖T x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hTmem.1).1 hTmem
  have hGint : Integrable (fun x => ‖G x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hG.1.1).1 hG.1
  refine ⟨?_, ?_⟩
  · simpa only [T] using hTmem
  · have hpow : ∀ᵐ x ∂μ, ‖T x‖ ^ 2 ≤ ‖G x‖ ^ 2 := by
      filter_upwards [hTG] with x hx
      exact pow_le_pow_left₀ (norm_nonneg _) (hx.trans (by
        rw [Real.norm_of_nonneg (hGnonneg x)])) 2
    calc
      (∫ x, ‖T x‖ ^ 2 ∂μ) ≤ ∫ x, ‖G x‖ ^ 2 ∂μ :=
        integral_mono_ae hTint hGint hpow
      _ ≤ B := hG.2

/-- The raw positive-radius relative-dyadic square and norm suprema are
measurable after folding the compact bandpass into a fixed Schwartz multiplier. -/
theorem measurable_raw_relative_dyadic_maxima
    {d : Nat} (phi f : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (j : Nat) :
    let Q : Euclidean (d + 1) → ENNReal := fun x =>
      ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal
        (‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
          surfaceFourier (d + 1) (-r.1 • xi) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
            𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ^ 2)
    let T : Euclidean (d + 1) → ℝ := fun x =>
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal
        ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
          surfaceFourier (d + 1) (-r.1 • xi) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
            𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖).toReal
    Measurable Q ∧ Measurable T := by
  obtain ⟨psi, hpsi, hpsi_compact, _⟩ :=
    exists_compactlySupported_schwartzMap_smooth_dyadic_bandpass
      phi hphi_one hphi_zero j
  obtain ⟨chi, hchi⟩ :=
    exists_schwartz_compactSupport_mul_surfaceFourier psi hpsi_compact 1
  have hchi' (xi : Euclidean (d + 1)) :
      chi xi = psi xi * surfaceFourier (d + 1) (-xi) := by
    simpa using hchi xi
  have hmult (r : Ioi (0 : ℝ)) :
      (fun xi : Euclidean (d + 1) =>
        surfaceFourier (d + 1) (-r.1 • xi) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi) =
      fun xi => chi (r.1 • xi) * 𝓕 (f : Euclidean (d + 1) → ℂ) xi := by
    funext xi
    rw [hchi' (r.1 • xi), hpsi]
    rw [show (-(r.1) : ℝ) • xi = -(r.1 • xi) by rw [neg_smul]]
    ring
  have hcont (r : Ioi (0 : ℝ)) : Continuous (fun x : Euclidean (d + 1) =>
      𝓕⁻ (fun xi : Euclidean (d + 1) => chi (r.1 • xi) *
        𝓕 (f : Euclidean (d + 1) → ℂ) xi) x) := by
    simpa [inv_inv] using
      (continuous_fourierInv_scaled_schwartz_multiplier chi f (inv_pos.mpr r.2))
  intro Q T
  have hQrewrite : Q = fun x : Euclidean (d + 1) =>
      ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal
        (‖𝓕⁻ (fun xi : Euclidean (d + 1) => chi (r.1 • xi) *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖ ^ 2) := by
    funext x
    dsimp only [Q]
    simp_rw [hmult]
  have hTrewrite : T = fun x : Euclidean (d + 1) =>
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal
        ‖𝓕⁻ (fun xi : Euclidean (d + 1) => chi (r.1 • xi) *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖).toReal := by
    funext x
    dsimp only [T]
    simp_rw [hmult]
  constructor
  · rw [hQrewrite]
    apply LowerSemicontinuous.measurable
    apply lowerSemicontinuous_iSup
    intro r
    exact (ENNReal.continuous_ofReal.comp ((hcont r).norm.pow 2)).lowerSemicontinuous
  · rw [hTrewrite]
    apply ENNReal.measurable_toReal.comp
    apply LowerSemicontinuous.measurable
    apply lowerSemicontinuous_iSup
    intro r
    exact (ENNReal.continuous_ofReal.comp (hcont r).norm).lowerSemicontinuous

/-- The literal positive-radius relative-dyadic maximal multiplier has the
global strong `L²` bound obtained from its finite dyadic radius exhaustion. -/
theorem memLp_two_iSup_relative_dyadic_moving_bandpass_global_of_sharp
    {d : Nat} (hd : 2 ≤ d) (C0 C1 : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ xi : Euclidean (d + 1), 1 ≤ ‖xi‖ →
      ‖surfaceFourier (d + 1) xi‖ ≤ C0 / ‖xi‖ ^ ((d : ℝ) / 2))
    (hderiv : ∀ xi : Euclidean (d + 1), ∀ r : ℝ, 1 ≤ ‖xi‖ →
      r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • xi)) r‖ ≤
        C1 / ‖xi‖ ^ ((d : ℝ) / 2 - 1))
    (phi f : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphi_norm : ∀ xi, ‖phi xi‖ ≤ 1) (j : Nat) :
    let M : Euclidean (d + 1) → ℝ := fun x =>
      (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal
        ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
          surfaceFourier (d + 1) (-r.1 • xi) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
            𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖).toReal
    MemLp M 2 volume ∧
      (∫ x : Euclidean (d + 1), ‖M x‖ ^ 2) ≤
        24 *
          (((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
            2 * ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) *
              (2 * ((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
                (12 * C0 *
                  ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) phi).toBoundedContinuousFunction‖) /
                  (dyadicScale j) ^ ((d : ℝ) / 2)))) *
          (∫ x : Euclidean (d + 1), ‖f x‖ ^ 2) := by
  classical
  intro M
  let F : Ioi (0 : ℝ) → Euclidean (d + 1) → ℂ := fun r x =>
    𝓕⁻ (fun xi : Euclidean (d + 1) =>
      surfaceFourier (d + 1) (-r.1 • xi) *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
          phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
        𝓕 (f : Euclidean (d + 1) → ℂ) xi) x
  let Q : Euclidean (d + 1) → ENNReal := fun x =>
    ⨆ r : Ioi (0 : ℝ), ENNReal.ofReal (‖F r x‖ ^ 2)
  let u : ℤ → Euclidean (d + 1) → ℝ := fun k x =>
    (⨆ r : Icc ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k), ENNReal.ofReal
      ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
        surfaceFourier (d + 1) (-r.1 • xi) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
          (phi (((2 : ℝ) ^ ((j : ℤ) + 3 - k))⁻¹ • xi) -
            phi (((2 : ℝ) ^ ((j : ℤ) - 2 - k))⁻¹ • xi)) *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖).toReal
  let L : ℝ :=
    ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
      2 * ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) *
        (2 * ((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
          (12 * C0 *
            ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) phi).toBoundedContinuousFunction‖) /
            (dyadicScale j) ^ ((d : ℝ) / 2)))
  let J : ℝ := ∫ x : Euclidean (d + 1), ‖f x‖ ^ 2
  let B : ℝ := 24 * L * J
  have hL : 0 ≤ L := by
    dsimp only [L]
    apply add_nonneg
    · exact sq_nonneg _
    · apply mul_nonneg
      · apply mul_nonneg
        · norm_num
        · exact div_nonneg (mul_nonneg (by norm_num) hC0.le)
            (Real.rpow_nonneg (dyadicScale_pos j).le _)
      · apply mul_nonneg
        · norm_num
        · apply add_nonneg
          · exact div_nonneg (mul_nonneg (by norm_num) hC1.le)
              (Real.rpow_nonneg (dyadicScale_pos j).le _)
          · exact div_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) hC0.le) (norm_nonneg _))
              (Real.rpow_nonneg (dyadicScale_pos j).le _)
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (by norm_num) hL) hJ
  have hfinite (K : Finset ℤ) (hK : K.Nonempty) :
      MemLp (fun x => K.sup' hK (fun k => u k x)) 2 volume ∧
        (∫ x : Euclidean (d + 1), ‖K.sup' hK (fun k => u k x)‖ ^ 2) ≤ B := by
    have h := finite_relative_dyadic_radius_blocks_l2
      hd C0 C1 hC0 hC1 hdecay hderiv phi f hphi_one hphi_zero hphi_norm j K hK
    constructor
    · simpa only [u, mul_assoc] using h.2.1
    · simpa only [u, L, J, B, mul_assoc] using h.2.2
  have hu_meas (k : ℤ) : Measurable (u k) := by
    have h := finite_relative_dyadic_radius_blocks_l2
      hd C0 C1 hC0 hC1 hdecay hderiv phi f hphi_one hphi_zero hphi_norm j ({k} : Finset ℤ)
      (by simp)
    simpa only [u, Finset.sup'_singleton, mul_assoc] using h.1
  have hu_nonneg (k : ℤ) (x : Euclidean (d + 1)) : 0 ≤ u k x := by
    dsimp only [u]
    exact ENNReal.toReal_nonneg
  have htrunc := lintegral_iSup_finset_Icc_sq_le u hu_meas hu_nonneg hfinite
  have hcover : ∀ x : Euclidean (d + 1), Q x ≤
      ⨆ N : ℕ, ENNReal.ofReal
        (((Finset.Icc (-(N : ℤ)) N).sup' (by
          refine ⟨0, ?_⟩
          simp only [Finset.mem_Icc]
          omega) (fun k => u k x)) ^ 2) := by
    simpa only [Q, F, u] using
      (raw_relative_dyadic_bandpass_square_le_iSup_finset_Icc_radius_blocks
        phi f hphi_one hphi_zero j)
  have hQlin : (∫⁻ x, Q x) ≤ ENNReal.ofReal B := by
    calc
      (∫⁻ x, Q x) ≤ ∫⁻ x, ⨆ N : ℕ, ENNReal.ofReal
          (((Finset.Icc (-(N : ℤ)) N).sup' (by
            refine ⟨0, ?_⟩
            simp only [Finset.mem_Icc]
            omega) (fun k => u k x)) ^ 2) :=
        lintegral_mono hcover
      _ ≤ ENNReal.ofReal B := by
        simpa only using htrunc
  have hmeas := measurable_raw_relative_dyadic_maxima phi f hphi_one hphi_zero j
  have hQmeas : Measurable Q := by
    simpa only [Q, F] using hmeas.1
  have hMmeas : AEMeasurable M volume := by
    simpa only [M, F] using hmeas.2.aemeasurable
  have hglobal := memLp_two_toReal_iSup_ennreal_norm_of_sq_lintegral
    F hQmeas hMmeas hB hQlin
  simpa only [M, F, B, L, J] using hglobal

/-- The coefficient in the global relative-dyadic `L²` estimate has the
expected frequency decay. -/
theorem relative_dyadic_global_coefficient_le_exponential
    {d : Nat} (C0 C1 Dphi : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hDphi : 0 ≤ Dphi) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : Nat,
      24 *
        (((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 +
          2 * ((4 * C0) / (dyadicScale j) ^ ((d : ℝ) / 2)) *
            (2 * ((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
              (12 * C0 * Dphi) / (dyadicScale j) ^ ((d : ℝ) / 2)))) ≤
        C * (2 : ℝ) ^ (-((d : ℝ) - 1) * (j : ℝ)) := by
  let K : ℝ :=
    (4 * C0) ^ 2 + 4 * (4 * C0) * (4 * C1) +
      4 * (4 * C0) * (12 * C0 * Dphi)
  refine ⟨24 * K + 1, ?_, ?_⟩
  · have hK : 0 ≤ K := by
      dsimp only [K]
      positivity
    nlinarith
  intro j
  let x : ℝ := dyadicScale j
  have hx : 0 < x := by
    dsimp only [x]
    exact dyadicScale_pos j
  have hx_one : 1 ≤ x := by
    dsimp only [x]
    calc
      1 = dyadicScale 0 := by simp [dyadicScale]
      _ ≤ dyadicScale j := dyadicScale_mono (Nat.zero_le _)
  have hpow : x ^ (-(d : ℝ)) ≤ x ^ (-((d : ℝ) - 1)) := by
    apply Real.rpow_le_rpow_of_exponent_le hx_one
    linarith
  have hA2 :
      ((4 * C0) / x ^ ((d : ℝ) / 2)) ^ 2 =
        (4 * C0) ^ 2 * x ^ (-(d : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hAB :
      ((4 * C0) / x ^ ((d : ℝ) / 2)) *
        ((4 * C1) / x ^ ((d : ℝ) / 2 - 1)) =
          (4 * C0) * (4 * C1) * x ^ (-((d : ℝ) - 1)) := by
    calc
      ((4 * C0) / x ^ ((d : ℝ) / 2)) *
          ((4 * C1) / x ^ ((d : ℝ) / 2 - 1)) =
          (4 * C0) * (4 * C1) *
            (x ^ (-((d : ℝ) / 2)) * x ^ (-((d : ℝ) / 2 - 1))) := by
        simp only [div_eq_mul_inv, ← Real.rpow_neg hx.le]
        ring
      _ = (4 * C0) * (4 * C1) * x ^ (-((d : ℝ) - 1)) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
  have hAE :
      ((4 * C0) / x ^ ((d : ℝ) / 2)) *
        ((12 * C0 * Dphi) / x ^ ((d : ℝ) / 2)) =
          (4 * C0) * (12 * C0 * Dphi) * x ^ (-(d : ℝ)) := by
    calc
      ((4 * C0) / x ^ ((d : ℝ) / 2)) *
          ((12 * C0 * Dphi) / x ^ ((d : ℝ) / 2)) =
          (4 * C0) * (12 * C0 * Dphi) *
            (x ^ (-((d : ℝ) / 2)) * x ^ (-((d : ℝ) / 2))) := by
        simp only [div_eq_mul_inv, ← Real.rpow_neg hx.le]
        ring
      _ = (4 * C0) * (12 * C0 * Dphi) * x ^ (-(d : ℝ)) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
  have hA2_le : (4 * C0) ^ 2 * x ^ (-(d : ℝ)) ≤
      (4 * C0) ^ 2 * x ^ (-((d : ℝ) - 1)) := by
    exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  have hAE_le :
      (4 * C0) * (12 * C0 * Dphi) * x ^ (-(d : ℝ)) ≤
        (4 * C0) * (12 * C0 * Dphi) * x ^ (-((d : ℝ) - 1)) := by
    apply mul_le_mul_of_nonneg_left hpow
    positivity
  have hsplit (a b e : ℝ) : 2 * a * (2 * (b + e)) =
      4 * (a * b) + 4 * (a * e) := by
    ring
  have hL :
      (((4 * C0) / x ^ ((d : ℝ) / 2)) ^ 2 +
        2 * ((4 * C0) / x ^ ((d : ℝ) / 2)) *
          (2 * ((4 * C1) / x ^ ((d : ℝ) / 2 - 1) +
            (12 * C0 * Dphi) / x ^ ((d : ℝ) / 2)))) ≤
        K * x ^ (-((d : ℝ) - 1)) := by
    rw [hsplit]
    rw [hA2, hAB, hAE]
    dsimp only [K]
    nlinarith
  have hq : 0 ≤ x ^ (-((d : ℝ) - 1)) := Real.rpow_nonneg hx.le _
  have hmain :
      24 *
        (((4 * C0) / x ^ ((d : ℝ) / 2)) ^ 2 +
          2 * ((4 * C0) / x ^ ((d : ℝ) / 2)) *
            (2 * ((4 * C1) / x ^ ((d : ℝ) / 2 - 1) +
              (12 * C0 * Dphi) / x ^ ((d : ℝ) / 2)))) ≤
        (24 * K + 1) * x ^ (-((d : ℝ) - 1)) := by
    nlinarith
  have hx_eq : x ^ (-((d : ℝ) - 1)) =
      (2 : ℝ) ^ (-((d : ℝ) - 1) * (j : ℝ)) := by
    dsimp only [x]
    rw [dyadicScale, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simpa only [x, hx_eq] using hmain

/-- The global relative-dyadic `L²` estimate in the form needed for summing
the annuli: its constant decays exponentially in the frequency index. -/
theorem exists_memLp_two_iSup_relative_dyadic_moving_bandpass_global_exponential_of_sharp
    {d : Nat} (hd : 2 ≤ d) (C0 C1 : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ xi : Euclidean (d + 1), 1 ≤ ‖xi‖ →
      ‖surfaceFourier (d + 1) xi‖ ≤ C0 / ‖xi‖ ^ ((d : ℝ) / 2))
    (hderiv : ∀ xi : Euclidean (d + 1), ∀ r : ℝ, 1 ≤ ‖xi‖ →
      r ∈ Icc (1 : ℝ) 2 →
      ‖deriv (fun s : ℝ => surfaceFourier (d + 1) (s • xi)) r‖ ≤
        C1 / ‖xi‖ ^ ((d : ℝ) / 2 - 1))
    (phi : SchwartzMap (Euclidean (d + 1)) ℂ)
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphi_norm : ∀ xi, ‖phi xi‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Nat) (f : SchwartzMap (Euclidean (d + 1)) ℂ),
      let M : Euclidean (d + 1) → ℝ := fun x =>
        (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal
          ‖𝓕⁻ (fun xi : Euclidean (d + 1) =>
            surfaceFourier (d + 1) (-r.1 • xi) *
              (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
                phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
              𝓕 (f : Euclidean (d + 1) → ℂ) xi) x‖).toReal
      MemLp M 2 volume ∧
        (∫ x : Euclidean (d + 1), ‖M x‖ ^ 2) ≤
          C * (2 : ℝ) ^ (-((d : ℝ) - 1) * (j : ℝ)) *
            (∫ x : Euclidean (d + 1), ‖f x‖ ^ 2) := by
  let Dphi : ℝ :=
    ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ) phi).toBoundedContinuousFunction‖
  obtain ⟨C, hC, hcoeff⟩ := relative_dyadic_global_coefficient_le_exponential
    C0 C1 Dphi hC0 hC1 (norm_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro j f
  have hglobal := memLp_two_iSup_relative_dyadic_moving_bandpass_global_of_sharp
    hd C0 C1 hC0 hC1 hdecay hderiv phi f hphi_one hphi_zero hphi_norm j
  refine ⟨hglobal.1, hglobal.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right (hcoeff j)
  exact integral_nonneg fun _ => sq_nonneg _

/-- In every ambient dimension at least three, the literal all-radius
relative-dyadic maximal multiplier has exponentially decaying strong `L²`
norm. -/
theorem exists_memLp_two_iSup_relative_dyadic_moving_bandpass_global_exponential
    {n : Nat} (hn : 3 ≤ n) (phi : SchwartzMap (Euclidean n) ℂ)
    (hphi_one : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphi_zero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphi_norm : ∀ xi, ‖phi xi‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Nat) (f : SchwartzMap (Euclidean n) ℂ),
      let M : Euclidean n → ℝ := fun x =>
        (⨆ r : Ioi (0 : ℝ), ENNReal.ofReal
          ‖𝓕⁻ (fun xi : Euclidean n =>
            surfaceFourier n (-r.1 • xi) *
              (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r.1 • xi)) -
                phi (((2 : ℝ) ^ j)⁻¹ • (r.1 • xi))) *
              𝓕 (f : Euclidean n → ℂ) xi) x‖).toReal
      MemLp M 2 volume ∧
        (∫ x : Euclidean n, ‖M x‖ ^ 2) ≤
          C * (2 : ℝ) ^ (-((n : ℝ) - 2) * (j : ℝ)) *
            (∫ x : Euclidean n, ‖f x‖ ^ 2) := by
  cases n with
  | zero => omega
  | succ m =>
    have hm : 2 ≤ m := by omega
    obtain ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩ :=
      exists_sharp_surfaceFourier_succ_decay_and_deriv (d := m) hm
    obtain ⟨C, hC, hinner⟩ :=
      exists_memLp_two_iSup_relative_dyadic_moving_bandpass_global_exponential_of_sharp
        hm C0 C1 hC0 hC1 hdecay hderiv phi hphi_one hphi_zero hphi_norm
    refine ⟨C, hC, ?_⟩
    intro j f
    have h := hinner j f
    have hcast : (m : ℝ) - 1 = ((m + 1 : Nat) : ℝ) - 2 := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    simpa only [hcast] using h

end LeanSpherical.HarmonicAnalysis
