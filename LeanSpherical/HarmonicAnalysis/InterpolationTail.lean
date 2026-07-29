/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.InterpolationCore

/-!
# Marcinkiewicz interpolation: applications

This module collects the scaled and endpoint applications of the core
Marcinkiewicz interpolation argument.
-/

open Filter MeasureTheory Set ENNReal

noncomputable section

namespace LeanSpherical.HarmonicAnalysis

/-- The split form of real-endpoint Marcinkiewicz interpolation with a
positive amplitude threshold scale.  The profiles are supplied at parameter
`r`, while the interpolation step uses the actual split at `r = s * t`; the
two displayed powers of `s` are proved by the preceding half-line
change-of-variables lemmas. -/
theorem marcinkiewicz_one_two_on_additive_split_real_scaled
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hmem_one : ∀ (g : F), g ∈ D → MemLp (T g) 1 μ)
    (hbound_one : ∀ (g : F), g ∈ D →
      (∫ x, T g x ∂μ) ≤ c₁ * ∫ x, ‖eval g x‖ ∂μ)
    (hinput_one : ∀ (g : F), g ∈ D →
      Integrable (fun x => ‖eval g x‖) μ)
    (hmem_two : ∀ (g : F), g ∈ D → MemLp (T g) 2 μ)
    (hbound_two : ∀ (g : F), g ∈ D →
      (∫ x, (T g x) ^ (2 : ℕ) ∂μ) ≤
        c₂ * ∫ x, ‖eval g x‖ ^ (2 : ℕ) ∂μ)
    (hinput_two : ∀ (g : F), g ∈ D →
      Integrable (fun x => ‖eval g x‖ ^ (2 : ℕ)) μ)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlowI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ))
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ))
    (A₂ A₁ : ℝ≥0∞)
    (hlow_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) ≤ A₂)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) ≤ A₁)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        (4 * ENNReal.ofReal c₂ * ((ENNReal.ofReal s) ^ (2 - p) * A₂) +
          2 * ENNReal.ofReal c₁ * ((ENNReal.ofReal s) ^ (1 - p) * A₁)) := by
  apply marcinkiewicz_one_two_on_additive_split_real D eval T hT_nonneg hT_subadd
    c₁ c₂ hc₁ hc₂ hmem_one hbound_one hinput_one hmem_two hbound_two hinput_two
    hp1 hp2 f hTf (fun t => low (s * t)) (fun t => high (s * t))
    ?_ ?_ ?_ ?_ ?_ ((ENNReal.ofReal s) ^ (2 - p) * A₂)
    ((ENNReal.ofReal s) ^ (1 - p) * A₁) ?_ ?_
  · intro t
    exact hlow_mem (s * t)
  · intro t
    exact hhigh_mem (s * t)
  · intro t
    exact hsplit (s * t)
  · change Measurable ((fun r : ℝ =>
        ∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ) ∘
        fun t : ℝ => s * t)
    exact hlowI_meas.comp (measurable_const_mul s)
  · change Measurable ((fun r : ℝ =>
        ∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ) ∘ fun t : ℝ => s * t)
    exact hhighI_meas.comp (measurable_const_mul s)
  · calc
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low (s * t)) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) =
          (ENNReal.ofReal s) ^ (2 - p) *
            (∫⁻ r in Ioi (0 : ℝ),
              (∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ) *
                (ENNReal.ofReal r) ^ (p - 3)) :=
        lintegral_Ioi_comp_mul_low_weight
          (fun r => ∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ)
          hlowI_meas s hs p
      _ ≤ (ENNReal.ofReal s) ^ (2 - p) * A₂ := by
        exact mul_le_mul_right hlow_tail _
  · calc
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high (s * t)) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) =
          (ENNReal.ofReal s) ^ (1 - p) *
            (∫⁻ r in Ioi (0 : ℝ),
              (∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ) *
                (ENNReal.ofReal r) ^ (p - 2)) :=
        lintegral_Ioi_comp_mul_high_weight
          (fun r => ∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ)
          hhighI_meas s hs p
      _ ≤ (ENNReal.ofReal s) ^ (1 - p) * A₁ := by
        exact mul_le_mul_right hhigh_tail _

/-- A strong `L¹`/`L²` form of `marcinkiewicz_weak_one_two`.  The endpoint
hypotheses are lower-integral estimates for an unbundled nonnegative,
subadditive operator; the conclusion is its explicit `Lᵖ` bound for
`1 < p < 2`. -/
theorem marcinkiewicz_one_two
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (T : (α → E) → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ g h x, T (g + h) x ≤ T g x + T h x)
    (hTmeas : ∀ g, AEMeasurable (T g) μ)
    (C₁ C₂ : ℝ≥0∞)
    (hstrong_one : ∀ g,
      (∫⁻ x, ENNReal.ofReal (T g x) ∂μ) ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ))
    (hstrong_two : ∀ g,
      (∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ) ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : α → E) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        ((4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ +
          2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) := by
  apply marcinkiewicz_weak_one_two T hT_nonneg hT_subadd C₁ C₂ ?_ ?_ hp1 hp2 f hf
    (hTmeas f)
  · intro g s hs
    calc
      ENNReal.ofReal s * μ {x | s < T g x} ≤
          ENNReal.ofReal s * μ {x | ENNReal.ofReal s ≤ ENNReal.ofReal (T g x)} := by
        apply mul_le_mul_right
        apply measure_mono
        intro x hx
        exact ENNReal.ofReal_le_ofReal hx.le
      _ ≤ ∫⁻ x, ENNReal.ofReal (T g x) ∂μ :=
        mul_meas_ge_le_lintegral₀ (hTmeas g).ennreal_ofReal (ENNReal.ofReal s)
      _ ≤ C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ) := hstrong_one g
  · intro g s hs
    calc
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤
          ENNReal.ofReal (s ^ (2 : ℕ)) *
            μ {x | ENNReal.ofReal (s ^ (2 : ℕ)) ≤
              ENNReal.ofReal ((T g x) ^ (2 : ℕ))} := by
        apply mul_le_mul_right
        apply measure_mono
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        exact pow_le_pow_left₀ hs.le hx.le 2
      _ ≤ ∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ :=
        mul_meas_ge_le_lintegral₀ ((hTmeas g).pow_const 2).ennreal_ofReal
          (ENNReal.ofReal (s ^ (2 : ℕ)))
      _ ≤ C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ) := hstrong_two g

theorem memLp_of_lintegral_ofReal_rpow_lt_top
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : α → ℝ) (hg : AEMeasurable g μ) (hnonneg : ∀ x, 0 ≤ g x)
    {p : ℝ} (hp : 0 < p)
    (h : (∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ) < ∞) :
    MemLp g (ENNReal.ofReal p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt).mpr
  calc
    (∫⁻ x, ‖g x‖ₑ ^ (ENNReal.ofReal p).toReal ∂μ) =
        ∫⁻ x, (ENNReal.ofReal (g x)) ^ p ∂μ := by
      rw [ENNReal.toReal_ofReal hp.le]
      apply lintegral_congr
      intro x
      rw [enorm_eq_nnnorm]
      rw [Real.nnnorm_of_nonneg (hnonneg x)]
      rw [← ENNReal.ofReal_eq_coe_nnreal (hnonneg x)]
    _ = ∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ := by
      apply lintegral_congr
      intro x
      exact ENNReal.ofReal_rpow_of_nonneg (hnonneg x) hp.le
    _ < ∞ := h

/-- Finite endpoint constants carry the explicit lower-integral estimate in
`marcinkiewicz_one_two` to membership in `Lᵖ`. -/
theorem marcinkiewicz_one_two_memLp
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (T : (α → E) → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ g h x, T (g + h) x ≤ T g x + T h x)
    (hTmeas : ∀ g, AEMeasurable (T g) μ)
    (C₁ C₂ : ℝ≥0∞) (hC₁ : C₁ < ∞) (hC₂ : C₂ < ∞)
    (hstrong_one : ∀ g,
      (∫⁻ x, ENNReal.ofReal (T g x) ∂μ) ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ))
    (hstrong_two : ∀ g,
      (∫⁻ x, ENNReal.ofReal ((T g x) ^ (2 : ℕ)) ∂μ) ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : α → E) (hf : Measurable f) (hfp : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (T f) (ENNReal.ofReal p) μ := by
  have hp : 0 < p := by linarith
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hinput : (∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) < ∞ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt).mp hfp.2
    simpa [ENNReal.toReal_ofReal hp.le, enorm_eq_nnnorm] using h
  have hinv_one : (ENNReal.ofReal (p - 1))⁻¹ < ∞ := by
    apply ENNReal.inv_lt_top.mpr
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hinv_two : (ENNReal.ofReal (2 - p))⁻¹ < ∞ := by
    apply ENNReal.inv_lt_top.mpr
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hlarge : 4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ < ∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hC₂) hinv_two
  have hsmall : 2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ < ∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hC₁) hinv_one
  have hright : ENNReal.ofReal p *
      ((4 * C₂ * (ENNReal.ofReal (2 - p))⁻¹ +
        2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹) *
        ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) < ∞ := by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    apply ENNReal.mul_lt_top
    · exact ENNReal.add_lt_top.mpr ⟨hlarge, hsmall⟩
    · exact hinput
  apply memLp_of_lintegral_ofReal_rpow_lt_top (T f) (hTmeas f) (hT_nonneg f) hp
  apply lt_of_le_of_lt
    (marcinkiewicz_one_two T hT_nonneg hT_subadd hTmeas C₁ C₂
      hstrong_one hstrong_two hp1 hp2 f hf)
  exact hright

/-- Marcinkiewicz interpolation between weak `(1,1)` and the pointwise
`L∞` contraction, on bounded inputs.  This is the form needed for the
dyadic-ball maximal operator: the low-amplitude truncation is killed by the
contraction, and the weak endpoint is integrated only over the
high-amplitude tail.  Restricting the interface to bounded inputs is
intentional: a real-valued maximal function formed with `ENNReal.toReal`
need not remain subadditive when an unbounded input has infinite averages. -/
theorem marcinkiewicz_weak_one_top
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (T : (α → E) → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ g h, Measurable g → Measurable h →
      (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖g x‖ ≤ a) →
      (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖h x‖ ≤ a) →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (C₁ : ℝ≥0∞)
    (hweak_one : ∀ (g : α → E), Measurable g →
      (∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖g x‖ ≤ a) → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * μ {x | s < T g x} ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ))
    (hT_top : ∀ (g : α → E) (a : ℝ), 0 ≤ a →
      (∀ x, ‖g x‖ ≤ a) → ∀ x, T g x ≤ a)
    {p : ℝ} (hp : 1 < p)
    (f : α → E) (hf : Measurable f)
    (hf_bounded : ∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖f x‖ ≤ a)
    (hTf : AEMeasurable (T f) μ) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        (2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) := by
  /- Split at half the output height.  The low piece has pointwise norm at
  most `t / 2`, hence contributes no points to `{t < T f}`. -/
  let u : α → ℝ := fun x => ‖f x‖
  let low : ℝ → α → E := fun t => {x | u x < t / 2}.indicator f
  let high : ℝ → α → E := fun t => {x | t / 2 ≤ u x}.indicator f
  let highI : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x in {x | t / 2 ≤ u x}, ENNReal.ofReal (u x) ∂μ
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 1))
  let whigh : ℝ → ℝ≥0∞ := fun t => (ENNReal.ofReal t) ^ (p - 2)
  have hu : Measurable u := by
    simpa only [u] using hf.norm
  have hu_nonneg : ∀ x, 0 ≤ u x := fun x => by
    dsimp only [u]
    exact norm_nonneg _
  have hvhigh : Measurable (fun x => ENNReal.ofReal (u x)) :=
    hu.ennreal_ofReal
  have hwhigh : Measurable whigh := by
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hhighI_meas : Measurable highI := by
    have hbase : Measurable (fun s : ℝ =>
        ∫⁻ x in {x | s ≤ u x}, ENNReal.ofReal (u x) ∂μ) :=
      measurable_lintegral_indicator_le u hu _ hvhigh
    change Measurable (fun t : ℝ =>
      (fun s : ℝ => ∫⁻ x in {x | s ≤ u x}, ENNReal.ofReal (u x) ∂μ) (t / 2))
    exact hbase.comp (measurable_id.div_const 2)
  have hhigh_norm (t : ℝ) :
      (∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) = highI t := by
    change (∫⁻ x, ENNReal.ofReal ‖{x | t / 2 ≤ u x}.indicator f x‖ ∂μ) = _
    dsimp only [highI]
    have hset : MeasurableSet {x | t / 2 ≤ u x} :=
      measurableSet_le measurable_const hu
    rw [← lintegral_indicator hset]
    apply lintegral_congr
    intro x
    by_cases hx : t / 2 ≤ u x <;> simp [hx, u]
  have hlow_meas (t : ℝ) : Measurable (low t) := by
    dsimp only [low]
    exact hf.indicator (measurableSet_lt hu measurable_const)
  have hhigh_meas (t : ℝ) : Measurable (high t) := by
    dsimp only [high]
    exact hf.indicator (measurableSet_le measurable_const hu)
  have hlow_norm (t : ℝ) (ht : 0 < t) : ∀ x, ‖low t x‖ ≤ t / 2 := by
    intro y
    change ‖{x | u x < t / 2}.indicator f y‖ ≤ t / 2
    by_cases hy : u y < t / 2
    · simpa [hy, u] using hy.le
    · have hnot : y ∉ {x | u x < t / 2} := by
        simpa only [Set.mem_setOf_eq] using hy
      rw [Set.indicator_of_notMem hnot, norm_zero]
      positivity
  have hlow_bounded (t : ℝ) (ht : 0 < t) :
      ∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖low t x‖ ≤ a := by
    exact ⟨t / 2, (by positivity), hlow_norm t ht⟩
  have hlow_bound (t : ℝ) (ht : 0 < t) (x : α) :
      T (low t) x ≤ t / 2 := by
    apply hT_top (low t) (t / 2) (by positivity)
    exact hlow_norm t ht
  have hhigh_bounded (t : ℝ) :
      ∃ a : ℝ, 0 ≤ a ∧ ∀ x, ‖high t x‖ ≤ a := by
    rcases hf_bounded with ⟨a, ha, hfa⟩
    refine ⟨a, ha, ?_⟩
    intro y
    change ‖{x | t / 2 ≤ u x}.indicator f y‖ ≤ a
    by_cases hy : t / 2 ≤ u y
    · simpa [hy] using hfa y
    · simp [hy, ha]
  have hsplit (t : ℝ) : f = low t + high t := by
    funext x
    by_cases hx : u x < t / 2
    · simp [low, high, hx]
    · have hx' : t / 2 ≤ u x := le_of_not_gt hx
      simp [low, high, hx, hx']
  have hdistribution (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} ≤ μ {x | t / 2 < T (high t) x} := by
    apply measure_mono
    intro x hx
    rw [hsplit t] at hx
    have hsum := hT_subadd (low t) (high t) (hlow_meas t) (hhigh_meas t)
      (hlow_bounded t ht) (hhigh_bounded t) x
    have hlow := hlow_bound t ht x
    by_contra h
    have hhigh : T (high t) x ≤ t / 2 := le_of_not_gt h
    have : T (low t + high t) x ≤ t := by
      calc
        T (low t + high t) x ≤ T (low t) x + T (high t) x := hsum
        _ ≤ t / 2 + t / 2 := add_le_add hlow hhigh
        _ = t := by ring
    exact (not_lt_of_ge this) hx
  have hhigh_endpoint (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (t / 2) * μ {x | t / 2 < T (high t) x} ≤ C₁ * highI t := by
    calc
      ENNReal.ofReal (t / 2) * μ {x | t / 2 < T (high t) x} ≤
          C₁ * (∫⁻ x, ENNReal.ofReal ‖high t x‖ ∂μ) :=
        hweak_one (high t) (hhigh_meas t) (hhigh_bounded t)
          (by positivity)
      _ = C₁ * highI t := by rw [hhigh_norm]
  have hdistribution_weight (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} * w t ≤ 2 * C₁ * highI t * whigh t := by
    dsimp only [w, whigh]
    calc
      μ {x | t < T f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
          μ {x | t / 2 < T (high t) x} * ENNReal.ofReal (t ^ (p - 1)) :=
        mul_le_mul_of_nonneg_right (hdistribution t ht) (by simp)
      _ ≤ 2 * C₁ * highI t * ENNReal.ofReal (t ^ (p - 2)) := by
        simpa only [ENNReal.ofReal_rpow_of_pos ht] using
          (direct_weak_one_weighted (p := p) ht (hhigh_endpoint t ht))
      _ = 2 * C₁ * highI t * (ENNReal.ofReal t) ^ (p - 2) := by
        rw [ENNReal.ofReal_rpow_of_pos ht]
  /- The remaining three facts are, respectively, the measurable
  high-tail integral, the change of variables `t = 2s`, and layer cake.
  They remain explicit to expose the actual interpolation argument. -/
  have hdistribution_integral :
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) ≤
        ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hdistribution_weight t ht
  have hhigh_integral :
      (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
        2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
    let baseI : ℝ → ℝ≥0∞ := fun s =>
      ∫⁻ x in {x | s ≤ u x}, ENNReal.ofReal (u x) ∂μ
    have hbaseI_meas : Measurable baseI := by
      dsimp only [baseI]
      exact measurable_lintegral_indicator_le u hu _ hvhigh
    have hhigh_eq (t : ℝ) : highI t = baseI (t / 2) := rfl
    have hbase_tail :
        (∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2)) =
          (ENNReal.ofReal (p - 1))⁻¹ *
            ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
      calc
        (∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2)) =
            ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal t) ^ (p - 2) * baseI t := by
              apply lintegral_congr
              intro t
              exact mul_comm _ _
        _ = ∫⁻ x, ENNReal.ofReal (u x) *
            (∫⁻ t in Ioc (0 : ℝ) (u x), (ENNReal.ofReal t) ^ (p - 2)) ∂μ := by
              rw [lintegral_swap_indicator_le u hu _ hvhigh _ hwhigh]
        _ = (ENNReal.ofReal (p - 1))⁻¹ *
            ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
              exact lintegral_ofReal_mul_lintegral_rpow_Ioc_eq u hu hu_nonneg hp
    have hcoefficient :
        (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - 2)) *
            ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) =
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) := by
      have htwo0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
      have htwoT : ENNReal.ofReal (2 : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
      have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) =
          (ENNReal.ofReal (2 : ℝ))⁻¹ := by
        rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num]
        exact ENNReal.ofReal_inv_of_pos (by norm_num)
      have hinvhalf : ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) = ENNReal.ofReal (2 : ℝ) := by
        norm_num
      rw [hhalf, hinvhalf, ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
      calc
        (ENNReal.ofReal (2 : ℝ)) ^ (p - 2) * ENNReal.ofReal (2 : ℝ) =
            (ENNReal.ofReal (2 : ℝ)) ^ (p - 2) *
              (ENNReal.ofReal (2 : ℝ)) ^ (1 : ℝ) := by
              rw [ENNReal.rpow_one]
        _ = (ENNReal.ofReal (2 : ℝ)) ^ ((p - 2) + 1) :=
          (ENNReal.rpow_add (p - 2) 1 htwo0 htwoT).symm
        _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) := by
          congr 1
          ring
    have hscale :
        (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) =
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
            ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2) := by
      calc
        (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) =
            ∫⁻ t in Ioi (0 : ℝ),
              baseI (((1 : ℝ) / 2) * t) * (ENNReal.ofReal t) ^ (p - 2) := by
              apply lintegral_congr
              intro t
              rw [hhigh_eq]
              dsimp only [whigh]
              congr 2
              ring
        _ = (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - 2)) *
            (ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) *
              ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2)) :=
              lintegral_Ioi_comp_mul_weight baseI hbaseI_meas ((1 : ℝ) / 2)
                (by norm_num) (p - 2)
        _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
            ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2) := by
              calc
                (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - 2)) *
                    (ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) *
                      ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2)) =
                    ((ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - 2)) *
                      ENNReal.ofReal (((1 : ℝ) / 2)⁻¹)) *
                        ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2) := by
                          ac_rfl
                _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
                    ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2) := by
                      rw [hcoefficient]
    calc
      (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
          (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := by
            have hconst :
                (∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highI t * whigh t)) =
                  (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) :=
              lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
                (2 * C₁) (hhighI_meas.mul hwhigh)
            calc
              (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) =
                  ∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highI t * whigh t) := by
                    apply lintegral_congr
                    intro t
                    ac_rfl
              _ = (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := hconst
      _ = (2 * C₁) * ((ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ t in Ioi (0 : ℝ), baseI t * (ENNReal.ofReal t) ^ (p - 2)) := by
            rw [hscale]
      _ = 2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
            rw [hbase_tail]
            ac_rfl
  have hp_pos : 0 < p := by linarith
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) := by
      simpa only [w] using
        (lintegral_rpow_eq_lintegral_meas_lt_mul μ
          (Filter.Eventually.of_forall (hT_nonneg f)) hTf hp_pos)
    _ ≤ ENNReal.ofReal p *
        (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highI t * whigh t) :=
      mul_le_mul_right hdistribution_integral _
    _ = ENNReal.ofReal p *
        (2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) := by rw [hhigh_integral]
    _ = ENNReal.ofReal p *
        (2 * C₁ * (ENNReal.ofReal (p - 1))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (p - 1) *
          ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ p ∂μ) := by rfl

private theorem rpow_mul_lintegral_rpow_Ioc_eq
    {u q p : ℝ} (hu : 0 ≤ u) (hq : 0 < q) (hqp : 0 < p - q) :
    (ENNReal.ofReal u) ^ q *
      (∫⁻ t in Ioc (0 : ℝ) u,
        (ENNReal.ofReal t) ^ (p - q - 1)) =
      (ENNReal.ofReal (p - q))⁻¹ * (ENNReal.ofReal u) ^ p := by
  have hr : 1 < p - q + 1 := by linarith
  rw [show p - q - 1 = (p - q + 1) - 2 by ring]
  rw [lintegral_rpow_Ioc_eq hr hu]
  rw [show p - q + 1 - 1 = p - q by ring]
  rcases hu.eq_or_lt with rfl | hu
  · have hp : 0 < p := by linarith
    simp only [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq,
      zero_mul, ENNReal.zero_rpow_of_pos hp, mul_zero]
  rw [ENNReal.ofReal_div_of_pos hqp]
  rw [← ENNReal.ofReal_rpow_of_pos hu]
  have hu0 : ENNReal.ofReal u ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hu
  have hutop : ENNReal.ofReal u ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [div_eq_mul_inv]
  calc
    ENNReal.ofReal u ^ q *
        (ENNReal.ofReal u ^ (p - q) * (ENNReal.ofReal (p - q))⁻¹) =
        (ENNReal.ofReal u ^ q * ENNReal.ofReal u ^ (p - q)) *
          (ENNReal.ofReal (p - q))⁻¹ := by ac_rfl
    _ = ENNReal.ofReal u ^ p * (ENNReal.ofReal (p - q))⁻¹ := by
      rw [← ENNReal.rpow_add _ _ hu0 hutop]
      congr 1
      ring_nf
    _ = (ENNReal.ofReal (p - q))⁻¹ * ENNReal.ofReal u ^ p := by ac_rfl

/-- The exact high-amplitude tail identity behind weak `(q,q)`--`L∞`
interpolation.  It is valid for every `0 < q < p`; the split at `t / 2`
is an amplitude threshold, not a restriction on the range of `p`. -/
theorem lintegral_high_tail_rpow_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (u : α → ℝ) (hu : Measurable u) (hu_nonneg : ∀ x, 0 ≤ u x)
    {q p : ℝ} (hq : 0 < q) (hqp : q < p) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t / 2 ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ) *
        (ENNReal.ofReal t) ^ (p - q - 1)) =
      (ENNReal.ofReal (p - q))⁻¹ *
        (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
  let baseI : ℝ → ENNReal := fun s =>
    ∫⁻ x in {x | s ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ
  let highI : ℝ → ENNReal := fun t =>
    ∫⁻ x in {x | t / 2 ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ
  let whigh : ℝ → ENNReal := fun t =>
    (ENNReal.ofReal t) ^ (p - q - 1)
  have hqp0 : 0 < p - q := sub_pos.mpr hqp
  have hv : Measurable (fun x => (ENNReal.ofReal (u x)) ^ q) :=
    ENNReal.continuous_rpow_const.measurable.comp hu.ennreal_ofReal
  have hbaseI_meas : Measurable baseI := by
    dsimp only [baseI]
    exact measurable_lintegral_indicator_le (μ := μ) u hu _ hv
  have hwhigh : Measurable whigh := by
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hbase_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        baseI t * (ENNReal.ofReal t) ^ (p - q - 1)) =
        (ENNReal.ofReal (p - q))⁻¹ *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
    calc
      (∫⁻ t in Ioi (0 : ℝ),
        baseI t * (ENNReal.ofReal t) ^ (p - q - 1)) =
          ∫⁻ t in Ioi (0 : ℝ),
            (ENNReal.ofReal t) ^ (p - q - 1) * baseI t := by
              apply lintegral_congr
              intro t
              exact mul_comm _ _
      _ = ∫⁻ x, (ENNReal.ofReal (u x)) ^ q *
          (∫⁻ t in Ioc (0 : ℝ) (u x),
            (ENNReal.ofReal t) ^ (p - q - 1)) ∂μ := by
              rw [lintegral_swap_indicator_le (μ := μ) u hu _ hv _ hwhigh]
      _ = (ENNReal.ofReal (p - q))⁻¹ *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
            rw [show (fun x => (ENNReal.ofReal (u x)) ^ q *
                (∫⁻ t in Ioc (0 : ℝ) (u x),
                  (ENNReal.ofReal t) ^ (p - q - 1))) =
                fun x => (ENNReal.ofReal (p - q))⁻¹ *
                  (ENNReal.ofReal (u x)) ^ p by
              funext x
              exact rpow_mul_lintegral_rpow_Ioc_eq (hu_nonneg x) hq hqp0]
            exact lintegral_const_mul (μ := μ) _
              (ENNReal.continuous_rpow_const.measurable.comp hu.ennreal_ofReal)
  have hcoefficient :
      (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
          ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) =
        (ENNReal.ofReal (2 : ℝ)) ^ (p - q) := by
    have htwo0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
    have htwoT : ENNReal.ofReal (2 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) =
        (ENNReal.ofReal (2 : ℝ))⁻¹ := by
      rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num]
      exact ENNReal.ofReal_inv_of_pos (by norm_num)
    have hinvhalf : ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) = ENNReal.ofReal (2 : ℝ) := by
      norm_num
    rw [hhalf, hinvhalf, ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
    calc
      (ENNReal.ofReal (2 : ℝ)) ^ (p - q - 1) * ENNReal.ofReal (2 : ℝ) =
          (ENNReal.ofReal (2 : ℝ)) ^ (p - q - 1) *
            (ENNReal.ofReal (2 : ℝ)) ^ (1 : ℝ) := by
              rw [ENNReal.rpow_one]
      _ = (ENNReal.ofReal (2 : ℝ)) ^ ((p - q - 1) + 1) :=
        (ENNReal.rpow_add (p - q - 1) 1 htwo0 htwoT).symm
      _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) := by
        congr 1
        ring
  have hscale :
      (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) =
        (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
          ∫⁻ t in Ioi (0 : ℝ),
            baseI t * (ENNReal.ofReal t) ^ (p - q - 1) := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) =
          ∫⁻ t in Ioi (0 : ℝ),
            baseI (((1 : ℝ) / 2) * t) *
              (ENNReal.ofReal t) ^ (p - q - 1) := by
            apply lintegral_congr
            intro t
            change baseI (t / 2) * (ENNReal.ofReal t) ^ (p - q - 1) = _
            congr 2
            ring
      _ = (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
          (ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) *
            ∫⁻ t in Ioi (0 : ℝ),
              baseI t * (ENNReal.ofReal t) ^ (p - q - 1)) :=
        lintegral_Ioi_comp_mul_weight baseI hbaseI_meas ((1 : ℝ) / 2)
          (by norm_num) (p - q - 1)
      _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
          ∫⁻ t in Ioi (0 : ℝ),
            baseI t * (ENNReal.ofReal t) ^ (p - q - 1) := by
          calc
            (ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
                (ENNReal.ofReal (((1 : ℝ) / 2)⁻¹) *
                  ∫⁻ t in Ioi (0 : ℝ),
                    baseI t * (ENNReal.ofReal t) ^ (p - q - 1)) =
                ((ENNReal.ofReal ((1 : ℝ) / 2)) ^ (-(p - q - 1)) *
                  ENNReal.ofReal (((1 : ℝ) / 2)⁻¹)) *
                    ∫⁻ t in Ioi (0 : ℝ),
                      baseI t * (ENNReal.ofReal t) ^ (p - q - 1) := by ac_rfl
            _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
                ∫⁻ t in Ioi (0 : ℝ),
                  baseI t * (ENNReal.ofReal t) ^ (p - q - 1) := by
              rw [hcoefficient]
  calc
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t / 2 ≤ u x}, (ENNReal.ofReal (u x)) ^ q ∂μ) *
        (ENNReal.ofReal t) ^ (p - q - 1)) =
        ∫⁻ t in Ioi (0 : ℝ), highI t * whigh t := by rfl
    _ = (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
        ∫⁻ t in Ioi (0 : ℝ),
          baseI t * (ENNReal.ofReal t) ^ (p - q - 1) := hscale
    _ = (ENNReal.ofReal (p - q))⁻¹ *
        (ENNReal.ofReal (2 : ℝ)) ^ (p - q) *
          ∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ := by
      rw [hbase_tail]
      ac_rfl

private theorem ofReal_rpow_weight_q {q p t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) =
      (ENNReal.ofReal (2 : ℝ)) ^ q *
        ((ENNReal.ofReal (t / 2)) ^ q *
          ENNReal.ofReal (t ^ (p - q - 1))) := by
  have hreal : t ^ (p - 1) =
      2 ^ q * ((t / 2) ^ q * t ^ (p - q - 1)) := by
    calc
      t ^ (p - 1) = t ^ q * t ^ (p - q - 1) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      _ = (2 * (t / 2)) ^ q * t ^ (p - q - 1) := by
        congr 2
        ring
      _ = 2 ^ q * ((t / 2) ^ q * t ^ (p - q - 1)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        ring
  calc
    ENNReal.ofReal (t ^ (p - 1)) =
        ENNReal.ofReal (2 ^ q * ((t / 2) ^ q * t ^ (p - q - 1))) :=
      congrArg ENNReal.ofReal hreal
    _ = (ENNReal.ofReal (2 : ℝ)) ^ q *
        ((ENNReal.ofReal (t / 2)) ^ q *
          ENNReal.ofReal (t ^ (p - q - 1))) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [← ENNReal.ofReal_rpow_of_pos (by positivity : 0 < t / 2)]

private theorem direct_weak_q_weighted
    {q p t : ℝ} {m C I : ENNReal} (ht : 0 < t)
    (h : (ENNReal.ofReal (t / 2)) ^ q * m ≤ C * I) :
    m * ENNReal.ofReal (t ^ (p - 1)) ≤
      (ENNReal.ofReal (2 : ℝ)) ^ q * C * I *
        ENNReal.ofReal (t ^ (p - q - 1)) := by
  rw [ofReal_rpow_weight_q ht]
  calc
    m * ((ENNReal.ofReal (2 : ℝ)) ^ q *
        ((ENNReal.ofReal (t / 2)) ^ q *
          ENNReal.ofReal (t ^ (p - q - 1)))) =
        ((ENNReal.ofReal (t / 2)) ^ q * m) *
          ((ENNReal.ofReal (2 : ℝ)) ^ q *
            ENNReal.ofReal (t ^ (p - q - 1))) := by ac_rfl
    _ ≤ (C * I) * ((ENNReal.ofReal (2 : ℝ)) ^ q *
          ENNReal.ofReal (t ^ (p - q - 1))) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = (ENNReal.ofReal (2 : ℝ)) ^ q * C * I *
          ENNReal.ofReal (t ^ (p - q - 1)) := by ac_rfl

/-- The weak `(q,q)`--`L∞` Marcinkiewicz step with a supplied additive
amplitude split.  This form applies directly to operators whose domain is a
stable test-function class, such as Schwartz maps. -/
private theorem marcinkiewicz_weak_q_top_on_additive_split
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (q : ℝ) (hq : 0 < q) (Cq : ENNReal)
    (hweak_q : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      (ENNReal.ofReal s) ^ q * μ {x | s < T g x} ≤
        Cq * (∫⁻ x, (ENNReal.ofReal ‖eval g x‖) ^ q ∂μ))
    (hT_top : ∀ (g : F), g ∈ D → ∀ (a : ℝ), 0 ≤ a →
      (∀ x, ‖eval g x‖ ≤ a) → ∀ x, T g x ≤ a)
    {p : ℝ} (hqp : q < p)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlow_norm : ∀ t, 0 < t → ∀ x, ‖eval (low t) x‖ ≤ t / 2)
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ))
    (Aq : ENNReal)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ) *
          (ENNReal.ofReal t) ^ (p - q - 1)) ≤ Aq) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p * ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq * Aq) := by
  let highI : ℝ → ENNReal := fun t =>
    ∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ
  let w : ℝ → ENNReal := fun t => ENNReal.ofReal (t ^ (p - 1))
  let whigh : ℝ → ENNReal := fun t =>
    (ENNReal.ofReal t) ^ (p - q - 1)
  have hp : 0 < p := hq.trans hqp
  have hlow_bound (t : ℝ) (ht : 0 < t) (x : α) :
      T (low t) x ≤ t / 2 := by
    apply hT_top (low t) (hlow_mem t) (t / 2) (by positivity)
    exact hlow_norm t ht
  have hdistribution (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} ≤ μ {x | t / 2 < T (high t) x} := by
    apply measure_mono
    intro x hx
    rw [hsplit t] at hx
    have hsum := hT_subadd (hlow_mem t) (hhigh_mem t) x
    have hlow := hlow_bound t ht x
    by_contra h
    have hhigh : T (high t) x ≤ t / 2 := le_of_not_gt h
    have : T (low t + high t) x ≤ t := by
      calc
        T (low t + high t) x ≤ T (low t) x + T (high t) x := hsum
        _ ≤ t / 2 + t / 2 := add_le_add hlow hhigh
        _ = t := by ring
    exact (not_lt_of_ge this) hx
  have hhigh_endpoint (t : ℝ) (ht : 0 < t) :
      (ENNReal.ofReal (t / 2)) ^ q * μ {x | t / 2 < T (high t) x} ≤
        Cq * highI t := by
    simpa only [highI] using hweak_q (high t) (hhigh_mem t) (by positivity)
  have hdistribution_weight (t : ℝ) (ht : 0 < t) :
      μ {x | t < T f x} * w t ≤
        (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t := by
    dsimp only [w, whigh]
    calc
      μ {x | t < T f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
          μ {x | t / 2 < T (high t) x} * ENNReal.ofReal (t ^ (p - 1)) :=
        mul_le_mul_of_nonneg_right (hdistribution t ht) (by simp)
      _ ≤ (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t *
          ENNReal.ofReal (t ^ (p - q - 1)) := by
        exact direct_weak_q_weighted ht (hhigh_endpoint t ht)
      _ = (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t *
          (ENNReal.ofReal t) ^ (p - q - 1) := by
        rw [ENNReal.ofReal_rpow_of_pos ht]
  have hdistribution_integral :
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) ≤
        ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hdistribution_weight t ht
  have hhigh_tail' :
      (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) ≤ Aq := by
    simpa only [highI, whigh] using hhigh_tail
  have hhigh_integral :
      (∫⁻ t in Ioi (0 : ℝ),
        (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t) ≤
          (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * Aq := by
    calc
      (∫⁻ t in Ioi (0 : ℝ),
        (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t) =
          ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq) *
            (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := by
          have hconst :
              (∫⁻ t in Ioi (0 : ℝ),
                ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq) * (highI t * whigh t)) =
                ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq) *
                  (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) :=
            lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ))) _
              (hhighI_meas.mul
                (ENNReal.continuous_rpow_const.measurable.comp
                  measurable_id.ennreal_ofReal))
          calc
            (∫⁻ t in Ioi (0 : ℝ),
              (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t) =
                ∫⁻ t in Ioi (0 : ℝ),
                  ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq) * (highI t * whigh t) := by
                    apply lintegral_congr
                    intro t
                    ac_rfl
            _ = ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq) *
                (∫⁻ t in Ioi (0 : ℝ), highI t * whigh t) := hconst
      _ ≤ (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * Aq :=
        mul_le_mul_of_nonneg_left hhigh_tail' (by positivity)
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ), μ {x | t < T f x} * w t) := by
      simpa only [w] using
        (lintegral_rpow_eq_lintegral_meas_lt_mul μ
          (Filter.Eventually.of_forall (hT_nonneg f)) hTf hp)
    _ ≤ ENNReal.ofReal p *
        (∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal (2 : ℝ)) ^ q * Cq * highI t * whigh t) :=
      mul_le_mul_right hdistribution_integral _
    _ ≤ ENNReal.ofReal p * ((ENNReal.ofReal (2 : ℝ)) ^ q * Cq * Aq) :=
      mul_le_mul_of_nonneg_left hhigh_integral (by positivity)

private theorem ofReal_q_top_coefficient
    {p q C A : ℝ} (hp : 0 ≤ p) (hA : 0 ≤ A) :
    ENNReal.ofReal p * ((ENNReal.ofReal (2 : ℝ)) ^ q *
        ENNReal.ofReal C * ENNReal.ofReal A) =
      ENNReal.ofReal (p * 2 ^ q * C * A) := by
  have htwoq : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
  calc
    ENNReal.ofReal p * ((ENNReal.ofReal (2 : ℝ)) ^ q *
        ENNReal.ofReal C * ENNReal.ofReal A) =
        ENNReal.ofReal p * (ENNReal.ofReal ((2 : ℝ) ^ q) *
          ENNReal.ofReal (C * A)) := by
          rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
          rw [ENNReal.ofReal_mul' hA]
          ac_rfl
    _ = ENNReal.ofReal p * ENNReal.ofReal ((2 : ℝ) ^ q * (C * A)) := by
      rw [ENNReal.ofReal_mul htwoq]
    _ = ENNReal.ofReal (p * ((2 : ℝ) ^ q * (C * A))) := by
      rw [ENNReal.ofReal_mul hp]
    _ = ENNReal.ofReal (p * 2 ^ q * C * A) := by ring_nf

/-- A real-constant supplied-split weak `(q,q)`--`L∞` interpolation bound.
Its conclusion keeps the coefficient inside `ENNReal.ofReal`, so dyadic
balancing can be done entirely in `ℝ`. -/
theorem marcinkiewicz_weak_q_top_on_additive_split_real
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (q : ℝ) (hq : 0 < q) (Cq : ℝ)
    (hweak_q : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      (ENNReal.ofReal s) ^ q * μ {x | s < T g x} ≤
        ENNReal.ofReal Cq * (∫⁻ x, (ENNReal.ofReal ‖eval g x‖) ^ q ∂μ))
    (hT_top : ∀ (g : F), g ∈ D → ∀ (a : ℝ), 0 ≤ a →
      (∀ x, ‖eval g x‖ ≤ a) → ∀ x, T g x ≤ a)
    {p : ℝ} (hqp : q < p)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlow_norm : ∀ t, 0 < t → ∀ x, ‖eval (low t) x‖ ≤ t / 2)
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ))
    (Aq : ℝ)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ) *
          (ENNReal.ofReal t) ^ (p - q - 1)) ≤ ENNReal.ofReal Aq)
    (hAq : 0 ≤ Aq) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal (p * 2 ^ q * Cq * Aq) := by
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
        ENNReal.ofReal p * ((ENNReal.ofReal (2 : ℝ)) ^ q *
          ENNReal.ofReal Cq * ENNReal.ofReal Aq) :=
      marcinkiewicz_weak_q_top_on_additive_split D eval T hT_nonneg hT_subadd
        q hq (ENNReal.ofReal Cq) hweak_q hT_top hqp f hTf low high hlow_mem hhigh_mem
        hsplit hlow_norm hhighI_meas (ENNReal.ofReal Aq) hhigh_tail
    _ = ENNReal.ofReal (p * 2 ^ q * Cq * Aq) :=
      ofReal_q_top_coefficient (le_of_lt (hq.trans hqp)) hAq

/-- The supplied-split weak `(q,q)`--`L∞` estimate with an explicit
`L∞` constant.  Normalizing the operator by that constant gives the
factor `Ctop ^ (p - q)` in the conclusion. -/
theorem marcinkiewicz_weak_q_top_on_additive_split_real_top_scaled
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (q : ℝ) (hq : 0 < q) (Cq Ctop : ℝ)
    (hCtop : 0 < Ctop)
    (hweak_q : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      (ENNReal.ofReal s) ^ q * μ {x | s < T g x} ≤
        ENNReal.ofReal Cq * (∫⁻ x, (ENNReal.ofReal ‖eval g x‖) ^ q ∂μ))
    (hT_top : ∀ (g : F), g ∈ D → ∀ (a : ℝ), 0 ≤ a →
      (∀ x, ‖eval g x‖ ≤ a) → ∀ x, T g x ≤ Ctop * a)
    {p : ℝ} (hqp : q < p)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlow_norm : ∀ t, 0 < t → ∀ x, ‖eval (low t) x‖ ≤ t / 2)
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ))
    (Aq : ℝ)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, (ENNReal.ofReal ‖eval (high t) x‖) ^ q ∂μ) *
          (ENNReal.ofReal t) ^ (p - q - 1)) ≤ ENNReal.ofReal Aq)
    (hAq : 0 ≤ Aq) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal (p * 2 ^ q * Cq * Aq * Ctop ^ (p - q)) := by
  let S : F → α → ℝ := fun g x => T g x / Ctop
  have hS_nonneg : ∀ g x, 0 ≤ S g x := by
    intro g x
    exact div_nonneg (hT_nonneg g x) hCtop.le
  have hS_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, S (g + h) x ≤ S g x + S h x := by
    intro g h hg hh x
    change T (g + h) x / Ctop ≤ T g x / Ctop + T h x / Ctop
    rw [← add_div]
    exact div_le_div_of_nonneg_right (hT_subadd hg hh x) hCtop.le
  have hlevel (g : F) (s : ℝ) :
      {x | s < S g x} = {x | Ctop * s < T g x} := by
    ext x
    change s < T g x / Ctop ↔ Ctop * s < T g x
    constructor
    · intro hx
      have hx' := (lt_div_iff₀ hCtop).mp hx
      simpa [mul_comm] using hx'
    · intro hx
      apply (lt_div_iff₀ hCtop).mpr
      simpa [mul_comm] using hx
  have hS_weak : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      (ENNReal.ofReal s) ^ q * μ {x | s < S g x} ≤
        ENNReal.ofReal (Cq / Ctop ^ q) *
          (∫⁻ x, (ENNReal.ofReal ‖eval g x‖) ^ q ∂μ) := by
    intro g hg s hs
    have hbase := hweak_q g hg (mul_pos hCtop hs)
    rw [← hlevel g s] at hbase
    let b : ENNReal := ENNReal.ofReal Ctop
    let v : ENNReal := (ENNReal.ofReal s) ^ q
    let m : ENNReal := μ {x | s < S g x}
    let I : ENNReal := ∫⁻ x, (ENNReal.ofReal ‖eval g x‖) ^ q ∂μ
    have hb0 : b ^ q ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hCtop)
      ENNReal.ofReal_ne_top).ne'
    have hbtop : b ^ q ≠ ⊤ := by
      rw [ENNReal.ofReal_rpow_of_pos hCtop]
      exact ENNReal.ofReal_ne_top
    have hbase' : (b ^ q * v) * m ≤ ENNReal.ofReal Cq * I := by
      rw [ENNReal.ofReal_mul hCtop.le,
        ENNReal.mul_rpow_of_nonneg _ _ hq.le] at hbase
      simpa only [b, v, m, I] using hbase
    have hmain : v * m ≤ (b ^ q)⁻¹ * ENNReal.ofReal Cq * I := by
      calc
        v * m = ((b ^ q)⁻¹ * b ^ q) * (v * m) := by
          rw [ENNReal.inv_mul_cancel hb0 hbtop, one_mul]
        _ = (b ^ q)⁻¹ * ((b ^ q * v) * m) := by ac_rfl
        _ ≤ (b ^ q)⁻¹ * (ENNReal.ofReal Cq * I) :=
          mul_le_mul_of_nonneg_left hbase' (by positivity)
        _ = (b ^ q)⁻¹ * ENNReal.ofReal Cq * I := by ac_rfl
    change v * m ≤ ENNReal.ofReal (Cq / Ctop ^ q) * I
    rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hCtop _)]
    rw [← ENNReal.ofReal_rpow_of_pos hCtop]
    rw [div_eq_mul_inv]
    simpa [mul_comm] using hmain
  have hS_top : ∀ (g : F), g ∈ D → ∀ (a : ℝ), 0 ≤ a →
      (∀ x, ‖eval g x‖ ≤ a) → ∀ x, S g x ≤ a := by
    intro g hg a ha hnorm x
    change T g x / Ctop ≤ a
    rw [div_le_iff₀ hCtop]
    simpa [mul_comm] using hT_top g hg a ha hnorm x
  have hS_meas : AEMeasurable (S f) μ := by
    change AEMeasurable (fun x => T f x / Ctop) μ
    exact hTf.div_const Ctop
  have hSbound := marcinkiewicz_weak_q_top_on_additive_split_real D eval S
    hS_nonneg hS_subadd q hq (Cq / Ctop ^ q) hS_weak hS_top hqp f hS_meas low high
    hlow_mem hhigh_mem hsplit hlow_norm hhighI_meas Aq hhigh_tail hAq
  have hp : 0 < p := hq.trans hqp
  have hTS (x : α) : T f x = Ctop * S f x := by
    change T f x = Ctop * (T f x / Ctop)
    field_simp
  have hpoint (x : α) :
      ENNReal.ofReal ((T f x) ^ p) =
        (ENNReal.ofReal Ctop) ^ p * ENNReal.ofReal ((S f x) ^ p) := by
    rw [hTS x, Real.mul_rpow hCtop.le (hS_nonneg f x),
      ENNReal.ofReal_mul (Real.rpow_nonneg hCtop.le _),
      ← ENNReal.ofReal_rpow_of_pos hCtop]
  have hscale :
      (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        (ENNReal.ofReal Ctop) ^ p *
          (∫⁻ x, ENNReal.ofReal ((S f x) ^ p) ∂μ) := by
    calc
      (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
          ∫⁻ x, (ENNReal.ofReal Ctop) ^ p * ENNReal.ofReal ((S f x) ^ p) ∂μ := by
            apply lintegral_congr
            intro x
            exact hpoint x
      _ = (ENNReal.ofReal Ctop) ^ p *
          (∫⁻ x, ENNReal.ofReal ((S f x) ^ p) ∂μ) :=
            lintegral_const_mul' _ _
              (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
  have hreal : Ctop ^ p *
      (p * 2 ^ q * (Cq / Ctop ^ q) * Aq) =
        p * 2 ^ q * Cq * Aq * Ctop ^ (p - q) := by
    rw [Real.rpow_sub hCtop p q]
    field_simp
  calc
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) =
        (ENNReal.ofReal Ctop) ^ p *
          (∫⁻ x, ENNReal.ofReal ((S f x) ^ p) ∂μ) := hscale
    _ ≤ (ENNReal.ofReal Ctop) ^ p *
        ENNReal.ofReal (p * 2 ^ q * (Cq / Ctop ^ q) * Aq) :=
      mul_le_mul_of_nonneg_left hSbound (by positivity)
    _ = ENNReal.ofReal (p * 2 ^ q * Cq * Aq * Ctop ^ (p - q)) := by
      rw [ENNReal.ofReal_rpow_of_pos hCtop,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hCtop.le _)]
      exact congrArg ENNReal.ofReal hreal

/-! The following scaled form is the version used when the threshold in a
Calderón--Zygmund decomposition is chosen independently of the distribution
parameter.  It simply applies the preceding weak-endpoint interpolation
argument to the actual split at `s * t`, and records the resulting change of
variables in the two displayed tails. -/
theorem marcinkiewicz_weak_one_two_on_additive_split_scaled
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [Add F] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} [SFinite μ]
    (D : Set F) (eval : F → α → E) (T : F → α → ℝ)
    (hT_nonneg : ∀ g x, 0 ≤ T g x)
    (hT_subadd : ∀ ⦃g h : F⦄, g ∈ D → h ∈ D →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (C₁ C₂ : ENNReal)
    (hweak_one : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal s * μ {x | s < T g x} ≤
        C₁ * (∫⁻ x, ENNReal.ofReal ‖eval g x‖ ∂μ))
    (hweak_two : ∀ (g : F), g ∈ D → ∀ {s : ℝ}, 0 < s →
      ENNReal.ofReal (s ^ (2 : ℕ)) * μ {x | s < T g x} ≤
        C₂ * (∫⁻ x, ENNReal.ofReal (‖eval g x‖ ^ (2 : ℕ)) ∂μ))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : F) (hTf : AEMeasurable (T f) μ)
    (low high : ℝ → F)
    (hlow_mem : ∀ t, low t ∈ D) (hhigh_mem : ∀ t, high t ∈ D)
    (hsplit : ∀ t, f = low t + high t)
    (hlowI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ))
    (hhighI_meas : Measurable (fun t : ℝ =>
      ∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ))
    (A₂ A₁ : ENNReal)
    (hlow_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low t) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) ≤ A₂)
    (hhigh_tail :
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high t) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) ≤ A₁)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ x, ENNReal.ofReal ((T f x) ^ p) ∂μ) ≤
      ENNReal.ofReal p *
        (4 * C₂ * ((ENNReal.ofReal s) ^ (2 - p) * A₂) +
          2 * C₁ * ((ENNReal.ofReal s) ^ (1 - p) * A₁)) := by
  apply marcinkiewicz_weak_one_two_on_additive_split D eval T hT_nonneg hT_subadd C₁ C₂
    hweak_one hweak_two hp1 hp2 f hTf (fun t => low (s * t)) (fun t => high (s * t))
    ?_ ?_ ?_ ?_ ?_ ((ENNReal.ofReal s) ^ (2 - p) * A₂)
    ((ENNReal.ofReal s) ^ (1 - p) * A₁) ?_ ?_
  · intro t
    exact hlow_mem (s * t)
  · intro t
    exact hhigh_mem (s * t)
  · intro t
    exact hsplit (s * t)
  · change Measurable ((fun r : ℝ =>
        ∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ) ∘
        fun t : ℝ => s * t)
    exact hlowI_meas.comp (measurable_const_mul s)
  · change Measurable ((fun r : ℝ =>
        ∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ) ∘ fun t : ℝ => s * t)
    exact hhighI_meas.comp (measurable_const_mul s)
  · calc
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal (‖eval (low (s * t)) x‖ ^ (2 : ℕ)) ∂μ) *
          (ENNReal.ofReal t) ^ (p - 3)) =
          (ENNReal.ofReal s) ^ (2 - p) *
            (∫⁻ r in Ioi (0 : ℝ),
              (∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ) *
                (ENNReal.ofReal r) ^ (p - 3)) :=
        lintegral_Ioi_comp_mul_low_weight
          (fun r => ∫⁻ x, ENNReal.ofReal (‖eval (low r) x‖ ^ (2 : ℕ)) ∂μ)
          hlowI_meas s hs p
      _ ≤ (ENNReal.ofReal s) ^ (2 - p) * A₂ := by
        exact mul_le_mul_right hlow_tail _
  · calc
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x, ENNReal.ofReal ‖eval (high (s * t)) x‖ ∂μ) *
          (ENNReal.ofReal t) ^ (p - 2)) =
          (ENNReal.ofReal s) ^ (1 - p) *
            (∫⁻ r in Ioi (0 : ℝ),
              (∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ) *
                (ENNReal.ofReal r) ^ (p - 2)) :=
        lintegral_Ioi_comp_mul_high_weight
          (fun r => ∫⁻ x, ENNReal.ofReal ‖eval (high r) x‖ ∂μ)
          hhighI_meas s hs p
      _ ≤ (ENNReal.ofReal s) ^ (1 - p) * A₁ := by
        exact mul_le_mul_right hhigh_tail _

/-!
# Summing geometrically decaying dyadic `Lᵖ` pieces

The theorem below is the literal finite partial-sum step used after obtaining
geometrically decaying `Lᵖ` bounds for dyadic pieces.  It combines Minkowski's
inequality with the geometric-series identity in `ℝ≥0∞`; it does not assume an
operator interface or claim convergence of a function series.
-/

/-- If the `Lᵖ` norm of the `n`th piece is at most `C * ρ^n`, then every
finite dyadic partial sum has `Lᵖ` norm at most `C / (1 - ρ)`. -/
theorem eLpNorm_sum_range_le_geometric
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (p : ℝ≥0∞) (hp : 1 ≤ p) (f : ℕ → α → E)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (C ρ : ℝ≥0∞)
    (hpiece : ∀ n, eLpNorm (f n) p μ ≤ C * ρ ^ n) (N : ℕ) :
    eLpNorm (fun x => ∑ n ∈ Finset.range N, f n x) p μ ≤ C * (1 - ρ)⁻¹ := by
  calc
    eLpNorm (fun x => ∑ n ∈ Finset.range N, f n x) p μ
        = eLpNorm (∑ n ∈ Finset.range N, f n) p μ := by
          apply eLpNorm_congr_ae
          filter_upwards with x
          simp
    _ ≤ ∑ n ∈ Finset.range N, eLpNorm (f n) p μ :=
      eLpNorm_sum_le (f := f) (s := Finset.range N) (fun n _ => hf n) hp
    _ ≤ ∑ n ∈ Finset.range N, C * ρ ^ n := by
      exact Finset.sum_le_sum fun n _ => hpiece n
    _ = C * ∑ n ∈ Finset.range N, ρ ^ n := by
      rw [Finset.mul_sum]
    _ ≤ C * ∑' n : ℕ, ρ ^ n := by
      exact mul_le_mul_right (ENNReal.sum_le_tsum (Finset.range N)) C
    _ = C * (1 - ρ)⁻¹ := congrArg (C * ·) (ENNReal.tsum_geometric ρ)

end LeanSpherical.HarmonicAnalysis
