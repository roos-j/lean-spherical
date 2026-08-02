import LeanSpherical.HarmonicAnalysis.PowerWeights.RelativeMovingSelectorComparison

/-!
# Palette comparison for entropy representatives

At one normalized radius block, the representatives produced independently
in each physical block are already indexed by the common palette `Fin N`.
Keeping that palette (instead of turning it back into an auxiliary finite
set) is what lets the global argument place each colour in one lacunary
selector.
-/

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory FourierTransform Metric Set intervalIntegral
open scoped BigOperators BoundedContinuousFunction ENNReal FourierTransform NNReal

noncomputable section

private theorem ennreal_ofReal_norm_sq_le_two_center_add_eight_variation
    {X : Type*} (F : ℝ → X → ℂ) {a b r s : ℝ} (hr : r ∈ Icc a b)
    (hs : s ∈ Icc a b) (x : X) :
    ENNReal.ofReal (‖F r x‖ ^ 2) ≤
      2 * ENNReal.ofReal (‖F s x‖ ^ 2) +
        8 * ⨆ t : Icc a b, ENNReal.ofReal (‖F t.1 x - F a x‖ ^ 2) := by
  let V : ENNReal :=
    ⨆ t : Icc a b, ENNReal.ofReal (‖F t.1 x - F a x‖ ^ 2)
  have hVr : ENNReal.ofReal (‖F r x - F a x‖ ^ 2) ≤ V :=
    le_iSup (fun t : Icc a b => ENNReal.ofReal (‖F t.1 x - F a x‖ ^ 2))
      ⟨r, hr⟩
  have hVs : ENNReal.ofReal (‖F s x - F a x‖ ^ 2) ≤ V :=
    le_iSup (fun t : Icc a b => ENNReal.ofReal (‖F t.1 x - F a x‖ ^ 2))
      ⟨s, hs⟩
  have hdiff : ENNReal.ofReal (‖F r x - F s x‖ ^ 2) ≤ 4 * V := by
    have htriangle : ‖F r x - F s x‖ ≤ ‖F r x - F a x‖ + ‖F s x - F a x‖ := by
      rw [show F r x - F s x = (F r x - F a x) - (F s x - F a x) by ring]
      exact norm_sub_le _ _
    have hsq : ‖F r x - F s x‖ ^ 2 ≤
        2 * ‖F r x - F a x‖ ^ 2 + 2 * ‖F s x - F a x‖ ^ 2 := by
      have hsquare : ‖F r x - F s x‖ ^ 2 ≤
          (‖F r x - F a x‖ + ‖F s x - F a x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htriangle
      nlinarith [sq_nonneg (‖F r x - F a x‖ - ‖F s x - F a x‖)]
    calc
      ENNReal.ofReal (‖F r x - F s x‖ ^ 2) ≤
          ENNReal.ofReal
            (2 * ‖F r x - F a x‖ ^ 2 + 2 * ‖F s x - F a x‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hsq
      _ = 2 * ENNReal.ofReal (‖F r x - F a x‖ ^ 2) +
          2 * ENNReal.ofReal (‖F s x - F a x‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ 2 * V + 2 * V := add_le_add
        (by simpa only [mul_comm] using mul_le_mul_left hVr 2)
        (by simpa only [mul_comm] using mul_le_mul_left hVs 2)
      _ = 4 * V := by ring
  calc
    ENNReal.ofReal (‖F r x‖ ^ 2) =
        ENNReal.ofReal (‖(F r x - F s x) + F s x‖ ^ 2) := by ring_nf
    _ ≤ 2 * ENNReal.ofReal (‖F r x - F s x‖ ^ 2) +
        2 * ENNReal.ofReal (‖F s x‖ ^ 2) := by
      have htriangle : ‖(F r x - F s x) + F s x‖ ≤
          ‖F r x - F s x‖ + ‖F s x‖ := norm_add_le _ _
      have hsq : ‖(F r x - F s x) + F s x‖ ^ 2 ≤
          2 * ‖F r x - F s x‖ ^ 2 + 2 * ‖F s x‖ ^ 2 := by
        have hsquare : ‖(F r x - F s x) + F s x‖ ^ 2 ≤
            (‖F r x - F s x‖ + ‖F s x‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _)
            (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htriangle
        nlinarith [sq_nonneg (‖F r x - F s x‖ - ‖F s x‖)]
      calc
        ENNReal.ofReal (‖(F r x - F s x) + F s x‖ ^ 2) ≤
            ENNReal.ofReal (2 * ‖F r x - F s x‖ ^ 2 + 2 * ‖F s x‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hsq
        _ = 2 * ENNReal.ofReal (‖F r x - F s x‖ ^ 2) +
            2 * ENNReal.ofReal (‖F s x‖ ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    _ ≤ 2 * (4 * V) + 2 * ENNReal.ofReal (‖F s x‖ ^ 2) :=
      add_le_add (by simpa only [mul_comm] using mul_le_mul_left hdiff 2) le_rfl
    _ = 2 * ENNReal.ofReal (‖F s x‖ ^ 2) + 8 * V := by ring
    _ = 2 * ENNReal.ofReal (‖F s x‖ ^ 2) +
        8 * ⨆ t : Icc a b, ENNReal.ofReal (‖F t.1 x - F a x‖ ^ 2) := by
      rfl

/-- A palette of centres controls the square maximal envelope on a normalized
radius block.  A centre need only lie in `[1,2]`; the cover condition singles
out the colours which are actual radii of the block. -/
theorem iSup_ennreal_norm_sq_le_palette_selector_add_cell_variation
    {X : Type*} (F : ℝ → X → ℂ) (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2)
    (δ : ℝ≥0) (N : ℕ) (c : Fin N → PositiveRadius)
    (hc : ∀ i, (c i : ℝ) ∈ Icc (1 : ℝ) 2)
    (hcover : ∀ r : PositiveRadius, (r : ℝ) ∈ E → ∃ i : Fin N,
      |logRadius r - logRadius (c i)| ≤ (δ : ℝ)) (x : X) :
    (⨆ r : ↥(E ∩ Ioi (0 : ℝ)), ENNReal.ofReal (‖F r.1 x‖ ^ 2)) ≤
      2 * (⨆ i : Fin N, ENNReal.ofReal (‖F (c i : ℝ) x‖ ^ 2)) +
        8 * ∑ i : Fin N,
          ⨆ t : Icc (unitScaleEntropyCell δ (c i)).1
              (unitScaleEntropyCell δ (c i)).2,
            ENNReal.ofReal
              (‖F t.1 x - F (unitScaleEntropyCell δ (c i)).1 x‖ ^ 2) := by
  classical
  apply iSup_le
  intro r
  let rpos : PositiveRadius := ⟨r.1, r.2.2⟩
  have hrE : (rpos : ℝ) ∈ E := r.2.1
  have hrblock : (rpos : ℝ) ∈ Icc (1 : ℝ) 2 := hE hrE
  obtain ⟨i, hri⟩ := hcover rpos hrE
  have hicell : (c i : ℝ) ∈
      Icc (unitScaleEntropyCell δ (c i)).1 (unitScaleEntropyCell δ (c i)).2 :=
    mem_unitScaleEntropyCell_center δ (c i) (hc i)
  have hrcell : (rpos : ℝ) ∈
      Icc (unitScaleEntropyCell δ (c i)).1 (unitScaleEntropyCell δ (c i)).2 :=
    mem_unitScaleEntropyCell_of_logRadius_close δ rpos (c i) hrblock (hc i) hri
  have hsingle := ennreal_ofReal_norm_sq_le_two_center_add_eight_variation
    F (a := (unitScaleEntropyCell δ (c i)).1)
      (b := (unitScaleEntropyCell δ (c i)).2)
      (r := (rpos : ℝ)) (s := (c i : ℝ)) hrcell hicell x
  have hselector : ENNReal.ofReal (‖F (c i : ℝ) x‖ ^ 2) ≤
      ⨆ z : Fin N, ENNReal.ofReal (‖F (c z : ℝ) x‖ ^ 2) :=
    le_iSup (fun z : Fin N => ENNReal.ofReal (‖F (c z : ℝ) x‖ ^ 2)) i
  have hvariation :
      (⨆ t : Icc (unitScaleEntropyCell δ (c i)).1
          (unitScaleEntropyCell δ (c i)).2,
        ENNReal.ofReal
          (‖F t.1 x - F (unitScaleEntropyCell δ (c i)).1 x‖ ^ 2)) ≤
        ∑ z : Fin N,
          ⨆ t : Icc (unitScaleEntropyCell δ (c z)).1
              (unitScaleEntropyCell δ (c z)).2,
            ENNReal.ofReal
              (‖F t.1 x - F (unitScaleEntropyCell δ (c z)).1 x‖ ^ 2) := by
    exact Finset.single_le_sum (s := Finset.univ) (f := fun z =>
      ⨆ t : Icc (unitScaleEntropyCell δ (c z)).1
          (unitScaleEntropyCell δ (c z)).2,
        ENNReal.ofReal
          (‖F t.1 x - F (unitScaleEntropyCell δ (c z)).1 x‖ ^ 2))
      (fun _ _ => bot_le) (Finset.mem_univ i)
  change ENNReal.ofReal (‖F (rpos : ℝ) x‖ ^ 2) ≤ _
  exact hsingle.trans (add_le_add
    (by simpa only [mul_comm] using mul_le_mul_left hselector 2)
    (by simpa only [mul_comm] using mul_le_mul_left hvariation 8))

/-- The variation portion of the palette comparison has the same sharp
short-cell square bound, summed over palette colours. -/
theorem lintegral_palette_entropy_cell_variation_of_sharp
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
    (hphi_norm : ∀ xi, ‖phi xi‖ ≤ 1) (j : Nat)
    (δ : ℝ≥0) (N : ℕ) (c : Fin N → PositiveRadius)
    (hc : ∀ i, (c i : ℝ) ∈ Icc (1 : ℝ) 2) :
    let F : ℝ → Euclidean (d + 1) → ℂ := fun s x =>
      𝓕⁻ (fun xi : Euclidean (d + 1) =>
        surfaceFourier (d + 1) (-s • xi) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (s • xi)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (s • xi))) *
          𝓕 (f : Euclidean (d + 1) → ℂ) xi) x
    let C : ℝ := 2 *
      ((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
        (12 * C0 *
          ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ)
            phi).toBoundedContinuousFunction‖) /
          (dyadicScale j) ^ ((d : ℝ) / 2))
    let J : ℝ := ∫ xi : Euclidean (d + 1), ‖𝓕 (f : Euclidean (d + 1) → ℂ) xi‖ ^ 2
    (∫⁻ x : Euclidean (d + 1), ∑ i : Fin N,
      ⨆ t : Icc (unitScaleEntropyCell δ (c i)).1
          (unitScaleEntropyCell δ (c i)).2,
        ENNReal.ofReal
          (‖F t.1 x - F (unitScaleEntropyCell δ (c i)).1 x‖ ^ 2)) ≤
      ∑ i : Fin N, ENNReal.ofReal
        (2 * ((unitScaleEntropyCell δ (c i)).2 -
          (unitScaleEntropyCell δ (c i)).1) ^ 2 * C ^ 2 * J) := by
  dsimp only
  let F : ℝ → Euclidean (d + 1) → ℂ := fun s x =>
    𝓕⁻ (fun xi : Euclidean (d + 1) =>
      surfaceFourier (d + 1) (-s • xi) *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (s • xi)) -
          phi (((2 : ℝ) ^ j)⁻¹ • (s • xi))) *
        𝓕 (f : Euclidean (d + 1) → ℂ) xi) x
  let C : ℝ := 2 *
    ((4 * C1) / (dyadicScale j) ^ ((d : ℝ) / 2 - 1) +
      (12 * C0 *
        ‖((SchwartzMap.fderivCLM ℂ (Euclidean (d + 1)) ℂ)
          phi).toBoundedContinuousFunction‖) /
        (dyadicScale j) ^ ((d : ℝ) / 2))
  let J : ℝ := ∫ xi : Euclidean (d + 1),
    ‖𝓕 (f : Euclidean (d + 1) → ℂ) xi‖ ^ 2
  have hmeas (i : Fin N) :
      Measurable (fun x : Euclidean (d + 1) =>
        ⨆ t : Icc (unitScaleEntropyCell δ (c i)).1
            (unitScaleEntropyCell δ (c i)).2,
          ENNReal.ofReal
            (‖F t.1 x - F (unitScaleEntropyCell δ (c i)).1 x‖ ^ 2)) := by
    have hcenter := mem_unitScaleEntropyCell_center δ (c i) (hc i)
    have hends := unitScaleEntropyCell_endpoints_mem δ (c i) (hc i)
    have hlocal :=
      measurable_and_lintegral_iSup_literal_relative_dyadic_moving_bandpass_interval_sub_left_of_sharp
        hd C0 C1 hC0 hC1 hdecay hderiv phi f hphi_one hphi_zero hphi_norm j
        (hcenter.1.trans hcenter.2) hends.1.1 hends.2.2
    simpa only [F] using hlocal.1
  have hbound (i : Fin N) :
      (∫⁻ x : Euclidean (d + 1),
        ⨆ t : Icc (unitScaleEntropyCell δ (c i)).1
            (unitScaleEntropyCell δ (c i)).2,
          ENNReal.ofReal
            (‖F t.1 x - F (unitScaleEntropyCell δ (c i)).1 x‖ ^ 2)) ≤
        ENNReal.ofReal
          (2 * ((unitScaleEntropyCell δ (c i)).2 -
            (unitScaleEntropyCell δ (c i)).1) ^ 2 * C ^ 2 * J) := by
    have hcenter := mem_unitScaleEntropyCell_center δ (c i) (hc i)
    have hends := unitScaleEntropyCell_endpoints_mem δ (c i) (hc i)
    have hlocal :=
      measurable_and_lintegral_iSup_literal_relative_dyadic_moving_bandpass_interval_sub_left_of_sharp
        hd C0 C1 hC0 hC1 hdecay hderiv phi f hphi_one hphi_zero hphi_norm j
        (hcenter.1.trans hcenter.2) hends.1.1 hends.2.2
    simpa only [F, C, J] using hlocal.2
  calc
    (∫⁻ x : Euclidean (d + 1), ∑ i : Fin N,
      ⨆ t : Icc (unitScaleEntropyCell δ (c i)).1
          (unitScaleEntropyCell δ (c i)).2,
        ENNReal.ofReal
          (‖F t.1 x - F (unitScaleEntropyCell δ (c i)).1 x‖ ^ 2)) =
        ∑ i : Fin N, ∫⁻ x : Euclidean (d + 1),
          ⨆ t : Icc (unitScaleEntropyCell δ (c i)).1
              (unitScaleEntropyCell δ (c i)).2,
            ENNReal.ofReal
              (‖F t.1 x - F (unitScaleEntropyCell δ (c i)).1 x‖ ^ 2) := by
          rw [lintegral_finsetSum]
          intro i _
          exact hmeas i
    _ ≤ ∑ i : Fin N, ENNReal.ofReal
        (2 * ((unitScaleEntropyCell δ (c i)).2 -
          (unitScaleEntropyCell δ (c i)).1) ^ 2 * C ^ 2 * J) := by
      exact Finset.sum_le_sum fun i _ => hbound i

/-- The finite-block form of the palette comparison.  Each normalized block
has its own moving family and centres, but the selector term is placed into
one common palette.  This is the exact pointwise reduction used before the
per-colour lacunary estimates. -/
theorem iSup_ennreal_norm_sq_finite_palette_blocks_le
    {X : Type*} (K : Finset ℤ) (E : ℤ → Set ℝ)
    (F : ℤ → ℝ → X → ℂ) (δ : ℝ≥0) (N : ℕ)
    (c : ℤ → Fin N → PositiveRadius) (P : Fin N → X → ENNReal)
    (hE : ∀ k ∈ K, E k ⊆ Icc (1 : ℝ) 2)
    (hc : ∀ k ∈ K, ∀ i, (c k i : ℝ) ∈ Icc (1 : ℝ) 2)
    (hcover : ∀ k ∈ K, ∀ r : PositiveRadius, (r : ℝ) ∈ E k →
      ∃ i : Fin N, |logRadius r - logRadius (c k i)| ≤ (δ : ℝ))
    (hselector : ∀ k ∈ K, ∀ i x,
      ENNReal.ofReal (‖F k (c k i : ℝ) x‖ ^ 2) ≤ P i x) (x : X) :
    (⨆ k : {k // k ∈ K},
      ⨆ r : ↥(E k.1 ∩ Ioi (0 : ℝ)), ENNReal.ofReal (‖F k.1 r.1 x‖ ^ 2)) ≤
      2 * (⨆ i : Fin N, P i x) +
        8 * ∑ k ∈ K, ∑ i : Fin N,
          ⨆ t : Icc (unitScaleEntropyCell δ (c k i)).1
              (unitScaleEntropyCell δ (c k i)).2,
            ENNReal.ofReal
              (‖F k t.1 x - F k (unitScaleEntropyCell δ (c k i)).1 x‖ ^ 2) := by
  classical
  apply iSup_le
  intro k
  apply iSup_le
  intro r
  have hlocal := iSup_ennreal_norm_sq_le_palette_selector_add_cell_variation
    (F k.1) (E k.1) (hE k.1 k.2) δ N (c k.1) (hc k.1 k.2)
    (hcover k.1 k.2) x
  have hleft : ENNReal.ofReal (‖F k.1 r.1 x‖ ^ 2) ≤
      2 * (⨆ i : Fin N, ENNReal.ofReal (‖F k.1 (c k.1 i : ℝ) x‖ ^ 2)) +
        8 * ∑ i : Fin N,
          ⨆ t : Icc (unitScaleEntropyCell δ (c k.1 i)).1
              (unitScaleEntropyCell δ (c k.1 i)).2,
            ENNReal.ofReal
              (‖F k.1 t.1 x -
                F k.1 (unitScaleEntropyCell δ (c k.1 i)).1 x‖ ^ 2) := by
    exact le_trans (le_iSup (fun z : {z // z ∈ E k.1 ∩ Ioi (0 : ℝ)} =>
      ENNReal.ofReal (‖F k.1 z.1 x‖ ^ 2)) r) hlocal
  have hpalette :
      (⨆ i : Fin N, ENNReal.ofReal (‖F k.1 (c k.1 i : ℝ) x‖ ^ 2)) ≤
        ⨆ i : Fin N, P i x := by
    apply iSup_le
    intro i
    exact (hselector k.1 k.2 i x).trans (le_iSup (fun z : Fin N => P z x) i)
  have hvariation :
      (∑ i : Fin N,
        ⨆ t : Icc (unitScaleEntropyCell δ (c k.1 i)).1
            (unitScaleEntropyCell δ (c k.1 i)).2,
          ENNReal.ofReal
            (‖F k.1 t.1 x -
              F k.1 (unitScaleEntropyCell δ (c k.1 i)).1 x‖ ^ 2)) ≤
        ∑ z ∈ K, ∑ i : Fin N,
          ⨆ t : Icc (unitScaleEntropyCell δ (c z i)).1
              (unitScaleEntropyCell δ (c z i)).2,
            ENNReal.ofReal
              (‖F z t.1 x - F z (unitScaleEntropyCell δ (c z i)).1 x‖ ^ 2) := by
    exact Finset.single_le_sum (s := K) (f := fun z =>
      ∑ i : Fin N,
        ⨆ t : Icc (unitScaleEntropyCell δ (c z i)).1
            (unitScaleEntropyCell δ (c z i)).2,
          ENNReal.ofReal
            (‖F z t.1 x - F z (unitScaleEntropyCell δ (c z i)).1 x‖ ^ 2))
      (fun _ _ => bot_le) k.2
  exact hleft.trans (add_le_add
    (by simpa only [mul_comm] using mul_le_mul_left hpalette 2)
    (by simpa only [mul_comm] using mul_le_mul_left hvariation 8))

/-- The distributional form of the palette square comparison.  The selector
term is retained at a literal level set, while the short-cell discrepancy is
paid for by its square integral.  This is the exact finite-block handoff for
any later Calderón--Zygmund estimate of the cell term. -/
private theorem finite_palette_square_distributional_of_le
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (Q S V : X → ENNReal) (a : ENNReal)
    (hV : AEMeasurable V mu)
    (hpoint : ∀ x, Q x ≤ 2 * S x + 8 * V x) :
    (16 * a) * mu {x | 16 * a < Q x} ≤
      16 * (a * mu {x | a < S x}) + 16 * ∫⁻ x, V x ∂mu := by
  let A : Set X := {x | 16 * a < Q x}
  let B : Set X := {x | a < S x}
  let C : Set X := {x | a < V x}
  have hsub : A ⊆ B ∪ C := by
    intro x hx
    by_contra hnot
    have hxB : x ∉ B := by
      intro hxb
      exact hnot (Or.inl hxb)
    have hxC : x ∉ C := by
      intro hxc
      exact hnot (Or.inr hxc)
    have hS : S x ≤ a := le_of_not_gt hxB
    have hVx : V x ≤ a := le_of_not_gt hxC
    have hQ : Q x ≤ 2 * S x + 8 * V x := hpoint x
    have hbound : Q x ≤ 16 * a := by
      calc
        Q x ≤ 2 * S x + 8 * V x := hQ
        _ ≤ 2 * a + 8 * a :=
          add_le_add (mul_le_mul_right hS 2) (mul_le_mul_right hVx 8)
        _ ≤ 16 * a := by
          calc
            2 * a + 8 * a = 10 * a := by ring
            _ ≤ 16 * a := by
              simpa only [mul_comm] using
                mul_le_mul_right (by norm_num : (10 : ENNReal) ≤ 16) a
    exact (not_lt_of_ge hbound) hx
  have hmeasure : mu A ≤ mu B + mu C :=
    (measure_mono hsub).trans (measure_union_le B C)
  have hmarkov : a * mu C ≤ ∫⁻ x, V x ∂mu := by
    calc
      a * mu C ≤ a * mu {x | a ≤ V x} := by
        simpa only [mul_comm] using mul_le_mul_left (measure_mono (by
          intro x hx
          change a < V x at hx
          exact hx.le)) a
      _ ≤ ∫⁻ x, V x ∂mu := mul_meas_ge_le_lintegral₀ hV a
  calc
    (16 * a) * mu A ≤ (16 * a) * (mu B + mu C) :=
      by simpa only [mul_comm] using mul_le_mul_left hmeasure (16 * a)
    _ = 16 * (a * mu B) + 16 * (a * mu C) := by ring
    _ ≤ 16 * (a * mu B) + 16 * ∫⁻ x, V x ∂mu :=
      add_le_add le_rfl
        (by simpa only [mul_comm] using mul_le_mul_left hmarkov 16)

/-- The finite physical-block palette comparison in distributional form.
Unlike the integrated square estimate, this retains the selector level set
and therefore can be combined directly with the shifted lacunary weak-one
endpoint. -/
theorem distributional_iSup_ennreal_norm_sq_finite_palette_blocks_le
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (K : Finset Int) (E : Int → Set Real)
    (F : Int → Real → X → Complex) (delta : NNReal) (N : Nat)
    (c : Int → Fin N → PositiveRadius) (P : Fin N → X → ENNReal)
    (hE : ∀ k ∈ K, E k ⊆ Icc (1 : Real) 2)
    (hc : ∀ k ∈ K, ∀ i, (c k i : Real) ∈ Icc (1 : Real) 2)
    (hcover : ∀ k ∈ K, ∀ r : PositiveRadius, (r : Real) ∈ E k →
      ∃ i : Fin N, |logRadius r - logRadius (c k i)| ≤ (delta : Real))
    (hselector : ∀ k ∈ K, ∀ i x,
      ENNReal.ofReal (‖F k (c k i : Real) x‖ ^ 2) ≤ P i x)
    (hVariationMeas : AEMeasurable (fun x : X =>
      ∑ k ∈ K, ∑ i : Fin N,
        ⨆ t : Icc (unitScaleEntropyCell delta (c k i)).1
            (unitScaleEntropyCell delta (c k i)).2,
          ENNReal.ofReal
            (‖F k t.1 x - F k (unitScaleEntropyCell delta (c k i)).1 x‖ ^ 2)) mu)
    (a : ENNReal) :
    (16 * a) * mu {x |
      16 * a < ⨆ k : {k // k ∈ K},
        ⨆ r : ↥(E k.1 ∩ Ioi (0 : Real)), ENNReal.ofReal (‖F k.1 r.1 x‖ ^ 2)} ≤
      16 * (a * mu {x | a < ⨆ i : Fin N, P i x}) +
        16 * ∫⁻ x,
          ∑ k ∈ K, ∑ i : Fin N,
            ⨆ t : Icc (unitScaleEntropyCell delta (c k i)).1
                (unitScaleEntropyCell delta (c k i)).2,
              ENNReal.ofReal
                (‖F k t.1 x - F k (unitScaleEntropyCell delta (c k i)).1 x‖ ^ 2) ∂mu := by
  let Q : X → ENNReal := fun x =>
    ⨆ k : {k // k ∈ K},
      ⨆ r : ↥(E k.1 ∩ Ioi (0 : Real)), ENNReal.ofReal (‖F k.1 r.1 x‖ ^ 2)
  let S : X → ENNReal := fun x => ⨆ i : Fin N, P i x
  let V : X → ENNReal := fun x =>
    ∑ k ∈ K, ∑ i : Fin N,
      ⨆ t : Icc (unitScaleEntropyCell delta (c k i)).1
          (unitScaleEntropyCell delta (c k i)).2,
        ENNReal.ofReal
          (‖F k t.1 x - F k (unitScaleEntropyCell delta (c k i)).1 x‖ ^ 2)
  have hpoint (x : X) : Q x ≤ 2 * S x + 8 * V x := by
    simpa only [Q, S, V] using
      iSup_ennreal_norm_sq_finite_palette_blocks_le K E F delta N c P
        hE hc hcover hselector x
  simpa only [Q, S, V] using
    finite_palette_square_distributional_of_le mu Q S V a
      (by simpa only [V] using hVariationMeas) hpoint

/-- Integrating the finite-palette comparison.  The selector and variation
terms stay literal, so this can be combined directly with the lacunary
selector estimate and the sharp cell-variation estimate. -/
theorem lintegral_iSup_ennreal_norm_sq_finite_palette_blocks_le
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (K : Finset Int) (E : Int → Set Real)
    (F : Int → Real → X → Complex) (delta : NNReal) (N : Nat)
    (c : Int → Fin N → PositiveRadius) (P : Fin N → X → ENNReal)
    (hE : ∀ k ∈ K, E k ⊆ Icc (1 : Real) 2)
    (hc : ∀ k ∈ K, ∀ i, (c k i : Real) ∈ Icc (1 : Real) 2)
    (hcover : ∀ k ∈ K, ∀ r : PositiveRadius, (r : Real) ∈ E k →
      ∃ i : Fin N, |logRadius r - logRadius (c k i)| ≤ (delta : Real))
    (hselector : ∀ k ∈ K, ∀ i x,
      ENNReal.ofReal (‖F k (c k i : Real) x‖ ^ 2) ≤ P i x)
    (hPaletteMeas : AEStronglyMeasurable (fun x : X => ⨆ i : Fin N, P i x) mu)
    (hVariationMeas : AEStronglyMeasurable (fun x : X =>
      ∑ k ∈ K, ∑ i : Fin N,
        ⨆ t : Icc (unitScaleEntropyCell delta (c k i)).1
            (unitScaleEntropyCell delta (c k i)).2,
          ENNReal.ofReal
            (‖F k t.1 x - F k (unitScaleEntropyCell delta (c k i)).1 x‖ ^ 2)) mu) :
    (∫⁻ x : X,
      ⨆ k : {k // k ∈ K},
        ⨆ r : ↥(E k.1 ∩ Ioi (0 : Real)), ENNReal.ofReal (‖F k.1 r.1 x‖ ^ 2)
      ∂mu) ≤
      2 * (∫⁻ x : X, ⨆ i : Fin N, P i x ∂mu) +
        8 * (∫⁻ x : X,
          ∑ k ∈ K, ∑ i : Fin N,
            ⨆ t : Icc (unitScaleEntropyCell delta (c k i)).1
                (unitScaleEntropyCell delta (c k i)).2,
              ENNReal.ofReal
                (‖F k t.1 x - F k (unitScaleEntropyCell delta (c k i)).1 x‖ ^ 2)
          ∂mu) := by
  let S : X → ENNReal := fun x => ⨆ i : Fin N, P i x
  let V : X → ENNReal := fun x =>
    ∑ k ∈ K, ∑ i : Fin N,
      ⨆ t : Icc (unitScaleEntropyCell delta (c k i)).1
          (unitScaleEntropyCell delta (c k i)).2,
        ENNReal.ofReal
          (‖F k t.1 x - F k (unitScaleEntropyCell delta (c k i)).1 x‖ ^ 2)
  have hSmeas : AEMeasurable S mu := by
    simpa only [S] using hPaletteMeas.aemeasurable
  have hVmeas : AEMeasurable V mu := by
    simpa only [V] using hVariationMeas.aemeasurable
  have hpoint (x : X) :
      (⨆ k : {k // k ∈ K},
        ⨆ r : ↥(E k.1 ∩ Ioi (0 : Real)), ENNReal.ofReal (‖F k.1 r.1 x‖ ^ 2)) ≤
        2 * S x + 8 * V x := by
    simpa only [S, V] using
      iSup_ennreal_norm_sq_finite_palette_blocks_le K E F delta N c P
        hE hc hcover hselector x
  calc
    (∫⁻ x : X,
      ⨆ k : {k // k ∈ K},
        ⨆ r : ↥(E k.1 ∩ Ioi (0 : Real)), ENNReal.ofReal (‖F k.1 r.1 x‖ ^ 2)
      ∂mu) ≤ ∫⁻ x : X, 2 * S x + 8 * V x ∂mu :=
      lintegral_mono hpoint
    _ = (∫⁻ x : X, 2 * S x ∂mu) + ∫⁻ x : X, 8 * V x ∂mu := by
      exact lintegral_add_left' (hSmeas.const_mul 2) _
    _ = 2 * (∫⁻ x : X, S x ∂mu) + 8 * (∫⁻ x : X, V x ∂mu) := by
      rw [lintegral_const_mul' 2 S (by norm_num),
        lintegral_const_mul' 8 V (by norm_num)]
    _ = 2 * (∫⁻ x : X, ⨆ i : Fin N, P i x ∂mu) +
        8 * (∫⁻ x : X,
          ∑ k ∈ K, ∑ i : Fin N,
            ⨆ t : Icc (unitScaleEntropyCell delta (c k i)).1
                (unitScaleEntropyCell delta (c k i)).2,
              ENNReal.ofReal
                (‖F k t.1 x - F k (unitScaleEntropyCell delta (c k i)).1 x‖ ^ 2)
          ∂mu) := by
      rfl

end

end LeanSpherical.HarmonicAnalysis
