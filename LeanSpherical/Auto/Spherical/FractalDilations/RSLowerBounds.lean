/-
Roos--Seeger lower-bound constructions used for Theorem 1.2.
Declaration namespace `Auto.Spherical.FractalDilations.RS` is retained.
-/

import LeanSpherical.Auto.Spherical.FractalDilations.RSUpperBounds

namespace Auto.Spherical.FractalDilations.RS

open MeasureTheory Metric Set
open Auto.Spherical.SurfaceCore
open Auto.Spherical.FractalDilations.AssouadSpectrum
open Auto.Spherical.FractalDilations.Minkowski
open Auto.Spherical.FractalDilations.QuasiAssouadBridge
open Auto.Spherical.FractalDilations.Q4RadialReduction
open Auto.Spherical.FractalDilations.OscillatoryIBP
open Auto.Spherical.FractalDilations.PlanarTripleWaveNormalForm
open Auto.Spherical.FractalDilations.CoordinateWaveSymbolBounds
open Auto.Spherical.FractalDilations.QuadraticStationaryPhase
open Auto.Spherical.FractalDilations.PlanarEndpointAmplitude
open Auto.Spherical.FractalDilations.CoordinateMeridianWaves
open Auto.Spherical.FractalDilations.CoordinateMiddleParameterDerivatives
open Auto.Spherical.FractalDilations.AllDimensionalTripleWaveNormalForm
open Auto.Spherical.FractalDilations.AbsoluteReassembly
open Auto.Spherical.FractalDilations.AbsoluteDyadic
open scoped ENNReal NNReal Real FourierTransform Convolution

noncomputable section
/-! ## Cantor midpoint sets

Section 6 of the paper builds quasi-Assouad regular sets from the *midpoints* of the
generations of a Cantor construction.  Working with these finite point sets keeps every
covering estimate elementary.

`cantorMid μ m u L` is the set of midpoints of the `2 ^ m` intervals of the `m`-th generation of
the Cantor construction with ratio `μ ≤ 1/2` inside the interval `[u, u + L]`. -/

/-- The midpoints of the `m`-th generation of the Cantor construction of ratio `mu` in
`[u, u + L]`. -/
def cantorMid (mu : ℝ) : ℕ → ℝ → ℝ → Finset ℝ
  | 0, u, L => {u + L / 2}
  | (m + 1), u, L =>
      cantorMid mu m u (mu * L) ∪ cantorMid mu m (u + (1 - mu) * L) (mu * L)

theorem cantorMid_zero (mu u L : ℝ) : cantorMid mu 0 u L = {u + L / 2} := rfl

theorem cantorMid_succ (mu : ℝ) (m : ℕ) (u L : ℝ) :
    cantorMid mu (m + 1) u L =
      cantorMid mu m u (mu * L) ∪ cantorMid mu m (u + (1 - mu) * L) (mu * L) := rfl

theorem cantorMid_nonempty (mu : ℝ) (m : ℕ) (u L : ℝ) : (cantorMid mu m u L).Nonempty := by
  induction m generalizing u L with
  | zero => exact ⟨u + L / 2, by simp [cantorMid_zero]⟩
  | succ m ih =>
      obtain ⟨x, hx⟩ := ih u (mu * L)
      exact ⟨x, by rw [cantorMid_succ]; exact Finset.mem_union_left _ hx⟩

/-- Every point of the midpoint set lies well inside `[u, u + L]`. -/
theorem cantorMid_mem_bounds {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2)
    (m : ℕ) {u L : ℝ} (hL : 0 ≤ L) {x : ℝ} (hx : x ∈ cantorMid mu m u L) :
    u + mu ^ m * L / 2 ≤ x ∧ x ≤ u + L - mu ^ m * L / 2 := by
  induction m generalizing u L with
  | zero =>
      rw [cantorMid_zero, Finset.mem_singleton] at hx
      subst hx
      refine ⟨by simp, ?_⟩
      simp
      linarith
  | succ m ih =>
      rw [cantorMid_succ, Finset.mem_union] at hx
      have hmuL : 0 ≤ mu * L := mul_nonneg hmu.le hL
      have hpow : 0 ≤ mu ^ m := le_of_lt (pow_pos hmu m)
      have hpowsucc : 0 ≤ mu ^ (m + 1) := le_of_lt (pow_pos hmu (m + 1))
      have hpowmul : mu ^ m * (mu * L) = mu ^ (m + 1) * L := by ring
      rcases hx with hx | hx
      · obtain ⟨h1, h2⟩ := ih hmuL hx
        rw [hpowmul] at h1 h2
        constructor
        · linarith
        · have hmuLle : mu * L ≤ L := by nlinarith [hL, hmu2]
          linarith
      · obtain ⟨h1, h2⟩ := ih hmuL hx
        rw [hpowmul] at h1 h2
        have hone : 0 ≤ (1 - mu) * L := mul_nonneg (by linarith) hL
        constructor
        · linarith
        · linarith

/-- Distinct points of the midpoint set are separated by at least the length of the generation
intervals. -/
theorem cantorMid_separated {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2)
    (m : ℕ) {u L : ℝ} (hL : 0 ≤ L) {x y : ℝ}
    (hx : x ∈ cantorMid mu m u L) (hy : y ∈ cantorMid mu m u L) (hxy : x ≠ y) :
    mu ^ m * L ≤ |x - y| := by
  induction m generalizing u L with
  | zero =>
      rw [cantorMid_zero, Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  | succ m ih =>
      have hmuL : 0 ≤ mu * L := mul_nonneg hmu.le hL
      have hpowmul : mu ^ m * (mu * L) = mu ^ (m + 1) * L := by ring
      rw [cantorMid_succ, Finset.mem_union] at hx hy
      rcases hx with hx | hx
      · rcases hy with hy | hy
        · have h := ih hmuL hx hy
          rw [hpowmul] at h
          exact h
        · -- `x` in the left half, `y` in the right half
          obtain ⟨-, hx2⟩ := cantorMid_mem_bounds hmu hmu2 m hmuL hx
          obtain ⟨hy1, -⟩ := cantorMid_mem_bounds hmu hmu2 m hmuL hy
          rw [hpowmul] at hx2 hy1
          have hposL : 0 ≤ mu ^ (m + 1) * L := mul_nonneg (pow_pos hmu (m + 1)).le hL
          have hgap : mu ^ (m + 1) * L ≤ y - x := by
            have hmu2L : (1 - 2 * mu) * L ≥ 0 := mul_nonneg (by linarith) hL
            nlinarith [hx2, hy1, hmu2L]
          rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
          exact hgap
      · rcases hy with hy | hy
        · obtain ⟨hx1, -⟩ := cantorMid_mem_bounds hmu hmu2 m hmuL hx
          obtain ⟨-, hy2⟩ := cantorMid_mem_bounds hmu hmu2 m hmuL hy
          rw [hpowmul] at hx1 hy2
          have hposL : 0 ≤ mu ^ (m + 1) * L := mul_nonneg (pow_pos hmu (m + 1)).le hL
          have hgap : mu ^ (m + 1) * L ≤ x - y := by
            have hmu2L : (1 - 2 * mu) * L ≥ 0 := mul_nonneg (by linarith) hL
            nlinarith [hx1, hy2, hmu2L]
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]
          exact hgap
        · have h := ih hmuL hx hy
          rw [hpowmul] at h
          exact h

/-- The midpoint set has exactly `2 ^ m` elements. -/
theorem cantorMid_card {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2)
    (m : ℕ) {u L : ℝ} (hL : 0 < L) :
    (cantorMid mu m u L).card = 2 ^ m := by
  induction m generalizing u L with
  | zero => simp [cantorMid_zero]
  | succ m ih =>
      have hmuL : 0 < mu * L := mul_pos hmu hL
      have hdisj : Disjoint (cantorMid mu m u (mu * L))
          (cantorMid mu m (u + (1 - mu) * L) (mu * L)) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨-, hx2⟩ := cantorMid_mem_bounds hmu hmu2 m hmuL.le hx
        obtain ⟨hx1, -⟩ := cantorMid_mem_bounds hmu hmu2 m hmuL.le hx'
        have hpos : 0 < mu ^ m * (mu * L) := mul_pos (pow_pos hmu m) hmuL
        have hmu2L : (1 - 2 * mu) * L ≥ 0 := mul_nonneg (by linarith) hL.le
        nlinarith [hx1, hx2, hpos, hmu2L]
      rw [cantorMid_succ, Finset.card_union_of_disjoint hdisj, ih hmuL, ih hmuL]
      ring

/-- The `j`-th generation midpoints cover the `m`-th generation midpoints at every scale at
least the length of the `j`-th generation intervals. -/
theorem cantorMid_cover {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2)
    (j : ℕ) : ∀ (m : ℕ), j ≤ m → ∀ (u L δ : ℝ), 0 ≤ L → mu ^ j * L ≤ δ →
      ∀ x ∈ cantorMid mu m u L, ∃ y ∈ cantorMid mu j u L, |x - y| ≤ δ / 2 := by
  induction j with
  | zero =>
      intro m _ u L δ hL hδ x hx
      refine ⟨u + L / 2, by simp [cantorMid_zero], ?_⟩
      obtain ⟨h1, h2⟩ := cantorMid_mem_bounds hmu hmu2 m hL hx
      have hpow : 0 ≤ mu ^ m * L / 2 := by
        apply div_nonneg (mul_nonneg (le_of_lt (pow_pos hmu m)) hL) (by norm_num)
      rw [abs_le]
      constructor
      · simp only [pow_zero, one_mul] at hδ
        linarith
      · simp only [pow_zero, one_mul] at hδ
        linarith
  | succ j ih =>
      intro m hjm u L δ hL hδ x hx
      obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' + 1 := ⟨m - 1, by omega⟩
      have hjm' : j ≤ m' := by omega
      have hmuL : 0 ≤ mu * L := mul_nonneg hmu.le hL
      have hδ' : mu ^ j * (mu * L) ≤ δ := by
        have : mu ^ j * (mu * L) = mu ^ (j + 1) * L := by ring
        rw [this]
        exact hδ
      rw [cantorMid_succ, Finset.mem_union] at hx
      rcases hx with hx | hx
      · obtain ⟨y, hy, hdist⟩ := ih m' hjm' u (mu * L) δ hmuL hδ' x hx
        refine ⟨y, ?_, hdist⟩
        rw [cantorMid_succ]
        exact Finset.mem_union_left _ hy
      · obtain ⟨y, hy, hdist⟩ := ih m' hjm' (u + (1 - mu) * L) (mu * L) δ hmuL hδ' x hx
        refine ⟨y, ?_, hdist⟩
        rw [cantorMid_succ]
        exact Finset.mem_union_right _ hy

/-! ## A toolkit for computing the covering dimensions

Lower bounds for covering numbers come from separated finite subsets, and the two dimensions
are infima of the sets of admissible exponents. -/

/-- A `δ`-separated subset is not larger than any cover at scale `δ`. -/
theorem card_le_card_of_intervalCover_of_separated
    {F : Set ℝ} {δ : ℝ} {ι S : Finset ℝ}
    (hcover : IsIntervalCover F δ ι) (hSF : ∀ x ∈ S, x ∈ F)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ < |x - y|) :
    S.card ≤ ι.card := by
  classical
  have hmem : ∀ x ∈ S, ∃ a ∈ ι, x ∈ Icc (a - δ / 2) (a + δ / 2) := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Set.mem_iUnion₂.mp (hcover (hSF x hx))
    exact ⟨a, ha, hax⟩
  choose! c hc hcmem using hmem
  refine Finset.card_le_card_of_injOn c (fun x hx => hc x hx) ?_
  intro x hx y hy hxy
  by_contra hne
  have h1 := hcmem x hx
  have h2 := hcmem y hy
  rw [hxy] at h1
  simp only [mem_Icc] at h1 h2
  have hdist : |x - y| ≤ δ := by
    rw [abs_le]
    exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  exact absurd hdist (not_le.mpr (hsep x hx y hy hne))

/-- Characterization of the upper Minkowski dimension by a matching pair of bounds. -/
theorem upperMinkowskiDimension_eq_of_bounds {F : Set ℝ} {beta : ℝ}
    (hbeta : 0 ≤ beta) (hup : HasUpperMinkowskiExponent F beta)
    (hlow : ∀ beta' : ℝ, 0 ≤ beta' → beta' < beta → ¬ HasUpperMinkowskiExponent F beta') :
    upperMinkowskiDimension F = beta := by
  have hmem : beta ∈ {b : ℝ | 0 ≤ b ∧ HasUpperMinkowskiExponent F b} := ⟨hbeta, hup⟩
  have hbdd : ∀ b ∈ {b : ℝ | 0 ≤ b ∧ HasUpperMinkowskiExponent F b}, beta ≤ b := by
    intro b hb
    by_contra hcon
    exact hlow b hb.1 (not_le.mp hcon) hb.2
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, fun b hb => hb.1⟩ hmem
  · exact le_csInf ⟨beta, hmem⟩ hbdd

/-- Characterization of the upper Assouad spectrum by a matching pair of bounds. -/
theorem upperAssouadSpectrum_eq_of_bounds {F : Set ℝ} {θ gam : ℝ}
    (hgam : 0 ≤ gam) (hup : HasUpperAssouadSpectrumExponent F θ gam)
    (hlow : ∀ gam' : ℝ, 0 ≤ gam' → gam' < gam → ¬ HasUpperAssouadSpectrumExponent F θ gam') :
    upperAssouadSpectrum F θ = gam := by
  have hmem : gam ∈ {g : ℝ | 0 ≤ g ∧ HasUpperAssouadSpectrumExponent F θ g} := ⟨hgam, hup⟩
  have hbdd : ∀ g ∈ {g : ℝ | 0 ≤ g ∧ HasUpperAssouadSpectrumExponent F θ g}, gam ≤ g := by
    intro g hg
    by_contra hcon
    exact hlow g hg.1 (not_le.mp hcon) hg.2
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, fun g hg => hg.1⟩ hmem
  · exact le_csInf ⟨gam, hmem⟩ hbdd

/-- If the spectrum is bounded by `γ` everywhere and equals `γ` at parameters arbitrarily close
to one, the quasi-Assouad dimension is `γ`. -/
theorem quasiAssouadDimension_eq_of_spectrum {F : Set ℝ} {gam : ℝ}
    (hle : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → upperAssouadSpectrum F θ ≤ gam)
    (hex : ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ gam - ε ≤ upperAssouadSpectrum F θ) :
    quasiAssouadDimension F = gam := by
  have hne : (upperAssouadSpectrum F '' Ico (0 : ℝ) 1).Nonempty :=
    ⟨upperAssouadSpectrum F 0, ⟨0, ⟨le_refl _, one_pos⟩, rfl⟩⟩
  have hbdd : ∀ y ∈ upperAssouadSpectrum F '' Ico (0 : ℝ) 1, y ≤ gam := by
    intro y hy
    obtain ⟨θ, hθ, rfl⟩ := hy
    exact hle θ hθ.1 hθ.2
  refine le_antisymm (csSup_le hne hbdd) ?_
  by_contra hcon
  have hlt : sSup (upperAssouadSpectrum F '' Ico (0 : ℝ) 1) < gam := by
    rw [quasiAssouadDimension] at hcon
    exact not_le.mp hcon
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := hex ((gam - sSup (upperAssouadSpectrum F '' Ico (0 : ℝ) 1)) / 2)
    (by linarith)
  have hmem : upperAssouadSpectrum F θ ∈ upperAssouadSpectrum F '' Ico (0 : ℝ) 1 :=
    ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
  have hle' : upperAssouadSpectrum F θ ≤ sSup (upperAssouadSpectrum F '' Ico (0 : ℝ) 1) :=
    le_csSup ⟨gam, hbdd⟩ hmem
  linarith

/-! ## The Cantor sets behind the regular examples

`cantorGen μ m u L` is the union of the `2 ^ m` intervals of the `m`-th generation, and
`cantorSet μ u L` is their intersection over all generations.  The midpoint sets of the previous
section provide the centers of the generation intervals. -/

/-- The tree structure of the midpoint sets: the `(a+b)`-th generation midpoints are the `b`-th
generation midpoints of the `a`-th generation intervals. -/
theorem cantorMid_add (mu : ℝ) (a b : ℕ) (u L : ℝ) :
    cantorMid mu (a + b) u L =
      (cantorMid mu a u L).biUnion
        (fun c => cantorMid mu b (c - mu ^ a * L / 2) (mu ^ a * L)) := by
  classical
  induction a generalizing u L with
  | zero =>
      simp only [Nat.zero_add, pow_zero, one_mul, cantorMid_zero, Finset.singleton_biUnion]
      congr 1
      ring
  | succ a ih =>
      have hsucc : a + 1 + b = (a + b) + 1 := by omega
      have hpow : mu ^ a * (mu * L) = mu ^ (a + 1) * L := by ring
      rw [hsucc, cantorMid_succ, ih u (mu * L), ih (u + (1 - mu) * L) (mu * L), cantorMid_succ,
        Finset.union_biUnion]
      simp only [hpow]

/-- The union of the `m`-th generation intervals. -/
def cantorGen (mu : ℝ) : ℕ → ℝ → ℝ → Set ℝ
  | 0, u, L => Icc u (u + L)
  | (m + 1), u, L =>
      cantorGen mu m u (mu * L) ∪ cantorGen mu m (u + (1 - mu) * L) (mu * L)

theorem cantorGen_zero (mu u L : ℝ) : cantorGen mu 0 u L = Icc u (u + L) := rfl

theorem cantorGen_succ (mu : ℝ) (m : ℕ) (u L : ℝ) :
    cantorGen mu (m + 1) u L =
      cantorGen mu m u (mu * L) ∪ cantorGen mu m (u + (1 - mu) * L) (mu * L) := rfl

/-- Each generation is the union of the closed intervals centered at the midpoints. -/
theorem cantorGen_eq_biUnion_Icc {mu : ℝ} (m : ℕ) (u L : ℝ) :
    cantorGen mu m u L =
      ⋃ c ∈ cantorMid mu m u L, Icc (c - mu ^ m * L / 2) (c + mu ^ m * L / 2) := by
  induction m generalizing u L with
  | zero =>
      rw [cantorGen_zero, cantorMid_zero]
      apply Set.eq_of_subset_of_subset
      · intro x hx
        refine Set.mem_iUnion₂.mpr ⟨u + L / 2, Finset.mem_singleton_self _, ?_⟩
        simp only [pow_zero, one_mul, Set.mem_Icc] at hx ⊢
        constructor <;> linarith [hx.1, hx.2]
      · intro x hx
        obtain ⟨c, hc, hx'⟩ := Set.mem_iUnion₂.mp hx
        rw [Finset.mem_singleton] at hc
        subst hc
        simp only [pow_zero, one_mul, Set.mem_Icc] at hx' ⊢
        constructor <;> linarith [hx'.1, hx'.2]
  | succ m ih =>
      rw [cantorGen_succ, cantorMid_succ, ih u (mu * L), ih (u + (1 - mu) * L) (mu * L)]
      have hpow : mu ^ m * (mu * L) = mu ^ (m + 1) * L := by ring
      rw [hpow]
      apply Set.eq_of_subset_of_subset
      · intro x hx
        rcases hx with hx | hx
        · obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
          exact Set.mem_iUnion₂.mpr ⟨c, Finset.mem_union_left _ hc, hxc⟩
        · obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
          exact Set.mem_iUnion₂.mpr ⟨c, Finset.mem_union_right _ hc, hxc⟩
      · intro x hx
        obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
        rw [Finset.mem_union] at hc
        rcases hc with hc | hc
        · exact Or.inl (Set.mem_iUnion₂.mpr ⟨c, hc, hxc⟩)
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨c, hc, hxc⟩)

/-- Later generations are contained in earlier ones. -/
theorem cantorGen_succ_subset {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2) (m : ℕ)
    {u L : ℝ} (hL : 0 ≤ L) : cantorGen mu (m + 1) u L ⊆ cantorGen mu m u L := by
  induction m generalizing u L with
  | zero =>
      rw [cantorGen_succ, cantorGen_zero, cantorGen_zero, cantorGen_zero]
      intro x hx
      rcases hx with hx | hx
      · refine ⟨hx.1, le_trans hx.2 ?_⟩
        have : mu * L ≤ L := by nlinarith
        linarith
      · refine ⟨le_trans ?_ hx.1, le_trans hx.2 ?_⟩
        · have : 0 ≤ (1 - mu) * L := mul_nonneg (by linarith) hL
          linarith
        · have : (1 - mu) * L + mu * L = L := by ring
          linarith
  | succ m ih =>
      have hmuL : 0 ≤ mu * L := mul_nonneg hmu.le hL
      rw [cantorGen_succ, cantorGen_succ]
      exact Set.union_subset_union (ih hmuL) (ih hmuL)

theorem cantorGen_antitone {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2)
    {u L : ℝ} (hL : 0 ≤ L) : ∀ {m m' : ℕ}, m ≤ m' →
      cantorGen mu m' u L ⊆ cantorGen mu m u L := by
  intro m m' hmm
  induction m' with
  | zero =>
      have : m = 0 := by omega
      subst this
      exact subset_rfl
  | succ m' ih =>
      rcases Nat.lt_or_ge m (m' + 1) with hlt | hge
      · have hm : m ≤ m' := by omega
        exact (cantorGen_succ_subset hmu hmu2 m' hL).trans (ih hm)
      · have : m = m' + 1 := by omega
        subst this
        exact subset_rfl

/-- The Cantor set of ratio `mu` in `[u, u + L]`. -/
def cantorSet (mu u L : ℝ) : Set ℝ := ⋂ m : ℕ, cantorGen mu m u L

theorem cantorSet_subset_cantorGen (mu u L : ℝ) (m : ℕ) :
    cantorSet mu u L ⊆ cantorGen mu m u L := Set.iInter_subset _ m

theorem cantorSet_subset_Icc (mu u L : ℝ) : cantorSet mu u L ⊆ Icc u (u + L) := by
  have := cantorSet_subset_cantorGen mu u L 0
  rwa [cantorGen_zero] at this

/-- The left endpoints of the `m`-th generation intervals. -/
def cantorLeft (mu : ℝ) : ℕ → ℝ → ℝ → Finset ℝ
  | 0, u, _ => {u}
  | (m + 1), u, L =>
      cantorLeft mu m u (mu * L) ∪ cantorLeft mu m (u + (1 - mu) * L) (mu * L)

theorem cantorLeft_zero (mu u L : ℝ) : cantorLeft mu 0 u L = {u} := rfl

theorem cantorLeft_succ (mu : ℝ) (m : ℕ) (u L : ℝ) :
    cantorLeft mu (m + 1) u L =
      cantorLeft mu m u (mu * L) ∪ cantorLeft mu m (u + (1 - mu) * L) (mu * L) := rfl

/-- Left endpoints are contained in the corresponding generation. -/
theorem cantorLeft_subset_cantorGen {mu : ℝ} (hmu : 0 < mu) (_hmu2 : mu ≤ 1 / 2) (m : ℕ)
    {u L : ℝ} (hL : 0 ≤ L) :
    ∀ x ∈ cantorLeft mu m u L, x ∈ cantorGen mu m u L := by
  induction m generalizing u L with
  | zero =>
      intro x hx
      rw [cantorLeft_zero, Finset.mem_singleton] at hx
      subst hx
      rw [cantorGen_zero]
      exact ⟨le_refl _, by linarith⟩
  | succ m ih =>
      intro x hx
      have hmuL : 0 ≤ mu * L := mul_nonneg hmu.le hL
      rw [cantorLeft_succ, Finset.mem_union] at hx
      rw [cantorGen_succ]
      rcases hx with hx | hx
      · exact Or.inl (ih hmuL x hx)
      · exact Or.inr (ih hmuL x hx)

/-- Left endpoints persist into the next generation. -/
theorem cantorLeft_subset_succ {mu : ℝ} (m : ℕ) {u L : ℝ} :
    ∀ x ∈ cantorLeft mu m u L, x ∈ cantorLeft mu (m + 1) u L := by
  induction m generalizing u L with
  | zero =>
      intro x hx
      rw [cantorLeft_zero, Finset.mem_singleton] at hx
      subst hx
      rw [cantorLeft_succ]
      refine Finset.mem_union_left _ ?_
      rw [cantorLeft_zero]
      exact Finset.mem_singleton_self _
  | succ m ih =>
      intro x hx
      rw [cantorLeft_succ, Finset.mem_union] at hx
      rw [cantorLeft_succ, Finset.mem_union]
      rcases hx with hx | hx
      · exact Or.inl (ih x hx)
      · exact Or.inr (ih x hx)

theorem cantorLeft_subset_of_le {mu : ℝ} {m m' : ℕ} (hmm : m ≤ m') {u L : ℝ} :
    ∀ x ∈ cantorLeft mu m u L, x ∈ cantorLeft mu m' u L := by
  induction m' with
  | zero =>
      have : m = 0 := by omega
      subst this
      exact fun x hx => hx
  | succ m' ih =>
      rcases Nat.lt_or_ge m (m' + 1) with hlt | hge
      · have hm : m ≤ m' := by omega
        exact fun x hx => cantorLeft_subset_succ m' x (ih hm x hx)
      · have : m = m' + 1 := by omega
        subst this
        exact fun x hx => hx

/-- The left endpoints of every generation belong to the Cantor set. -/
theorem cantorLeft_subset_cantorSet {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2) (m : ℕ)
    {u L : ℝ} (hL : 0 ≤ L) :
    ∀ x ∈ cantorLeft mu m u L, x ∈ cantorSet mu u L := by
  intro x hx
  rw [cantorSet, Set.mem_iInter]
  intro m'
  rcases Nat.lt_or_ge m' m with hlt | hge
  · exact cantorGen_antitone hmu hmu2 hL (le_of_lt hlt)
      (cantorLeft_subset_cantorGen hmu hmu2 m hL x hx)
  · exact cantorLeft_subset_cantorGen hmu hmu2 m' hL x
      (cantorLeft_subset_of_le hge x hx)

/-! ### Left endpoints: bounds, separation and cardinality -/

theorem cantorLeft_mem_bounds {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2)
    (m : ℕ) {u L : ℝ} (hL : 0 ≤ L) {x : ℝ} (hx : x ∈ cantorLeft mu m u L) :
    u ≤ x ∧ x ≤ u + L - mu ^ m * L := by
  induction m generalizing u L with
  | zero =>
      rw [cantorLeft_zero, Finset.mem_singleton] at hx
      subst hx
      refine ⟨le_refl _, ?_⟩
      simp
  | succ m ih =>
      rw [cantorLeft_succ, Finset.mem_union] at hx
      have hmuL : 0 ≤ mu * L := mul_nonneg hmu.le hL
      have hpowmul : mu ^ m * (mu * L) = mu ^ (m + 1) * L := by ring
      rcases hx with hx | hx
      · obtain ⟨h1, h2⟩ := ih hmuL hx
        rw [hpowmul] at h2
        refine ⟨h1, ?_⟩
        have hmuLle : mu * L ≤ L := by nlinarith
        linarith
      · obtain ⟨h1, h2⟩ := ih hmuL hx
        rw [hpowmul] at h2
        have hone : 0 ≤ (1 - mu) * L := mul_nonneg (by linarith) hL
        refine ⟨by linarith, ?_⟩
        have hsum : (1 - mu) * L + mu * L = L := by ring
        linarith

theorem cantorLeft_separated {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2)
    (m : ℕ) {u L : ℝ} (hL : 0 ≤ L) {x y : ℝ}
    (hx : x ∈ cantorLeft mu m u L) (hy : y ∈ cantorLeft mu m u L) (hxy : x ≠ y) :
    mu ^ m * L ≤ |x - y| := by
  induction m generalizing u L with
  | zero =>
      rw [cantorLeft_zero, Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  | succ m ih =>
      have hmuL : 0 ≤ mu * L := mul_nonneg hmu.le hL
      have hpowmul : mu ^ m * (mu * L) = mu ^ (m + 1) * L := by ring
      have hposL : 0 ≤ mu ^ (m + 1) * L := mul_nonneg (pow_pos hmu (m + 1)).le hL
      rw [cantorLeft_succ, Finset.mem_union] at hx hy
      rcases hx with hx | hx
      · rcases hy with hy | hy
        · have h := ih hmuL hx hy
          rw [hpowmul] at h
          exact h
        · obtain ⟨-, hx2⟩ := cantorLeft_mem_bounds hmu hmu2 m hmuL hx
          obtain ⟨hy1, -⟩ := cantorLeft_mem_bounds hmu hmu2 m hmuL hy
          rw [hpowmul] at hx2
          have hgap : mu ^ (m + 1) * L ≤ y - x := by
            have hmu2L : (1 - 2 * mu) * L ≥ 0 := mul_nonneg (by linarith) hL
            nlinarith [hx2, hy1, hmu2L]
          rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
          exact hgap
      · rcases hy with hy | hy
        · obtain ⟨hx1, -⟩ := cantorLeft_mem_bounds hmu hmu2 m hmuL hx
          obtain ⟨-, hy2⟩ := cantorLeft_mem_bounds hmu hmu2 m hmuL hy
          rw [hpowmul] at hy2
          have hgap : mu ^ (m + 1) * L ≤ x - y := by
            have hmu2L : (1 - 2 * mu) * L ≥ 0 := mul_nonneg (by linarith) hL
            nlinarith [hx1, hy2, hmu2L]
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]
          exact hgap
        · have h := ih hmuL hx hy
          rw [hpowmul] at h
          exact h

theorem cantorLeft_card {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2)
    (m : ℕ) {u L : ℝ} (hL : 0 < L) :
    (cantorLeft mu m u L).card = 2 ^ m := by
  induction m generalizing u L with
  | zero => simp [cantorLeft_zero]
  | succ m ih =>
      have hmuL : 0 < mu * L := mul_pos hmu hL
      have hdisj : Disjoint (cantorLeft mu m u (mu * L))
          (cantorLeft mu m (u + (1 - mu) * L) (mu * L)) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨-, hx2⟩ := cantorLeft_mem_bounds hmu hmu2 m hmuL.le hx
        obtain ⟨hx1, -⟩ := cantorLeft_mem_bounds hmu hmu2 m hmuL.le hx'
        have hpos : 0 < mu ^ m * (mu * L) := mul_pos (pow_pos hmu m) hmuL
        have hmu2L : (1 - 2 * mu) * L ≥ 0 := mul_nonneg (by linarith) hL.le
        nlinarith [hx1, hx2, hpos, hmu2L]
      rw [cantorLeft_succ, Finset.card_union_of_disjoint hdisj, ih hmuL, ih hmuL]
      ring

/-! ### The generation midpoints cover the Cantor set -/

theorem cantorSet_intervalCover {mu : ℝ} (m : ℕ) {u L δ : ℝ}
    (hδ : mu ^ m * L ≤ δ) :
    IsIntervalCover (cantorSet mu u L) δ (cantorMid mu m u L) := by
  intro x hx
  have hxgen : x ∈ cantorGen mu m u L := cantorSet_subset_cantorGen mu u L m hx
  rw [cantorGen_eq_biUnion_Icc] at hxgen
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hxgen
  refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
  simp only [Set.mem_Icc] at hxc ⊢
  constructor <;> linarith [hxc.1, hxc.2, hδ]

/-! ### The Cantor ratio attached to a dimension -/

/-- The contraction ratio of a Cantor set of dimension `gam`. -/
def cantorRatio (gam : ℝ) : ℝ := (2 : ℝ) ^ (-(1 / gam))

theorem cantorRatio_pos (gam : ℝ) : 0 < cantorRatio gam :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem cantorRatio_le_half {gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1) :
    cantorRatio gam ≤ 1 / 2 := by
  rw [cantorRatio]
  have hexp : -(1 / gam) ≤ -1 := by
    have h1 : (1 : ℝ) ≤ 1 / gam := by
      rw [le_div_iff₀ hgam]
      linarith
    linarith
  calc (2 : ℝ) ^ (-(1 / gam)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 1 / 2 := by
        rw [Real.rpow_neg_one]
        norm_num

theorem cantorRatio_lt_one {gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1) :
    cantorRatio gam < 1 :=
  lt_of_le_of_lt (cantorRatio_le_half hgam hgam1) (by norm_num)

/-- The defining relation of the ratio: the `m`-th generation has `2 ^ m` intervals of
length `μ ^ m`, and `(μ ^ m) ^ (-γ) = 2 ^ m`. -/
theorem cantorRatio_pow_rpow_neg {gam : ℝ} (hgam : 0 < gam) (m : ℕ) :
    ((cantorRatio gam) ^ m) ^ (-gam) = (2 : ℝ) ^ m := by
  have hpos : (0 : ℝ) < cantorRatio gam := cantorRatio_pos gam
  have hpow : (cantorRatio gam) ^ m = (2 : ℝ) ^ (-(m / gam)) := by
    rw [cantorRatio, ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / gam))) m,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    field_simp
  rw [hpow, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show -(m / gam) * -gam = (m : ℝ) by field_simp]
  rw [Real.rpow_natCast]

/-! ### The Minkowski dimension of the Cantor set -/

/-- The `m`-th generation cover gives the upper Minkowski estimate at the exponent `gam`. -/
theorem hasUpperMinkowskiExponent_cantorSet {gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1)
    (u : ℝ) : HasUpperMinkowskiExponent (cantorSet (cantorRatio gam) u 1) gam := by
  intro ε hε
  refine ⟨2, by norm_num, ?_⟩
  intro δ hδ hδone
  have hmu : 0 < cantorRatio gam := cantorRatio_pos gam
  have hmu2 : cantorRatio gam ≤ 1 / 2 := cantorRatio_le_half hgam hgam1
  have hmulone : cantorRatio gam < 1 := lt_of_le_of_lt hmu2 (by norm_num)
  -- the least generation whose intervals are shorter than `δ`
  have hex : ∃ n : ℕ, (cantorRatio gam) ^ n < δ := exists_pow_lt_of_lt_one hδ hmulone
  classical
  set m : ℕ := Nat.find hex with hmdef
  have hmspec : (cantorRatio gam) ^ m < δ := Nat.find_spec hex
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · rw [h0] at hmspec
      simp only [pow_zero] at hmspec
      linarith
    · exact h
  have hprev : ¬ ((cantorRatio gam) ^ (m - 1) < δ) := Nat.find_min hex (by omega)
  have hprevle : δ ≤ (cantorRatio gam) ^ (m - 1) := not_lt.mp hprev
  refine ⟨cantorMid (cantorRatio gam) m u 1, ?_, ?_⟩
  · refine cantorSet_intervalCover m ?_
    rw [mul_one]
    exact hmspec.le
  · rw [cantorMid_card hmu hmu2 m (by norm_num : (0:ℝ) < 1)]
    -- `2 ^ m = (μ ^ m) ^ (-γ) < (μ δ) ^ (-γ) = 2 δ ^ (-γ) ≤ 2 δ ^ (-(γ + ε))`
    have hpowpos : 0 < (cantorRatio gam) ^ m := pow_pos hmu m
    have hmuprev : (cantorRatio gam) ^ m = cantorRatio gam * (cantorRatio gam) ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hlow : cantorRatio gam * δ ≤ (cantorRatio gam) ^ m := by
      rw [hmuprev]
      exact mul_le_mul_of_nonneg_left hprevle hmu.le
    have hstep1 : ((cantorRatio gam) ^ m) ^ (-gam) ≤ (cantorRatio gam * δ) ^ (-gam) := by
      rcases eq_or_lt_of_le hlow with heq | hlt
      · rw [heq]
      · exact le_of_lt (Real.rpow_lt_rpow_of_neg (by positivity) hlt (by linarith))
    have hstep2 : (cantorRatio gam * δ) ^ (-gam) = 2 * δ ^ (-gam) := by
      rw [Real.mul_rpow hmu.le hδ.le]
      congr 1
      have h1 : (cantorRatio gam) ^ (-gam) = ((cantorRatio gam) ^ (1 : ℕ)) ^ (-gam) := by
        norm_num
      rw [h1, cantorRatio_pow_rpow_neg hgam 1]
      norm_num
    have hstep3 : δ ^ (-gam) ≤ δ ^ (-(gam + ε)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδone.le
      linarith
    have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by
      push_cast
      ring
    rw [hcast, ← cantorRatio_pow_rpow_neg hgam m]
    calc ((cantorRatio gam) ^ m) ^ (-gam) ≤ (cantorRatio gam * δ) ^ (-gam) := hstep1
      _ = 2 * δ ^ (-gam) := hstep2
      _ ≤ 2 * δ ^ (-(gam + ε)) := by
          exact mul_le_mul_of_nonneg_left hstep3 (by norm_num)

/-- The separated left-endpoint sets rule out every smaller Minkowski exponent. -/
theorem not_hasUpperMinkowskiExponent_cantorSet {gam gam' : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1)
    (hgam'0 : 0 ≤ gam') (hlt : gam' < gam) (u : ℝ) :
    ¬ HasUpperMinkowskiExponent (cantorSet (cantorRatio gam) u 1) gam' := by
  intro hcon
  have hmu : 0 < cantorRatio gam := cantorRatio_pos gam
  have hmu2 : cantorRatio gam ≤ 1 / 2 := cantorRatio_le_half hgam hgam1
  have hmulone : cantorRatio gam < 1 := lt_of_le_of_lt hmu2 (by norm_num)
  set ε : ℝ := (gam - gam') / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, hC, hcover⟩ := hcon ε hε
  set gam'' : ℝ := gam' + ε with hg2def
  have hg2 : gam'' < gam := by rw [hg2def, hεdef]; linarith
  have hg20 : 0 ≤ gam'' := by rw [hg2def]; linarith
  -- choose a generation with more separated points than the covering bound allows
  set ρ : ℝ := 1 - gam'' / gam with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    have : gam'' / gam < 1 := by
      rw [div_lt_one hgam]
      exact hg2
    linarith
  have hbase : (1 : ℝ) < (2 : ℝ) ^ ρ := Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr
    (Or.inl ⟨by norm_num, hρpos⟩)
  have hexn : ∃ n : ℕ, ((2 : ℝ) ^ ρ)⁻¹ ^ n < (C * 2 ^ gam'')⁻¹ := by
    apply exists_pow_lt_of_lt_one
    · positivity
    · rw [inv_lt_one_iff₀]
      right
      exact hbase
  obtain ⟨m, hm⟩ := hexn
  -- the cover at scale `δ = μ ^ m / 2`
  set δ : ℝ := (cantorRatio gam) ^ m / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδone : δ < 1 := by
    rw [hδdef]
    have h1 : (cantorRatio gam) ^ m ≤ 1 := pow_le_one₀ hmu.le hmulone.le
    linarith
  obtain ⟨ι, hι, hcard⟩ := hcover δ hδpos hδone
  have hsep : ∀ x ∈ cantorLeft (cantorRatio gam) m u 1, ∀ y ∈ cantorLeft (cantorRatio gam) m u 1,
      x ≠ y → δ < |x - y| := by
    intro x hx y hy hxy
    have h := cantorLeft_separated hmu hmu2 m (by norm_num : (0:ℝ) ≤ 1) hx hy hxy
    rw [mul_one] at h
    rw [hδdef]
    have hpospow : 0 < (cantorRatio gam) ^ m := pow_pos hmu m
    linarith
  have hSF : ∀ x ∈ cantorLeft (cantorRatio gam) m u 1, x ∈ cantorSet (cantorRatio gam) u 1 := by
    intro x hx
    exact cantorLeft_subset_cantorSet hmu hmu2 m (by norm_num : (0:ℝ) ≤ 1) x hx
  have hlow := card_le_card_of_intervalCover_of_separated hι hSF hsep
  rw [cantorLeft_card hmu hmu2 m (by norm_num : (0:ℝ) < 1)] at hlow
  -- contradiction with the covering bound
  have hcardreal : ((2 ^ m : ℕ) : ℝ) ≤ C * δ ^ (-(gam' + ε)) := by
    refine le_trans ?_ hcard
    exact_mod_cast hlow
  have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by push_cast; ring
  rw [hcast] at hcardreal
  -- evaluate the right-hand side
  have hval : δ ^ (-gam'') = 2 ^ gam'' * ((2 : ℝ) ^ m) ^ (gam'' / gam) := by
    rw [hδdef]
    rw [Real.div_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 2)]
    have h1 : ((cantorRatio gam) ^ m) ^ (-gam'') =
        (((cantorRatio gam) ^ m) ^ (-gam)) ^ (gam'' / gam) := by
      rw [← Real.rpow_natCast (cantorRatio gam) m]
      rw [← Real.rpow_mul hmu.le, ← Real.rpow_mul hmu.le, ← Real.rpow_mul hmu.le]
      congr 1
      field_simp
    have h2 : ((2 : ℝ) ^ (-gam'')) = ((2 : ℝ) ^ gam'')⁻¹ :=
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) gam''
    rw [h1, cantorRatio_pow_rpow_neg hgam m, h2]
    field_simp
  rw [← hg2def] at hcardreal
  rw [hval] at hcardreal
  -- now `2 ^ m ≤ C * 2 ^ γ'' * (2 ^ m) ^ (γ''/γ)`, contradicting the choice of `m`
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hsplit : ((2 : ℝ) ^ m) ^ ρ ≤ C * 2 ^ gam'' := by
    have hid : ((2 : ℝ) ^ m) ^ ρ * ((2 : ℝ) ^ m) ^ (gam'' / gam) = (2 : ℝ) ^ m := by
      rw [← Real.rpow_natCast 2 m, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      rw [hρdef]
      ring
    have hposq : (0 : ℝ) < ((2 : ℝ) ^ m) ^ (gam'' / gam) := by positivity
    have hmul : ((2 : ℝ) ^ m) ^ ρ * ((2 : ℝ) ^ m) ^ (gam'' / gam) ≤
        (C * 2 ^ gam'') * ((2 : ℝ) ^ m) ^ (gam'' / gam) := by
      rw [hid]
      calc (2 : ℝ) ^ m ≤ C * (2 ^ gam'' * ((2 : ℝ) ^ m) ^ (gam'' / gam)) := hcardreal
        _ = C * 2 ^ gam'' * ((2 : ℝ) ^ m) ^ (gam'' / gam) := by ring
    exact le_of_mul_le_mul_right hmul hposq
  have hgrow : C * 2 ^ gam'' < ((2 : ℝ) ^ ρ) ^ m := by
    have hinv : ((2 : ℝ) ^ ρ)⁻¹ ^ m < (C * 2 ^ gam'')⁻¹ := hm
    have hposbase : (0 : ℝ) < ((2 : ℝ) ^ ρ) ^ m := by positivity
    have hposC : (0 : ℝ) < C * 2 ^ gam'' := by positivity
    rw [inv_pow] at hinv
    exact (inv_lt_inv₀ hposbase hposC).mp hinv
  have hidpow : ((2 : ℝ) ^ m) ^ ρ = ((2 : ℝ) ^ ρ) ^ m := by
    rw [← Real.rpow_natCast 2 m, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast ((2 : ℝ) ^ ρ) m, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [hidpow] at hsplit
  linarith

/-! ### Counting separated points in a short interval -/

/-- A `len`-separated subset of an interval of length `2 * len` has at most three points. -/
theorem card_le_three_of_separated_in_interval {S : Finset ℝ} {s len : ℝ} (hlen : 0 < len)
    (hsub : ∀ x ∈ S, x ∈ Icc s (s + 2 * len))
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → len ≤ |x - y|) :
    S.card ≤ 3 := by
  classical
  have hcard : S.card ≤ (Finset.Icc (0 : ℤ) 2).card := by
    refine Finset.card_le_card_of_injOn (fun x => ⌊(x - s) / len⌋) ?_ ?_
    · intro x hx
      obtain ⟨h1, h2⟩ := hsub x hx
      have hq0 : (0 : ℝ) ≤ (x - s) / len := by
        apply div_nonneg (by linarith) hlen.le
      have hq2 : (x - s) / len ≤ 2 := by
        rw [div_le_iff₀ hlen]
        linarith
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · exact Int.le_floor.mpr (by simpa using hq0)
      · have hfl := Int.floor_le_floor hq2
        simpa using hfl
    · intro x hx y hy hxy
      by_contra hne
      have hfx : ((⌊(x - s) / len⌋ : ℝ)) ≤ (x - s) / len := Int.floor_le _
      have hfy : ((⌊(y - s) / len⌋ : ℝ)) ≤ (y - s) / len := Int.floor_le _
      have hfx' : (x - s) / len < (⌊(x - s) / len⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have hfy' : (y - s) / len < (⌊(y - s) / len⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have hxy' : ⌊(x - s) / len⌋ = ⌊(y - s) / len⌋ := hxy
      rw [hxy'] at hfx hfx'
      have hdiff : |(x - s) / len - (y - s) / len| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      have hlenne : len ≠ 0 := hlen.ne'
      have hxydiv : (x - s) / len - (y - s) / len = (x - y) / len := by
        field_simp
        ring
      rw [hxydiv, abs_div, abs_of_pos hlen, div_lt_one hlen] at hdiff
      exact absurd (hsep x hx y hy hne) (not_le.mpr hdiff)
  simpa using hcard

/-! ### The ancestor of a midpoint -/

/-- Every `m`-th generation midpoint lies in the copy attached to a unique `ℓ`-th generation
midpoint, and is close to it. -/
theorem exists_ancestor_cantorMid {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2) {l m : ℕ}
    (hlm : l ≤ m) {u L : ℝ} (hL : 0 ≤ L) {c : ℝ} (hc : c ∈ cantorMid mu m u L) :
    ∃ c' ∈ cantorMid mu l u L,
      c ∈ cantorMid mu (m - l) (c' - mu ^ l * L / 2) (mu ^ l * L) ∧
        |c - c'| ≤ (mu ^ l * L - mu ^ m * L) / 2 := by
  classical
  have hml : m = l + (m - l) := by omega
  rw [hml, cantorMid_add] at hc
  obtain ⟨c', hc', hcc⟩ := Finset.mem_biUnion.mp hc
  refine ⟨c', hc', hcc, ?_⟩
  have hLl : 0 ≤ mu ^ l * L := mul_nonneg (pow_pos hmu l).le hL
  obtain ⟨h1, h2⟩ := cantorMid_mem_bounds hmu hmu2 (m - l) hLl hcc
  have hpowmul : mu ^ (m - l) * (mu ^ l * L) = mu ^ m * L := by
    have hp : mu ^ (m - l) * mu ^ l = mu ^ m := by
      rw [← pow_add]
      congr 1
      omega
    calc mu ^ (m - l) * (mu ^ l * L) = (mu ^ (m - l) * mu ^ l) * L := by ring
      _ = mu ^ m * L := by rw [hp]
  rw [hpowmul] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-! ### The Assouad estimate for the Cantor set -/

set_option maxHeartbeats 1000000 in
/-- For every interval longer than the scale, the Cantor set inside it is covered by at most
`12 (|I|/δ)^γ` intervals of length `δ`. -/
theorem cantorSet_assouad_cover {gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1) (u : ℝ)
    {δ a b : ℝ} (hδ : 0 < δ) (_hab : a ≤ b) (hlen : δ ≤ b - a) (hb1 : b - a ≤ 1) :
    ∃ ι : Finset ℝ, IsIntervalCover (cantorSet (cantorRatio gam) u 1 ∩ Icc a b) δ ι ∧
      (ι.card : ℝ) ≤ 12 * ((b - a) / δ) ^ gam := by
  classical
  set mu : ℝ := cantorRatio gam with hmudef
  have hmu : 0 < mu := cantorRatio_pos gam
  have hmu2 : mu ≤ 1 / 2 := cantorRatio_le_half hgam hgam1
  have hmulone : mu < 1 := lt_of_le_of_lt hmu2 (by norm_num)
  have hlenpos : 0 < b - a := lt_of_lt_of_le hδ hlen
  -- the generation finer than `δ`
  have hexm : ∃ n : ℕ, mu ^ n < δ := exists_pow_lt_of_lt_one hδ hmulone
  set m : ℕ := Nat.find hexm with hmdef
  have hmspec : mu ^ m < δ := Nat.find_spec hexm
  have hmpos : 0 < m ∨ δ > 1 := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · right
      rw [h0] at hmspec
      simpa using hmspec
    · left
      exact h
  -- the generation coarser than the interval
  have hexl : ∃ n : ℕ, mu ^ n < b - a := exists_pow_lt_of_lt_one hlenpos hmulone
  set l1 : ℕ := Nat.find hexl with hl1def
  have hl1spec : mu ^ l1 < b - a := Nat.find_spec hexl
  have hl1pos : 0 < l1 := by
    rcases Nat.eq_zero_or_pos l1 with h0 | h
    · rw [h0] at hl1spec
      simp only [pow_zero] at hl1spec
      linarith
    · exact h
  set l : ℕ := l1 - 1 with hldef
  have hlprev : ¬ (mu ^ l < b - a) := by
    rw [hldef]
    exact Nat.find_min hexl (by omega)
  have hlge : b - a ≤ mu ^ l := not_lt.mp hlprev
  have hl1eq : l1 = l + 1 := by omega
  have hlsucc : mu ^ (l + 1) < b - a := by rw [← hl1eq]; exact hl1spec
  -- the fine generation is finer than the coarse one
  have hlm : l ≤ m := by
    by_contra hcon
    have hml : m < l := by omega
    have hlt : mu ^ l < mu ^ m := (pow_lt_pow_iff_right_of_lt_one₀ hmu hmulone).2 hml
    linarith [hmspec, hlge, hlen]
  have hpowmpos : 0 < mu ^ m := pow_pos hmu m
  have hpowlpos : 0 < mu ^ l := pow_pos hmu l
  -- the cover: the fine midpoints whose intervals meet `[a, b]`
  set ι : Finset ℝ := (cantorMid mu m u 1).filter
    (fun c => a - mu ^ m / 2 ≤ c ∧ c ≤ b + mu ^ m / 2) with hιdef
  refine ⟨ι, ?_, ?_⟩
  · -- the covering property
    intro x hx
    obtain ⟨hxset, hxab⟩ := hx
    have hcover := cantorSet_intervalCover (mu := mu) m (u := u) (L := 1) (δ := mu ^ m)
      (by rw [mul_one])
    have hxmem := hcover hxset
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hxmem
    simp only [Set.mem_Icc] at hxc hxab
    refine Set.mem_iUnion₂.mpr ⟨c, ?_, ?_⟩
    · rw [hιdef, Finset.mem_filter]
      refine ⟨hc, ?_, ?_⟩
      · linarith [hxc.2, hxab.1]
      · linarith [hxc.1, hxab.2]
    · simp only [Set.mem_Icc]
      constructor <;> linarith [hxc.1, hxc.2, hmspec]
  · -- the cardinality bound
    set A : Finset ℝ := (cantorMid mu l u 1).filter
      (fun c' => a - mu ^ l / 2 ≤ c' ∧ c' ≤ b + mu ^ l / 2) with hAdef
    have hAcard : A.card ≤ 3 := by
      refine card_le_three_of_separated_in_interval (s := a - mu ^ l / 2) (len := mu ^ l)
        hpowlpos ?_ ?_
      · intro x hx
        rw [hAdef, Finset.mem_filter] at hx
        obtain ⟨-, h1, h2⟩ := hx
        simp only [Set.mem_Icc]
        constructor
        · exact h1
        · linarith [hlge]
      · intro x hx y hy hxy
        rw [hAdef, Finset.mem_filter] at hx hy
        have h := cantorMid_separated hmu hmu2 l (by norm_num : (0:ℝ) ≤ 1) hx.1 hy.1 hxy
        rw [mul_one] at h
        exact h
    have hsub : ι ⊆ A.biUnion (fun c' => cantorMid mu (m - l) (c' - mu ^ l * 1 / 2)
        (mu ^ l * 1)) := by
      intro c hc
      rw [hιdef, Finset.mem_filter] at hc
      obtain ⟨hcmid, hc1, hc2⟩ := hc
      obtain ⟨c', hc', hcpiece, hdist⟩ :=
        exists_ancestor_cantorMid hmu hmu2 hlm (by norm_num : (0:ℝ) ≤ 1) hcmid
      rw [mul_one, mul_one] at hdist
      refine Finset.mem_biUnion.mpr ⟨c', ?_, hcpiece⟩
      rw [hAdef, Finset.mem_filter]
      refine ⟨hc', ?_, ?_⟩
      · have habs := abs_le.mp hdist
        linarith [habs.1, habs.2]
      · have habs := abs_le.mp hdist
        linarith [habs.1, habs.2]
    have hcardbound : ι.card ≤ 3 * 2 ^ (m - l) := by
      have hstep1 : ι.card ≤ (A.biUnion (fun c' => cantorMid mu (m - l) (c' - mu ^ l * 1 / 2)
          (mu ^ l * 1))).card := Finset.card_le_card hsub
      have hstep2 : (A.biUnion (fun c' => cantorMid mu (m - l) (c' - mu ^ l * 1 / 2)
          (mu ^ l * 1))).card ≤ ∑ c' ∈ A, (cantorMid mu (m - l) (c' - mu ^ l * 1 / 2)
            (mu ^ l * 1)).card := Finset.card_biUnion_le
      have hstep3 : ∑ c' ∈ A, (cantorMid mu (m - l) (c' - mu ^ l * 1 / 2)
          (mu ^ l * 1)).card = A.card * 2 ^ (m - l) := by
        rw [Finset.sum_congr rfl (fun c' _ => cantorMid_card hmu hmu2 (m - l)
          (by rw [mul_one]; exact hpowlpos))]
        rw [Finset.sum_const, smul_eq_mul]
      calc ι.card ≤ ∑ c' ∈ A, (cantorMid mu (m - l) (c' - mu ^ l * 1 / 2)
            (mu ^ l * 1)).card := le_trans hstep1 hstep2
        _ = A.card * 2 ^ (m - l) := hstep3
        _ ≤ 3 * 2 ^ (m - l) := Nat.mul_le_mul_right _ hAcard
    -- convert to the real-valued estimate
    have hpow : ((2 : ℝ) ^ (m - l)) = ((mu ^ (m - l)) ^ (-gam)) := by
      rw [hmudef, cantorRatio_pow_rpow_neg hgam (m - l)]
    have hsplit : mu ^ (m - l) * mu ^ l = mu ^ m := by
      rw [← pow_add]
      congr 1
      omega
    have hlowbd : mu * δ ≤ mu ^ m * 1 := by
      rw [mul_one]
      have hmprev : ¬ (mu ^ (m - 1) < δ) := by
        rcases hmpos with hm | hd
        · exact Nat.find_min hexm (by omega)
        · exfalso
          linarith [hδ, hd, hlen, hb1]
      have hprevle : δ ≤ mu ^ (m - 1) := not_lt.mp hmprev
      have hmuprev : mu ^ m = mu * mu ^ (m - 1) := by
        rw [← pow_succ']
        congr 1
        rcases hmpos with hm | hd
        · omega
        · exfalso; linarith [hδ, hd, hlen, hb1]
      rw [hmuprev]
      exact mul_le_mul_of_nonneg_left hprevle hmu.le
    have hupbd : mu ^ l * mu < b - a := by
      calc mu ^ l * mu = mu ^ (l + 1) := (pow_succ mu l).symm
        _ < b - a := hlsucc
    have hratio : mu ^ 2 * δ / (b - a) < mu ^ (m - l) := by
      rw [div_lt_iff₀ hlenpos]
      have hkey : mu ^ (m - l) * (b - a) > mu ^ (m - l) * (mu ^ l * mu) := by
        apply mul_lt_mul_of_pos_left hupbd (pow_pos hmu (m - l))
      have hid : mu ^ (m - l) * (mu ^ l * mu) = mu ^ m * mu := by
        rw [← mul_assoc, hsplit]
      rw [hid] at hkey
      have hlow : mu ^ 2 * δ ≤ mu ^ m * mu := by
        have h1 : mu * δ ≤ mu ^ m := by
          have := hlowbd
          rw [mul_one] at this
          exact this
        calc mu ^ 2 * δ = mu * (mu * δ) := by ring
          _ ≤ mu * mu ^ m := by exact mul_le_mul_of_nonneg_left h1 hmu.le
          _ = mu ^ m * mu := by ring
      linarith
    have hfinal : ((2 : ℝ) ^ (m - l)) ≤ 4 * ((b - a) / δ) ^ gam := by
      rw [hpow]
      have hposq : (0 : ℝ) < mu ^ 2 * δ / (b - a) := by positivity
      have hstep : (mu ^ (m - l)) ^ (-gam) ≤ (mu ^ 2 * δ / (b - a)) ^ (-gam) := by
        exact le_of_lt (Real.rpow_lt_rpow_of_neg hposq hratio (by linarith))
      have heval : (mu ^ 2 * δ / (b - a)) ^ (-gam) = 4 * ((b - a) / δ) ^ gam := by
        have h1 : mu ^ 2 * δ / (b - a) = (mu ^ 2) * (δ / (b - a)) := by ring
        rw [h1, Real.mul_rpow (by positivity) (by positivity)]
        have h2 : ((mu ^ 2 : ℝ)) ^ (-gam) = 4 := by
          rw [hmudef, cantorRatio_pow_rpow_neg hgam 2]
          norm_num
        have h3 : ((δ / (b - a)) : ℝ) ^ (-gam) = ((b - a) / δ) ^ gam := by
          rw [Real.rpow_neg (by positivity), Real.div_rpow hδ.le hlenpos.le,
            Real.div_rpow hlenpos.le hδ.le, inv_div]
        rw [h2, h3]
      rw [heval] at hstep
      exact hstep
    have hcast : ((ι.card : ℝ)) ≤ 3 * (2 : ℝ) ^ (m - l) := by
      have h := hcardbound
      have hc : ((ι.card : ℝ)) ≤ ((3 * 2 ^ (m - l) : ℕ) : ℝ) := by exact_mod_cast h
      calc ((ι.card : ℝ)) ≤ ((3 * 2 ^ (m - l) : ℕ) : ℝ) := hc
        _ = 3 * (2 : ℝ) ^ (m - l) := by push_cast; ring
    calc ((ι.card : ℝ)) ≤ 3 * (2 : ℝ) ^ (m - l) := hcast
      _ ≤ 3 * (4 * ((b - a) / δ) ^ gam) := by
          exact mul_le_mul_of_nonneg_left hfinal (by norm_num)
      _ = 12 * ((b - a) / δ) ^ gam := by ring

/-! ### From the spectrum to the Minkowski estimate -/

/-- For a subset of `[1,2]` an upper-spectrum estimate implies the global Minkowski
estimate at the same exponent. -/
theorem hasUpperMinkowskiExponent_of_hasUpperAssouadSpectrumExponent {F : Set ℝ} {θ gam : ℝ}
    (hF : F ⊆ Icc (1 : ℝ) 2) (hθ0 : 0 ≤ θ)
    (h : HasUpperAssouadSpectrumExponent F θ gam) :
    HasUpperMinkowskiExponent F gam := by
  intro ε hε
  obtain ⟨C, hC, hcov⟩ := h
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδone
  have hscale : δ ^ θ ≤ (2 : ℝ) - 1 := by
    have h1 : δ ^ θ ≤ 1 := Real.rpow_le_one hδ.le hδone.le hθ0
    linarith
  obtain ⟨ι, hι, hcard⟩ := hcov δ 1 2 hδ hδone (le_refl _) (by norm_num) (le_refl _) hscale
  refine ⟨ι, ?_, ?_⟩
  · refine IsIntervalCover.mono ?_ hι
    intro x hx
    exact ⟨hx, hF hx⟩
  · refine le_trans hcard ?_
    have hval : ((2 : ℝ) - 1) / δ = δ⁻¹ := by
      norm_num
    rw [hval]
    have hstep : (δ⁻¹ : ℝ) ^ gam ≤ δ ^ (-(gam + ε)) := by
      rw [Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδone.le (by linarith)
    exact mul_le_mul_of_nonneg_left hstep hC.le

/-! ### The dimensions of the Cantor set -/

theorem cantorSet_subset_Icc_one_two {gam : ℝ} (u : ℝ) (hu : 1 ≤ u) (hu2 : u + 1 ≤ 2) :
    cantorSet (cantorRatio gam) u 1 ⊆ Icc (1 : ℝ) 2 := by
  intro x hx
  obtain ⟨h1, h2⟩ := cantorSet_subset_Icc (cantorRatio gam) u 1 hx
  exact ⟨by linarith, by linarith⟩

theorem cantorSet_nonempty {gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1) (u : ℝ) :
    (cantorSet (cantorRatio gam) u 1).Nonempty := by
  refine ⟨u, ?_⟩
  have hmu : 0 < cantorRatio gam := cantorRatio_pos gam
  have hmu2 : cantorRatio gam ≤ 1 / 2 := cantorRatio_le_half hgam hgam1
  refine cantorLeft_subset_cantorSet hmu hmu2 0 (by norm_num : (0:ℝ) ≤ 1) u ?_
  rw [cantorLeft_zero]
  exact Finset.mem_singleton_self _

/-- The upper Assouad spectrum of the Cantor set is its dimension, at every scale
parameter. -/
theorem upperAssouadSpectrum_cantorSet {gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (u : ℝ) (hu : 1 ≤ u) (hu2 : u + 1 ≤ 2) :
    upperAssouadSpectrum (cantorSet (cantorRatio gam) u 1) θ = gam := by
  refine upperAssouadSpectrum_eq_of_bounds hgam.le ?_ ?_
  · -- the covering estimate
    refine ⟨12, by norm_num, ?_⟩
    intro δ a b hδ hδone ha hab hb hscale
    have hb1 : b - a ≤ 1 := by linarith
    have hδscale : δ ≤ b - a := by
      have h1 : δ ≤ δ ^ θ := by
        calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
          _ ≤ δ ^ θ := Real.rpow_le_rpow_of_exponent_ge hδ hδone.le hθ1
      linarith
    obtain ⟨ι, hι, hcard⟩ := cantorSet_assouad_cover hgam hgam1 u hδ hab hδscale hb1
    exact ⟨ι, hι, hcard⟩
  · -- no smaller exponent works
    intro gam' hgam'0 hlt hcon
    have hmink := hasUpperMinkowskiExponent_of_hasUpperAssouadSpectrumExponent
      (cantorSet_subset_Icc_one_two u hu hu2) hθ0 hcon
    exact not_hasUpperMinkowskiExponent_cantorSet hgam hgam1 hgam'0 hlt u hmink

/-- The quasi-Assouad dimension of the Cantor set is its dimension. -/
theorem quasiAssouadDimension_cantorSet {gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1)
    (u : ℝ) (hu : 1 ≤ u) (hu2 : u + 1 ≤ 2) :
    quasiAssouadDimension (cantorSet (cantorRatio gam) u 1) = gam := by
  refine quasiAssouadDimension_eq_of_spectrum ?_ ?_
  · intro θ hθ0 hθ1
    rw [upperAssouadSpectrum_cantorSet hgam hgam1 hθ0 hθ1.le u hu hu2]
  · intro ε hε
    refine ⟨0, le_refl _, one_pos, ?_⟩
    rw [upperAssouadSpectrum_cantorSet hgam hgam1 (le_refl _) (by norm_num) u hu hu2]
    linarith

/-- The upper Minkowski dimension of the Cantor set is its dimension. -/
theorem upperMinkowskiDimension_cantorSet {gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1)
    (u : ℝ) : upperMinkowskiDimension (cantorSet (cantorRatio gam) u 1) = gam := by
  refine upperMinkowskiDimension_eq_of_bounds hgam.le
    (hasUpperMinkowskiExponent_cantorSet hgam hgam1 u) ?_
  intro beta' hbeta'0 hlt
  exact not_hasUpperMinkowskiExponent_cantorSet hgam hgam1 hbeta'0 hlt u

/-- **The Cantor set of dimension `γ` is `(γ,γ)`-quasi-Assouad regular.** -/
theorem isQuasiAssouadRegular_cantorSet {gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1)
    (u : ℝ) (hu : 1 ≤ u) (hu2 : u + 1 ≤ 2) :
    IsQuasiAssouadRegular (cantorSet (cantorRatio gam) u 1) gam gam := by
  refine ⟨upperMinkowskiDimension_cantorSet hgam hgam1 u,
    quasiAssouadDimension_cantorSet hgam hgam1 u hu hu2, Or.inr ?_⟩
  intro θ hθ0 hθ1 _
  exact upperAssouadSpectrum_cantorSet hgam hgam1 hθ0 hθ1.le u hu hu2

/-! ### The trivial example: a single radius -/

theorem hasUpperMinkowskiExponent_singleton (t : ℝ) :
    HasUpperMinkowskiExponent ({t} : Set ℝ) 0 := by
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro δ hδ hδone
  refine ⟨{t}, ?_, ?_⟩
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine Set.mem_iUnion₂.mpr ⟨x, Finset.mem_singleton_self _, ?_⟩
    simp only [Set.mem_Icc]
    constructor <;> linarith
  · simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    have h1 : (1 : ℝ) ≤ δ ^ (-(0 + ε)) := by
      rw [zero_add, Real.rpow_neg hδ.le]
      have hle : δ ^ ε ≤ 1 := Real.rpow_le_one hδ.le hδone.le hε.le
      have hpos : 0 < δ ^ ε := Real.rpow_pos_of_pos hδ ε
      rw [le_inv_comm₀ (by norm_num) hpos]
      simpa using hle
    linarith

theorem hasUpperAssouadSpectrumExponent_singleton (t : ℝ) (θ : ℝ) :
    HasUpperAssouadSpectrumExponent ({t} : Set ℝ) θ 0 := by
  refine ⟨1, one_pos, ?_⟩
  intro δ a b hδ hδone ha hab hb hscale
  refine ⟨{t}, ?_, ?_⟩
  · intro x hx
    obtain ⟨hx1, -⟩ := hx
    rw [Set.mem_singleton_iff] at hx1
    subst hx1
    refine Set.mem_iUnion₂.mpr ⟨x, Finset.mem_singleton_self _, ?_⟩
    simp only [Set.mem_Icc]
    constructor <;> linarith
  · simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    rw [Real.rpow_zero]

theorem isQuasiAssouadRegular_singleton (t : ℝ) :
    IsQuasiAssouadRegular ({t} : Set ℝ) 0 0 := by
  refine ⟨?_, ?_, Or.inl rfl⟩
  · refine upperMinkowskiDimension_eq_of_bounds (le_refl _)
      (hasUpperMinkowskiExponent_singleton t) ?_
    intro beta' hbeta'0 hlt
    exact absurd hlt (not_lt.mpr hbeta'0)
  · refine quasiAssouadDimension_eq_of_spectrum ?_ ?_
    · intro θ hθ0 hθ1
      refine le_of_eq ?_
      refine upperAssouadSpectrum_eq_of_bounds (le_refl _)
        (hasUpperAssouadSpectrumExponent_singleton t θ) ?_
      intro gam' hgam'0 hlt
      exact absurd hlt (not_lt.mpr hgam'0)
    · intro ε hε
      refine ⟨0, le_refl _, one_pos, ?_⟩
      have heq : upperAssouadSpectrum ({t} : Set ℝ) 0 = 0 := by
        refine upperAssouadSpectrum_eq_of_bounds (le_refl _)
          (hasUpperAssouadSpectrumExponent_singleton t 0) ?_
        intro gam' hgam'0 hlt
        exact absurd hlt (not_lt.mpr hgam'0)
      rw [heq]
      linarith

/-! ### The localized covering estimate for a single midpoint set -/

/-- A `len`-separated subset of an interval of length `n * len` has at most `n + 1` points. -/
theorem card_le_succ_of_separated_in_interval {S : Finset ℝ} {s len : ℝ} {n : ℕ} (hlen : 0 < len)
    (hsub : ∀ x ∈ S, x ∈ Icc s (s + (n : ℝ) * len))
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → len ≤ |x - y|) :
    S.card ≤ n + 1 := by
  classical
  have hcard : S.card ≤ (Finset.Icc (0 : ℤ) (n : ℤ)).card := by
    refine Finset.card_le_card_of_injOn (fun x => ⌊(x - s) / len⌋) ?_ ?_
    · intro x hx
      obtain ⟨h1, h2⟩ := hsub x hx
      have hq0 : (0 : ℝ) ≤ (x - s) / len := div_nonneg (by linarith) hlen.le
      have hqn : (x - s) / len ≤ (n : ℝ) := by
        rw [div_le_iff₀ hlen]
        linarith
      refine Finset.mem_Icc.mpr ⟨Int.le_floor.mpr (by simpa using hq0), ?_⟩
      have hfl := Int.floor_le_floor hqn
      simpa using hfl
    · intro x hx y hy hxy
      by_contra hne
      have hfx : ((⌊(x - s) / len⌋ : ℝ)) ≤ (x - s) / len := Int.floor_le _
      have hfy : ((⌊(y - s) / len⌋ : ℝ)) ≤ (y - s) / len := Int.floor_le _
      have hfx' : (x - s) / len < (⌊(x - s) / len⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have hfy' : (y - s) / len < (⌊(y - s) / len⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have hxy' : ⌊(x - s) / len⌋ = ⌊(y - s) / len⌋ := hxy
      rw [hxy'] at hfx hfx'
      have hdiff : |(x - s) / len - (y - s) / len| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      have hlenne : len ≠ 0 := hlen.ne'
      have hxydiv : (x - s) / len - (y - s) / len = (x - y) / len := by
        field_simp
        ring
      rw [hxydiv, abs_div, abs_of_pos hlen, div_lt_one hlen] at hdiff
      exact absurd (hsep x hx y hy hne) (not_le.mpr hdiff)
  simpa using hcard

set_option maxHeartbeats 2000000 in
/-- The Assouad-type covering estimate for the finite midpoint sets: inside every interval
shorter than the ambient one, the `m`-th generation midpoints are covered by at most
`12 (|I|/δ)^γ` intervals of length `δ`. -/
theorem cantorMid_assouad_cover {gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1) (m : ℕ)
    (u : ℝ) {L : ℝ} (hL : 0 < L) {δ a b : ℝ} (hδ : 0 < δ) (hlen : δ ≤ b - a)
    (hbL : b - a ≤ L) :
    ∃ ι : Finset ℝ,
      IsIntervalCover ((↑(cantorMid (cantorRatio gam) m u L) : Set ℝ) ∩ Icc a b) δ ι ∧
        (ι.card : ℝ) ≤ 16 * ((b - a) / δ) ^ gam := by
  classical
  set mu : ℝ := cantorRatio gam with hmudef
  have hmu : 0 < mu := cantorRatio_pos gam
  have hmu2 : mu ≤ 1 / 2 := cantorRatio_le_half hgam hgam1
  have hmulone : mu < 1 := lt_of_le_of_lt hmu2 (by norm_num)
  have htpos : 0 < b - a := lt_of_lt_of_le hδ hlen
  have hab : a ≤ b := by linarith
  -- the fine generation
  obtain ⟨j, hjm, hjcov, hjlow⟩ : ∃ j : ℕ, j ≤ m ∧
      (∀ x ∈ cantorMid mu m u L, ∃ y ∈ cantorMid mu j u L, |x - y| ≤ δ / 2) ∧
        mu * δ ≤ mu ^ j * L := by
    by_cases hcase : mu ^ m * L ≤ δ
    · have hex : ∃ n : ℕ, mu ^ n * L ≤ δ := ⟨m, hcase⟩
      set j : ℕ := Nat.find hex with hjdef
      have hjspec : mu ^ j * L ≤ δ := Nat.find_spec hex
      have hjm : j ≤ m := Nat.find_le hcase
      refine ⟨j, hjm, ?_, ?_⟩
      · intro x hx
        exact cantorMid_cover hmu hmu2 j m hjm u L δ hL.le hjspec x hx
      · rcases Nat.eq_zero_or_pos j with h0 | hpos
        · rw [h0]
          simp only [pow_zero, one_mul]
          nlinarith [hδ, hlen, hbL, hmulone, hmu]
        · have hprev : ¬ (mu ^ (j - 1) * L ≤ δ) := Nat.find_min hex (by omega)
          have hprevlt : δ < mu ^ (j - 1) * L := not_le.mp hprev
          have hsucc : mu ^ j = mu * mu ^ (j - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          rw [hsucc]
          calc mu * δ ≤ mu * (mu ^ (j - 1) * L) := by
                exact mul_le_mul_of_nonneg_left hprevlt.le hmu.le
            _ = mu * mu ^ (j - 1) * L := by ring
    · refine ⟨m, le_refl _, fun x hx => ⟨x, hx, ?_⟩, ?_⟩
      · simp only [sub_self, abs_zero]
        linarith
      · have hgt : δ < mu ^ m * L := not_le.mp hcase
        nlinarith [hmu, hmulone, hδ]
  have hjpow : 0 < mu ^ j * L := mul_pos (pow_pos hmu j) hL
  -- the coarse generation
  have hexl : ∃ n : ℕ, mu ^ n * L < b - a := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos htpos hL) hmulone
    exact ⟨n, by rw [lt_div_iff₀ hL] at hn; linarith⟩
  set l1 : ℕ := Nat.find hexl with hl1def
  have hl1spec : mu ^ l1 * L < b - a := Nat.find_spec hexl
  have hl1pos : 0 < l1 := by
    rcases Nat.eq_zero_or_pos l1 with h0 | h
    · rw [h0] at hl1spec
      simp only [pow_zero, one_mul] at hl1spec
      linarith
    · exact h
  set l : ℕ := l1 - 1 with hldef
  have hlge : b - a ≤ mu ^ l * L := by
    have hprev : ¬ (mu ^ l * L < b - a) := by
      rw [hldef]
      exact Nat.find_min hexl (by omega)
    exact not_lt.mp hprev
  have hlsucc : mu ^ (l + 1) * L < b - a := by
    have : l + 1 = l1 := by omega
    rw [this]
    exact hl1spec
  have hlpow : 0 < mu ^ l * L := mul_pos (pow_pos hmu l) hL
  -- the candidate cover
  set ι : Finset ℝ := (cantorMid mu j u L).filter
    (fun c => a - δ / 2 ≤ c ∧ c ≤ b + δ / 2) with hιdef
  have hcover : IsIntervalCover ((↑(cantorMid mu m u L) : Set ℝ) ∩ Icc a b) δ ι := by
    intro x hx
    obtain ⟨hxmid, hxab⟩ := hx
    obtain ⟨y, hy, hdist⟩ := hjcov x hxmid
    simp only [Set.mem_Icc] at hxab
    have habs := abs_le.mp hdist
    refine Set.mem_iUnion₂.mpr ⟨y, ?_, ?_⟩
    · rw [hιdef, Finset.mem_filter]
      refine ⟨hy, ?_, ?_⟩
      · linarith [habs.1, habs.2, hxab.1]
      · linarith [habs.1, habs.2, hxab.2]
    · simp only [Set.mem_Icc]
      constructor <;> linarith [habs.1, habs.2]
  refine ⟨ι, hcover, ?_⟩
  have hge1 : (1 : ℝ) ≤ (b - a) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have hrpowge1 : (1 : ℝ) ≤ ((b - a) / δ) ^ gam := Real.one_le_rpow hge1 hgam.le
  rcases Nat.lt_or_ge j l with hjl | hlj
  · -- the interval is much shorter than the generation intervals: few centers
    have hsep : ∀ x ∈ ι, ∀ y ∈ ι, x ≠ y → mu ^ j * L ≤ |x - y| := by
      intro x hx y hy hxy
      rw [hιdef, Finset.mem_filter] at hx hy
      exact cantorMid_separated hmu hmu2 j hL.le hx.1 hy.1 hxy
    have hsub : ∀ x ∈ ι, x ∈ Icc (a - δ / 2) (a - δ / 2 + 2 * (mu ^ j * L)) := by
      intro x hx
      rw [hιdef, Finset.mem_filter] at hx
      obtain ⟨-, h1, h2⟩ := hx
      have hlgt : mu ^ l * L < mu ^ j * L := by
        have := (pow_lt_pow_iff_right_of_lt_one₀ hmu hmulone).2 hjl
        exact mul_lt_mul_of_pos_right this hL
      simp only [Set.mem_Icc]
      refine ⟨h1, ?_⟩
      have hdt : b - a ≤ mu ^ j * L := le_trans hlge hlgt.le
      have hδle : δ ≤ mu ^ j * L := le_trans hlen hdt
      linarith
    have hcard3 : ι.card ≤ 3 :=
      card_le_three_of_separated_in_interval hjpow hsub hsep
    calc ((ι.card : ℝ)) ≤ 3 := by exact_mod_cast hcard3
      _ ≤ 16 * ((b - a) / δ) ^ gam := by nlinarith [hrpowge1]
  · -- the ancestor count
    set A : Finset ℝ := (cantorMid mu l u L).filter
      (fun c' => a - mu ^ l * L ≤ c' ∧ c' ≤ b + mu ^ l * L) with hAdef
    have hAcard : A.card ≤ 4 := by
      refine card_le_succ_of_separated_in_interval (s := a - mu ^ l * L) (n := 3)
        (len := mu ^ l * L) hlpow ?_ ?_
      · intro x hx
        rw [hAdef, Finset.mem_filter] at hx
        obtain ⟨-, h1, h2⟩ := hx
        simp only [Set.mem_Icc]
        refine ⟨h1, ?_⟩
        push_cast
        linarith [hlge]
      · intro x hx y hy hxy
        rw [hAdef, Finset.mem_filter] at hx hy
        exact cantorMid_separated hmu hmu2 l hL.le hx.1 hy.1 hxy
    have hsubset : ι ⊆ A.biUnion (fun c' => cantorMid mu (j - l) (c' - mu ^ l * L / 2)
        (mu ^ l * L)) := by
      intro c hc
      rw [hιdef, Finset.mem_filter] at hc
      obtain ⟨hcmid, hc1, hc2⟩ := hc
      obtain ⟨c', hc', hcpiece, hdist⟩ :=
        exists_ancestor_cantorMid hmu hmu2 hlj hL.le hcmid
      refine Finset.mem_biUnion.mpr ⟨c', ?_, hcpiece⟩
      rw [hAdef, Finset.mem_filter]
      have habs := abs_le.mp hdist
      have hjle : mu ^ j * L ≤ mu ^ l * L := by
        refine mul_le_mul_of_nonneg_right ?_ hL.le
        exact pow_le_pow_of_le_one hmu.le hmulone.le hlj
      have hδle : δ ≤ mu ^ l * L := by
        calc δ ≤ b - a := hlen
          _ ≤ mu ^ l * L := hlge
      refine ⟨hc', ?_, ?_⟩
      · linarith [habs.1, habs.2]
      · linarith [habs.1, habs.2]
    have hcardbound : ι.card ≤ 4 * 2 ^ (j - l) := by
      have hstep1 : ι.card ≤ (A.biUnion (fun c' => cantorMid mu (j - l) (c' - mu ^ l * L / 2)
          (mu ^ l * L))).card := Finset.card_le_card hsubset
      have hstep2 : (A.biUnion (fun c' => cantorMid mu (j - l) (c' - mu ^ l * L / 2)
          (mu ^ l * L))).card ≤ ∑ c' ∈ A, (cantorMid mu (j - l) (c' - mu ^ l * L / 2)
            (mu ^ l * L)).card := Finset.card_biUnion_le
      have hstep3 : ∑ c' ∈ A, (cantorMid mu (j - l) (c' - mu ^ l * L / 2)
          (mu ^ l * L)).card = A.card * 2 ^ (j - l) := by
        rw [Finset.sum_congr rfl (fun c' _ => cantorMid_card hmu hmu2 (j - l) hlpow)]
        rw [Finset.sum_const, smul_eq_mul]
      calc ι.card ≤ ∑ c' ∈ A, (cantorMid mu (j - l) (c' - mu ^ l * L / 2)
            (mu ^ l * L)).card := le_trans hstep1 hstep2
        _ = A.card * 2 ^ (j - l) := hstep3
        _ ≤ 4 * 2 ^ (j - l) := Nat.mul_le_mul_right _ hAcard
    -- the numerical bound
    have hsplit : mu ^ (j - l) * mu ^ l = mu ^ j := by
      rw [← pow_add]
      congr 1
      omega
    have hratio : mu ^ 2 * δ / (b - a) < mu ^ (j - l) := by
      rw [div_lt_iff₀ htpos]
      have hupbd : mu ^ l * L * mu < b - a := by
        calc mu ^ l * L * mu = mu ^ (l + 1) * L := by rw [pow_succ]; ring
          _ < b - a := hlsucc
      have hkey : mu ^ (j - l) * (mu ^ l * L * mu) < mu ^ (j - l) * (b - a) :=
        mul_lt_mul_of_pos_left hupbd (pow_pos hmu (j - l))
      have hid : mu ^ (j - l) * (mu ^ l * L * mu) = mu ^ j * L * mu := by
        calc mu ^ (j - l) * (mu ^ l * L * mu) = (mu ^ (j - l) * mu ^ l) * L * mu := by ring
          _ = mu ^ j * L * mu := by rw [hsplit]
      rw [hid] at hkey
      have hlow2 : mu ^ 2 * δ ≤ mu ^ j * L * mu := by
        calc mu ^ 2 * δ = mu * (mu * δ) := by ring
          _ ≤ mu * (mu ^ j * L) := mul_le_mul_of_nonneg_left hjlow hmu.le
          _ = mu ^ j * L * mu := by ring
      linarith
    have hfinal : ((2 : ℝ) ^ (j - l)) ≤ 4 * ((b - a) / δ) ^ gam := by
      have hpow : ((2 : ℝ) ^ (j - l)) = ((mu ^ (j - l)) ^ (-gam)) := by
        rw [hmudef, cantorRatio_pow_rpow_neg hgam (j - l)]
      rw [hpow]
      have hposq : (0 : ℝ) < mu ^ 2 * δ / (b - a) := by positivity
      have hstep : (mu ^ (j - l)) ^ (-gam) ≤ (mu ^ 2 * δ / (b - a)) ^ (-gam) :=
        le_of_lt (Real.rpow_lt_rpow_of_neg hposq hratio (by linarith))
      have heval : (mu ^ 2 * δ / (b - a)) ^ (-gam) = 4 * ((b - a) / δ) ^ gam := by
        have h1 : mu ^ 2 * δ / (b - a) = (mu ^ 2) * (δ / (b - a)) := by ring
        rw [h1, Real.mul_rpow (by positivity) (by positivity)]
        have h2 : ((mu ^ 2 : ℝ)) ^ (-gam) = 4 := by
          rw [hmudef, cantorRatio_pow_rpow_neg hgam 2]
          norm_num
        have h3 : ((δ / (b - a)) : ℝ) ^ (-gam) = ((b - a) / δ) ^ gam := by
          rw [Real.rpow_neg (by positivity), Real.div_rpow hδ.le htpos.le,
            Real.div_rpow htpos.le hδ.le, inv_div]
        rw [h2, h3]
      rw [heval] at hstep
      exact hstep
    have hcast : ((ι.card : ℝ)) ≤ 4 * (2 : ℝ) ^ (j - l) := by
      have hc : ((ι.card : ℝ)) ≤ ((4 * 2 ^ (j - l) : ℕ) : ℝ) := by exact_mod_cast hcardbound
      calc ((ι.card : ℝ)) ≤ ((4 * 2 ^ (j - l) : ℕ) : ℝ) := hc
        _ = 4 * (2 : ℝ) ^ (j - l) := by push_cast; ring
    calc ((ι.card : ℝ)) ≤ 4 * (2 : ℝ) ^ (j - l) := hcast
      _ ≤ 4 * (4 * ((b - a) / δ) ^ gam) := mul_le_mul_of_nonneg_left hfinal (by norm_num)
      _ = 16 * ((b - a) / δ) ^ gam := by ring

/-! ## The off-diagonal regular examples

For `0 < β < γ ≤ 1` the example of §6.2 of the paper is a union of Cantor midpoint sets placed in
intervals whose lengths decay geometrically.  The `j`-th piece is the generation `k₀ j` of the
Cantor construction of dimension `γ` inside an interval of length `Lⱼ = 4⁻¹ρ^{k₀ j}`, where
`ρ = 2^{-(1/β - 1/γ)}`.  Then the `j`-th piece consists of `2^{k₀ j}` points at separation
`σⱼ = 4⁻¹2^{-k₀ j/β}`, so that

* `2^{k₀ j} = (4σⱼ)^{-β}`  (the Minkowski dimension is `β`), and
* `Lⱼ = 4⁻¹(4σⱼ)^{1 - β/γ}` (the Assouad spectrum reaches `γ` at `θ > 1 - β/γ`).

The step `k₀` is any natural number with `ρ^{k₀} ≤ 1/3`; this makes the intervals disjoint. -/

/-- The gap exponent `1/β - 1/γ` of an off-diagonal pair. -/
def offDiagGap (beta gam : ℝ) : ℝ := 1 / beta - 1 / gam

/-- The geometric ratio of the piece lengths at unit step. -/
def offDiagRatio (beta gam : ℝ) : ℝ := (2 : ℝ) ^ (-offDiagGap beta gam)

/-- The length of the `j`-th piece. -/
def offDiagLen (beta gam : ℝ) (k0 j : ℕ) : ℝ :=
  (1 / 4) * (offDiagRatio beta gam) ^ (k0 * j)

/-- The `j`-th piece of the off-diagonal example. -/
def offDiagPiece (beta gam : ℝ) (k0 j : ℕ) : Finset ℝ :=
  cantorMid (cantorRatio gam) (k0 * j) (1 + 2 * offDiagLen beta gam k0 j)
    (offDiagLen beta gam k0 j)

/-- The off-diagonal example itself. -/
def offDiagSet (beta gam : ℝ) (k0 : ℕ) : Set ℝ :=
  ⋃ j : ℕ, (↑(offDiagPiece beta gam k0 j) : Set ℝ)

/-- The separation of the points of the `j`-th piece. -/
def offDiagSep (beta gam : ℝ) (k0 j : ℕ) : ℝ :=
  (cantorRatio gam) ^ (k0 * j) * offDiagLen beta gam k0 j

theorem offDiagGap_pos {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam) :
    0 < offDiagGap beta gam := by
  rw [offDiagGap, sub_pos]
  exact one_div_lt_one_div_of_lt hbeta hbg

theorem offDiagRatio_pos (beta gam : ℝ) : 0 < offDiagRatio beta gam :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem offDiagRatio_lt_one {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam) :
    offDiagRatio beta gam < 1 := by
  rw [offDiagRatio]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  simpa using offDiagGap_pos hbeta hbg

theorem offDiagLen_pos {beta gam : ℝ} (k0 j : ℕ) : 0 < offDiagLen beta gam k0 j := by
  rw [offDiagLen]
  have := offDiagRatio_pos beta gam
  positivity

theorem offDiagLen_le_quarter {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam) (k0 j : ℕ) :
    offDiagLen beta gam k0 j ≤ 1 / 4 := by
  have h1 : (offDiagRatio beta gam) ^ (k0 * j) ≤ 1 :=
    pow_le_one₀ (offDiagRatio_pos beta gam).le (offDiagRatio_lt_one hbeta hbg).le
  have h2 : 0 < (offDiagRatio beta gam) ^ (k0 * j) := pow_pos (offDiagRatio_pos beta gam) _
  rw [offDiagLen]
  nlinarith [h1, h2]

/-- With a step for which the ratio drops below `1/3`, consecutive pieces are well separated. -/
theorem offDiagLen_succ {beta gam : ℝ} {k0 : ℕ}
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) (j : ℕ) :
    3 * offDiagLen beta gam k0 (j + 1) ≤ offDiagLen beta gam k0 j := by
  have hpos : 0 < offDiagRatio beta gam := offDiagRatio_pos beta gam
  have hstep : (offDiagRatio beta gam) ^ (k0 * (j + 1)) =
      (offDiagRatio beta gam) ^ (k0 * j) * (offDiagRatio beta gam) ^ k0 := by
    rw [← pow_add]
    congr 1
  rw [offDiagLen, offDiagLen, hstep]
  have hjpos : 0 < (offDiagRatio beta gam) ^ (k0 * j) := pow_pos hpos _
  nlinarith [hk0, hjpos]

theorem offDiagPiece_subset_Icc {beta gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1)
    (k0 j : ℕ) :
    ∀ x ∈ offDiagPiece beta gam k0 j,
      1 + 2 * offDiagLen beta gam k0 j ≤ x ∧ x ≤ 1 + 3 * offDiagLen beta gam k0 j := by
  intro x hx
  have hmu : 0 < cantorRatio gam := cantorRatio_pos gam
  have hmu2 : cantorRatio gam ≤ 1 / 2 := cantorRatio_le_half hgam hgam1
  obtain ⟨h1, h2⟩ := cantorMid_mem_bounds hmu hmu2 (k0 * j) (offDiagLen_pos k0 j).le hx
  have hpow : 0 ≤ (cantorRatio gam) ^ (k0 * j) * offDiagLen beta gam k0 j / 2 := by
    have := (offDiagLen_pos (beta := beta) (gam := gam) k0 j).le
    positivity
  exact ⟨by linarith, by linarith⟩

theorem offDiagSet_subset_Icc {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam : 0 < gam) (hgam1 : gam ≤ 1) (k0 : ℕ) :
    offDiagSet beta gam k0 ⊆ Icc (1 : ℝ) 2 := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨h1, h2⟩ := offDiagPiece_subset_Icc hgam hgam1 k0 j x hj
  have hlen := offDiagLen_le_quarter hbeta hbg k0 j
  have hlenpos := offDiagLen_pos (beta := beta) (gam := gam) k0 j
  exact ⟨by linarith, by linarith⟩

theorem offDiagSet_nonempty {beta gam : ℝ} (k0 : ℕ) : (offDiagSet beta gam k0).Nonempty := by
  obtain ⟨x, hx⟩ := cantorMid_nonempty (cantorRatio gam) (k0 * 0)
    (1 + 2 * offDiagLen beta gam k0 0) (offDiagLen beta gam k0 0)
  exact ⟨x, Set.mem_iUnion.mpr ⟨0, hx⟩⟩

/-! ### The two exponent relations -/

theorem offDiagSep_pos {beta gam : ℝ} (k0 j : ℕ) : 0 < offDiagSep beta gam k0 j := by
  rw [offDiagSep]
  have h1 : 0 < (cantorRatio gam) ^ (k0 * j) := pow_pos (cantorRatio_pos gam) _
  have h2 := offDiagLen_pos (beta := beta) (gam := gam) k0 j
  positivity

/-- The separation of the `j`-th piece is `4⁻¹ 2^{-k₀ j/β}`. -/
theorem offDiagSep_eq {beta gam : ℝ} (hbeta : 0 < beta) (hgam : 0 < gam) (k0 j : ℕ) :
    offDiagSep beta gam k0 j = (1 / 4) * (2 : ℝ) ^ (-((k0 * j : ℕ) : ℝ) / beta) := by
  have h1 : (cantorRatio gam) ^ (k0 * j) = (2 : ℝ) ^ (-((k0 * j : ℕ) : ℝ) / gam) := by
    rw [cantorRatio, ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / gam))) (k0 * j),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    field_simp
  have h2 : (offDiagRatio beta gam) ^ (k0 * j)
      = (2 : ℝ) ^ (-((k0 * j : ℕ) : ℝ) * offDiagGap beta gam) := by
    rw [offDiagRatio, ← Real.rpow_natCast ((2 : ℝ) ^ (-offDiagGap beta gam)) (k0 * j),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [offDiagSep, offDiagLen, h1, h2]
  rw [show (2 : ℝ) ^ (-((k0 * j : ℕ) : ℝ) / gam) *
        ((1 / 4) * (2 : ℝ) ^ (-((k0 * j : ℕ) : ℝ) * offDiagGap beta gam))
      = (1 / 4) * ((2 : ℝ) ^ (-((k0 * j : ℕ) : ℝ) / gam) *
        (2 : ℝ) ^ (-((k0 * j : ℕ) : ℝ) * offDiagGap beta gam)) by ring]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 2
  rw [offDiagGap]
  field_simp
  ring

/-! ### Two geometric sums -/

/-- A sum of increasing geometric terms, each below a threshold, is at most twice the
threshold. -/
theorem sum_ite_geom_incr_le {r M : ℝ} (hr : 2 ≤ r) (hM : 0 ≤ M) (J : ℕ) :
    ∑ j ∈ Finset.range J, (if r ^ j ≤ M then r ^ j else 0) ≤ 2 * M := by
  classical
  have hr0 : (0 : ℝ) < r := by linarith
  set S := (Finset.range J).filter (fun j => r ^ j ≤ M) with hS
  have hsum : ∑ j ∈ Finset.range J, (if r ^ j ≤ M then r ^ j else 0) = ∑ j ∈ S, r ^ j := by
    rw [hS, Finset.sum_filter]
  rw [hsum]
  rcases S.eq_empty_or_nonempty with hempty | hne
  · rw [hempty, Finset.sum_empty]
    linarith
  · set jstar := S.max' hne with hjs
    have hjstar : r ^ jstar ≤ M := by
      have hmem := S.max'_mem hne
      simp only [hS, Finset.mem_filter] at hmem
      exact hmem.2
    have hsub : S ⊆ Finset.range (jstar + 1) := by
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' S j hj))
    have hstep : ∑ j ∈ S, r ^ j ≤ ∑ j ∈ Finset.range (jstar + 1), r ^ j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    have hgeom : ∑ j ∈ Finset.range (jstar + 1), r ^ j ≤ 2 * r ^ jstar := by
      rw [geom_sum_eq (by linarith : r ≠ 1)]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < r - 1)]
      have hpos : (0 : ℝ) < r ^ jstar := by positivity
      have hsucc : r ^ (jstar + 1) = r ^ jstar * r := by rw [pow_succ]
      rw [hsucc]
      nlinarith [hpos]
    calc ∑ j ∈ S, r ^ j ≤ ∑ j ∈ Finset.range (jstar + 1), r ^ j := hstep
      _ ≤ 2 * r ^ jstar := hgeom
      _ ≤ 2 * M := by linarith

/-- A sum of decreasing geometric terms, each below a threshold, is controlled by the
threshold. -/
theorem sum_ite_geom_decr_le {q M : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hM : 0 ≤ M) (J : ℕ) :
    ∑ j ∈ Finset.range J, (if q ^ j ≤ M then q ^ j else 0) ≤ M / (1 - q) := by
  classical
  set S := (Finset.range J).filter (fun j => q ^ j ≤ M) with hS
  have hsum : ∑ j ∈ Finset.range J, (if q ^ j ≤ M then q ^ j else 0) = ∑ j ∈ S, q ^ j := by
    rw [hS, Finset.sum_filter]
  rw [hsum]
  rcases S.eq_empty_or_nonempty with hempty | hne
  · rw [hempty, Finset.sum_empty]
    positivity
  · set j0 := S.min' hne with hj0
    have hj0mem : q ^ j0 ≤ M := by
      have hmem := S.min'_mem hne
      simp only [hS, Finset.mem_filter] at hmem
      exact hmem.2
    have hsub : S ⊆ Finset.Ico j0 J := by
      intro j hj
      refine Finset.mem_Ico.mpr ⟨Finset.min'_le S j hj, ?_⟩
      simp only [hS, Finset.mem_filter, Finset.mem_range] at hj
      exact hj.1
    have hstep : ∑ j ∈ S, q ^ j ≤ ∑ j ∈ Finset.Ico j0 J, q ^ j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    have hshift : ∑ j ∈ Finset.Ico j0 J, q ^ j =
        q ^ j0 * ∑ i ∈ Finset.range (J - j0), q ^ i := by
      rw [Finset.mul_sum]
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]
    have hgeom : ∑ i ∈ Finset.range (J - j0), q ^ i ≤ 1 / (1 - q) := by
      have h1q : (0 : ℝ) < 1 - q := by linarith
      have hqpow : (0 : ℝ) < q ^ (J - j0) := by positivity
      rw [geom_sum_eq (by linarith : q ≠ 1)]
      have hid : (q ^ (J - j0) - 1) / (q - 1) = (1 - q ^ (J - j0)) / (1 - q) := by
        rw [div_eq_div_iff (by linarith : q - 1 ≠ 0) (by linarith : (1 : ℝ) - q ≠ 0)]
        ring
      rw [hid, div_le_div_iff₀ h1q h1q]
      nlinarith [hqpow]
    have hqpow0 : (0 : ℝ) < q ^ j0 := by positivity
    calc ∑ j ∈ S, q ^ j ≤ ∑ j ∈ Finset.Ico j0 J, q ^ j := hstep
      _ = q ^ j0 * ∑ i ∈ Finset.range (J - j0), q ^ i := hshift
      _ ≤ q ^ j0 * (1 / (1 - q)) := by
          exact mul_le_mul_of_nonneg_left hgeom hqpow0.le
      _ ≤ M * (1 / (1 - q)) := by
          apply mul_le_mul_of_nonneg_right hj0mem
          positivity
      _ = M / (1 - q) := by ring

/-! ### The two exponent identities and the per-piece covers -/

/-- The number of points of the `j`-th piece is `(4σⱼ)^{-β}`. -/
theorem offDiagCount_eq {beta gam : ℝ} (hbeta : 0 < beta) (hgam : 0 < gam) (k0 j : ℕ) :
    (4 * offDiagSep beta gam k0 j) ^ (-beta) = (2 : ℝ) ^ (k0 * j) := by
  have h4 : 4 * offDiagSep beta gam k0 j = (2 : ℝ) ^ (-((k0 * j : ℕ) : ℝ) / beta) := by
    rw [offDiagSep_eq hbeta hgam]
    ring
  rw [h4, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show -((k0 * j : ℕ) : ℝ) / beta * -beta = ((k0 * j : ℕ) : ℝ) by field_simp]
  rw [Real.rpow_natCast]

/-- The length of the `j`-th piece is `4⁻¹(4σⱼ)^{1-β/γ}`. -/
theorem offDiagRatioPow_eq {beta gam : ℝ} (hbeta : 0 < beta) (hgam : 0 < gam) (k0 j : ℕ) :
    (offDiagRatio beta gam) ^ (k0 * j) = (4 * offDiagSep beta gam k0 j) ^ (1 - beta / gam) := by
  have h4 : 4 * offDiagSep beta gam k0 j = (2 : ℝ) ^ (-((k0 * j : ℕ) : ℝ) / beta) := by
    rw [offDiagSep_eq hbeta hgam]
    ring
  have hleft : (offDiagRatio beta gam) ^ (k0 * j)
      = (2 : ℝ) ^ (-((k0 * j : ℕ) : ℝ) * offDiagGap beta gam) := by
    rw [offDiagRatio, ← Real.rpow_natCast ((2 : ℝ) ^ (-offDiagGap beta gam)) (k0 * j),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [hleft, h4, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  rw [offDiagGap]
  field_simp

/-! ### The per-piece covers -/

theorem offDiagPiece_card {beta gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1) (k0 j : ℕ) :
    (offDiagPiece beta gam k0 j).card = 2 ^ (k0 * j) :=
  cantorMid_card (cantorRatio_pos gam) (cantorRatio_le_half hgam hgam1) _
    (offDiagLen_pos (beta := beta) (gam := gam) k0 j)

/-- The points of the piece cover it at any scale. -/
theorem offDiagPiece_cover_self {beta gam : ℝ} (k0 j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IsIntervalCover (↑(offDiagPiece beta gam k0 j) : Set ℝ) δ (offDiagPiece beta gam k0 j) := by
  intro x hx
  refine Set.mem_iUnion₂.mpr ⟨x, hx, ?_⟩
  simp only [Set.mem_Icc]
  constructor <;> linarith

/-- Below the length of the piece the Assouad cover applies. -/
theorem offDiagPiece_cover_assouad {beta gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1) (k0 j : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hδL : δ ≤ offDiagLen beta gam k0 j) :
    ∃ ι : Finset ℝ, IsIntervalCover (↑(offDiagPiece beta gam k0 j) : Set ℝ) δ ι ∧
      (ι.card : ℝ) ≤ 16 * (offDiagLen beta gam k0 j / δ) ^ gam := by
  have hLpos : 0 < offDiagLen beta gam k0 j := offDiagLen_pos k0 j
  have hdiff : (1 + 3 * offDiagLen beta gam k0 j) - (1 + 2 * offDiagLen beta gam k0 j)
      = offDiagLen beta gam k0 j := by ring
  obtain ⟨ι, hι, hcard⟩ := cantorMid_assouad_cover hgam hgam1 (k0 * j)
    (1 + 2 * offDiagLen beta gam k0 j) hLpos (δ := δ)
    (a := 1 + 2 * offDiagLen beta gam k0 j) (b := 1 + 3 * offDiagLen beta gam k0 j)
    hδ (by rw [hdiff]; exact hδL) (by rw [hdiff])
  rw [hdiff] at hcard
  refine ⟨ι, ?_, hcard⟩
  refine IsIntervalCover.mono ?_ hι
  intro x hx
  refine ⟨hx, ?_⟩
  obtain ⟨h1, h2⟩ := offDiagPiece_subset_Icc hgam hgam1 k0 j x hx
  exact ⟨h1, h2⟩

/-- The piece lengths are antitone in the index. -/
theorem offDiagLen_antitone {beta gam : ℝ} {k0 : ℕ}
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) (i : ℕ) :
    ∀ j : ℕ, i ≤ j → offDiagLen beta gam k0 j ≤ offDiagLen beta gam k0 i := by
  intro j
  induction j with
  | zero =>
      intro h
      have hi : i = 0 := by omega
      rw [hi]
  | succ j ih =>
      intro h
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · have hij : i ≤ j := by omega
        have hstep : offDiagLen beta gam k0 (j + 1) ≤ offDiagLen beta gam k0 j := by
          have h3 := offDiagLen_succ hk0 j
          have hpos := offDiagLen_pos (beta := beta) (gam := gam) k0 (j + 1)
          linarith
        exact le_trans hstep (ih hij)
      · have hi : i = j + 1 := by omega
        rw [hi]

/-- The pieces of index at least `J` all lie in `[1, 1 + 3 δ]` as soon as `L_J ≤ δ`. -/
theorem offDiagPiece_near_one {beta gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1)
    {k0 : ℕ} (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) {J j : ℕ} (hJj : J ≤ j)
    {δ : ℝ} (hδ : offDiagLen beta gam k0 J ≤ δ) :
    ∀ x ∈ offDiagPiece beta gam k0 j, 1 ≤ x ∧ x ≤ 1 + 3 * δ := by
  intro x hx
  obtain ⟨h1, h2⟩ := offDiagPiece_subset_Icc hgam hgam1 k0 j x hx
  have hmono := offDiagLen_antitone hk0 J j hJj
  have hlenpos := offDiagLen_pos (beta := beta) (gam := gam) k0 j
  exact ⟨by linarith, by linarith⟩

/-- Three intervals of length `δ` cover `[1, 1 + 3 δ]`. -/
theorem cover_near_one {δ : ℝ} (_hδ : 0 < δ) {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 1 + 3 * δ) :
    x ∈ ⋃ c ∈ ({1 + δ / 2, 1 + 3 * δ / 2, 1 + 5 * δ / 2} : Finset ℝ),
      Icc (c - δ / 2) (c + δ / 2) := by
  rcases le_or_gt x (1 + δ) with hc1 | hc1
  · refine Set.mem_iUnion₂.mpr ⟨1 + δ / 2, by simp, ?_⟩
    simp only [Set.mem_Icc]
    constructor <;> linarith
  · rcases le_or_gt x (1 + 2 * δ) with hc2 | hc2
    · refine Set.mem_iUnion₂.mpr ⟨1 + 3 * δ / 2, by simp, ?_⟩
      simp only [Set.mem_Icc]
      constructor <;> linarith
    · refine Set.mem_iUnion₂.mpr ⟨1 + 5 * δ / 2, by simp, ?_⟩
      simp only [Set.mem_Icc]
      constructor <;> linarith

/-! ### The two pointwise comparisons -/

/-- Commuting a real power past two natural powers. -/
theorem rpow_pow_comm {x : ℝ} (hx : 0 < x) (y : ℝ) (a b : ℕ) :
    ((x ^ a) ^ y) ^ b = (x ^ (a * b)) ^ y := by
  have e1 : (x ^ a : ℝ) = x ^ ((a : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
  have e2 : (x ^ (a * b) : ℝ) = x ^ (((a * b : ℕ)) : ℝ) := (Real.rpow_natCast _ _).symm
  calc ((x ^ a) ^ y) ^ b = (x ^ ((a : ℝ) * y)) ^ b := by
        rw [e1, ← Real.rpow_mul hx.le]
    _ = x ^ ((a : ℝ) * y * (b : ℝ)) := by
        rw [← Real.rpow_natCast (x ^ ((a : ℝ) * y)) b, ← Real.rpow_mul hx.le]
    _ = (x ^ (((a * b : ℕ)) : ℝ)) ^ y := by
        rw [← Real.rpow_mul hx.le]
        congr 1
        push_cast
        ring
    _ = (x ^ (a * b)) ^ y := by rw [← e2]

/-- Above the separation scale the number of points is controlled by `(4δ)^{-β}`. -/
theorem offDiagCount_le_of_le_sep {beta gam : ℝ} (hbeta : 0 < beta) (hgam : 0 < gam)
    (k0 j : ℕ) {δ : ℝ} (hδ : 0 < δ) (hσ : δ ≤ offDiagSep beta gam k0 j) :
    ((2 : ℝ) ^ k0) ^ j ≤ (4 * δ) ^ (-beta) := by
  rw [← pow_mul, ← offDiagCount_eq hbeta hgam k0 j]
  have h4 : 4 * δ ≤ 4 * offDiagSep beta gam k0 j := by linarith
  rcases eq_or_lt_of_le h4 with heq | hlt
  · rw [heq]
  · exact le_of_lt (Real.rpow_lt_rpow_of_neg (by positivity) hlt (by linarith))

/-- Below the separation scale the piece length is controlled by `(4δ)^{γ-β}`. -/
theorem offDiagLenPow_le_of_sep_lt {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta ≤ gam)
    (hgam : 0 < gam) (k0 j : ℕ) {δ : ℝ} (_hδ : 0 < δ) (hσ : offDiagSep beta gam k0 j < δ) :
    (((offDiagRatio beta gam) ^ k0) ^ gam) ^ j ≤ (4 * δ) ^ (gam - beta) := by
  have hr0 : 0 < offDiagRatio beta gam := offDiagRatio_pos beta gam
  have hσpos : 0 < offDiagSep beta gam k0 j := offDiagSep_pos k0 j
  rw [rpow_pow_comm hr0 gam k0 j, offDiagRatioPow_eq hbeta hgam]
  rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ 4 * offDiagSep beta gam k0 j)]
  have hexp : (1 - beta / gam) * gam = gam - beta := by
    field_simp
  rw [hexp]
  have h4 : 4 * offDiagSep beta gam k0 j ≤ 4 * δ := by linarith
  exact Real.rpow_le_rpow (by linarith) h4 (by linarith)

/-- The `γ`-th power of the piece length. -/
theorem offDiagLen_rpow_eq {beta gam : ℝ} (_hgam : 0 < gam) (k0 j : ℕ) :
    (offDiagLen beta gam k0 j) ^ gam
      = (4 : ℝ) ^ (-gam) * (((offDiagRatio beta gam) ^ k0) ^ gam) ^ j := by
  have hr0 : 0 < offDiagRatio beta gam := offDiagRatio_pos beta gam
  rw [offDiagLen, Real.mul_rpow (by norm_num) (by positivity)]
  have h1 : ((1 : ℝ) / 4) ^ gam = (4 : ℝ) ^ (-gam) := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  rw [h1, rpow_pow_comm hr0 gam k0 j]

theorem offDiagLen_eq_pow {beta gam : ℝ} (k0 j : ℕ) :
    offDiagLen beta gam k0 j = (1 / 4) * ((offDiagRatio beta gam) ^ k0) ^ j := by
  rw [offDiagLen, ← pow_mul]

/-! ### The Minkowski cover of the off-diagonal example -/

set_option maxHeartbeats 1000000 in
theorem offDiagSet_minkowski_cover {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ ι : Finset ℝ, IsIntervalCover (offDiagSet beta gam k0) δ ι ∧
      (ι.card : ℝ) ≤
        (5 + 16 / (1 - ((offDiagRatio beta gam) ^ k0) ^ gam)) * δ ^ (-beta) := by
  classical
  have hgam : 0 < gam := lt_trans hbeta hbg
  have hR0 : (0 : ℝ) < (offDiagRatio beta gam) ^ k0 := pow_pos (offDiagRatio_pos beta gam) k0
  have hR1 : (offDiagRatio beta gam) ^ k0 < 1 := by linarith
  set q : ℝ := ((offDiagRatio beta gam) ^ k0) ^ gam with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hR0 gam
  have hq1 : q < 1 := by
    rw [hqdef]
    exact Real.rpow_lt_one hR0.le hR1 hgam
  have hr2 : (2 : ℝ) ≤ (2 : ℝ) ^ k0 := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ k0 := pow_le_pow_right₀ (by norm_num) hk0pos
  -- the least index whose piece is shorter than `δ`
  have hexJ : ∃ n : ℕ, offDiagLen beta gam k0 n ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < 4 * δ) hR1
    refine ⟨n, ?_⟩
    rw [offDiagLen_eq_pow]
    linarith
  set J : ℕ := Nat.find hexJ with hJdef
  have hJspec : offDiagLen beta gam k0 J ≤ δ := Nat.find_spec hexJ
  have hJmin : ∀ j, j < J → δ < offDiagLen beta gam k0 j := by
    intro j hj
    exact not_le.mp (Nat.find_min hexJ hj)
  -- the per-piece covers
  have hchoice : ∀ j : ℕ, j < J → ∃ ι : Finset ℝ,
      IsIntervalCover (↑(offDiagPiece beta gam k0 j) : Set ℝ) δ ι ∧
        (ι.card : ℝ) ≤
          (if δ ≤ offDiagSep beta gam k0 j then ((2 : ℝ) ^ k0) ^ j else 0) +
            (if δ ≤ offDiagSep beta gam k0 j then 0
              else 16 * (offDiagLen beta gam k0 j / δ) ^ gam) := by
    intro j hj
    by_cases hσ : δ ≤ offDiagSep beta gam k0 j
    · refine ⟨offDiagPiece beta gam k0 j, offDiagPiece_cover_self k0 j hδ, ?_⟩
      rw [if_pos hσ, if_pos hσ, offDiagPiece_card hgam hgam1 k0 j]
      have hcast : (((2 ^ (k0 * j) : ℕ)) : ℝ) = ((2 : ℝ) ^ k0) ^ j := by
        rw [← pow_mul]
        push_cast
        ring
      rw [hcast]
      linarith
    · obtain ⟨ι, hι, hcard⟩ :=
        offDiagPiece_cover_assouad hgam hgam1 k0 j hδ (le_of_lt (hJmin j hj))
      refine ⟨ι, hι, ?_⟩
      rw [if_neg hσ, if_neg hσ]
      linarith
  choose! covOf hcovIs hcovCard using hchoice
  set ι : Finset ℝ := ({1 + δ / 2, 1 + 3 * δ / 2, 1 + 5 * δ / 2} : Finset ℝ) ∪
    (Finset.range J).biUnion covOf with hιdef
  refine ⟨ι, ?_, ?_⟩
  · -- covering
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rcases Nat.lt_or_ge j J with hlt | hge
    · obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (hcovIs j hlt hj)
      refine Set.mem_iUnion₂.mpr ⟨c, ?_, hxc⟩
      rw [hιdef]
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hlt, hc⟩)
    · obtain ⟨h1, h2⟩ := offDiagPiece_near_one hgam hgam1 hk0 hge hJspec x hj
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (cover_near_one hδ h1 h2)
      refine Set.mem_iUnion₂.mpr ⟨c, ?_, hxc⟩
      rw [hιdef]
      exact Finset.mem_union_left _ hc
  · -- cardinality
    have hcard3 : ({1 + δ / 2, 1 + 3 * δ / 2, 1 + 5 * δ / 2} : Finset ℝ).card ≤ 3 := by
      apply le_trans (Finset.card_insert_le _ _)
      have h2 : ({1 + 3 * δ / 2, 1 + 5 * δ / 2} : Finset ℝ).card ≤ 2 := by
        apply le_trans (Finset.card_insert_le _ _)
        simp
      omega
    have hbi : ((Finset.range J).biUnion covOf).card ≤ ∑ j ∈ Finset.range J, (covOf j).card :=
      Finset.card_biUnion_le
    have hcardι : (ι.card : ℝ) ≤ 3 + ∑ j ∈ Finset.range J, ((covOf j).card : ℝ) := by
      have hunion : ι.card ≤ ({1 + δ / 2, 1 + 3 * δ / 2, 1 + 5 * δ / 2} : Finset ℝ).card +
          ((Finset.range J).biUnion covOf).card := by
        rw [hιdef]
        exact Finset.card_union_le _ _
      have hnat : ι.card ≤ 3 + ∑ j ∈ Finset.range J, (covOf j).card := by
        omega
      calc (ι.card : ℝ) ≤ ((3 + ∑ j ∈ Finset.range J, (covOf j).card : ℕ) : ℝ) := by
            exact_mod_cast hnat
        _ = 3 + ∑ j ∈ Finset.range J, ((covOf j).card : ℝ) := by push_cast; ring
    -- the two sums
    have hsum : ∑ j ∈ Finset.range J, ((covOf j).card : ℝ) ≤
        (∑ j ∈ Finset.range J,
          (if δ ≤ offDiagSep beta gam k0 j then ((2 : ℝ) ^ k0) ^ j else 0)) +
        (∑ j ∈ Finset.range J,
          (if δ ≤ offDiagSep beta gam k0 j then 0
            else 16 * (offDiagLen beta gam k0 j / δ) ^ gam)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum ?_
      intro j hj
      exact hcovCard j (Finset.mem_range.mp hj)
    -- the increasing sum
    have hsumA : (∑ j ∈ Finset.range J,
        (if δ ≤ offDiagSep beta gam k0 j then ((2 : ℝ) ^ k0) ^ j else 0)) ≤
        2 * (4 * δ) ^ (-beta) := by
      refine le_trans (Finset.sum_le_sum ?_)
        (sum_ite_geom_incr_le hr2 (by positivity : (0:ℝ) ≤ (4 * δ) ^ (-beta)) J)
      intro j _
      by_cases hσ : δ ≤ offDiagSep beta gam k0 j
      · rw [if_pos hσ, if_pos (offDiagCount_le_of_le_sep hbeta hgam k0 j hδ hσ)]
      · rw [if_neg hσ]
        by_cases hc : ((2 : ℝ) ^ k0) ^ j ≤ (4 * δ) ^ (-beta)
        · rw [if_pos hc]
          positivity
        · rw [if_neg hc]
    -- the decreasing sum
    have hsumB : (∑ j ∈ Finset.range J,
        (if δ ≤ offDiagSep beta gam k0 j then 0
          else 16 * (offDiagLen beta gam k0 j / δ) ^ gam)) ≤
        16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) * ((4 * δ) ^ (gam - beta) / (1 - q)) := by
      have hstep : ∀ j ∈ Finset.range J,
          (if δ ≤ offDiagSep beta gam k0 j then 0
            else 16 * (offDiagLen beta gam k0 j / δ) ^ gam) ≤
          16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) *
            (if q ^ j ≤ (4 * δ) ^ (gam - beta) then q ^ j else 0) := by
        intro j _
        by_cases hσ : δ ≤ offDiagSep beta gam k0 j
        · rw [if_pos hσ]
          positivity
        · rw [if_neg hσ]
          have hqle : q ^ j ≤ (4 * δ) ^ (gam - beta) := by
            rw [hqdef]
            exact offDiagLenPow_le_of_sep_lt hbeta hbg.le hgam k0 j hδ (not_le.mp hσ)
          rw [if_pos hqle]
          have hdiv : (offDiagLen beta gam k0 j / δ) ^ gam
              = (4 : ℝ) ^ (-gam) * q ^ j * δ ^ (-gam) := by
            rw [Real.div_rpow (offDiagLen_pos k0 j).le hδ.le,
              offDiagLen_rpow_eq hgam k0 j, hqdef]
            rw [Real.rpow_neg hδ.le]
            field_simp
          rw [hdiv]
          ring_nf
          exact le_refl _
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.mul_sum]
      have hgeom := sum_ite_geom_decr_le hq0 hq1
        (by positivity : (0:ℝ) ≤ (4 * δ) ^ (gam - beta)) J
      have hcoef : (0 : ℝ) ≤ 16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) := by positivity
      exact mul_le_mul_of_nonneg_left hgeom hcoef
    -- collect
    have hδpow : (1 : ℝ) ≤ δ ^ (-beta) := by
      rw [Real.rpow_neg hδ.le]
      have hpos : 0 < δ ^ beta := Real.rpow_pos_of_pos hδ beta
      have hle : δ ^ beta ≤ 1 := Real.rpow_le_one hδ.le hδone.le hbeta.le
      rw [le_inv_comm₀ (by norm_num) hpos]
      simpa using hle
    have hA' : 2 * (4 * δ) ^ (-beta) ≤ 2 * δ ^ (-beta) := by
      have h4 : (4 * δ) ^ (-beta) ≤ δ ^ (-beta) := by
        apply Real.rpow_le_rpow_of_nonpos hδ (by linarith) (by linarith)
      linarith
    have hB' : 16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) * ((4 * δ) ^ (gam - beta) / (1 - q))
        ≤ 16 / (1 - q) * δ ^ (-beta) := by
      have hsplit : (4 * δ) ^ (gam - beta) = (4 : ℝ) ^ (gam - beta) * δ ^ (gam - beta) :=
        Real.mul_rpow (by norm_num) hδ.le
      have hδsplit : δ ^ (-gam) * δ ^ (gam - beta) = δ ^ (-beta) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      have h4split : (4 : ℝ) ^ (-gam) * (4 : ℝ) ^ (gam - beta) = (4 : ℝ) ^ (-beta) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 4)]
        congr 1
        ring
      have h4le : (4 : ℝ) ^ (-beta) ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      have hone_q : 0 < 1 - q := by linarith
      have hδpos : 0 < δ ^ (-beta) := Real.rpow_pos_of_pos hδ _
      calc 16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) * ((4 * δ) ^ (gam - beta) / (1 - q))
          = 16 * ((4 : ℝ) ^ (-gam) * (4 : ℝ) ^ (gam - beta)) *
              (δ ^ (-gam) * δ ^ (gam - beta)) / (1 - q) := by
            rw [hsplit]
            ring
        _ = 16 * (4 : ℝ) ^ (-beta) * δ ^ (-beta) / (1 - q) := by
            rw [h4split, hδsplit]
        _ ≤ 16 * 1 * δ ^ (-beta) / (1 - q) := by
            gcongr
        _ = 16 / (1 - q) * δ ^ (-beta) := by ring
    calc (ι.card : ℝ) ≤ 3 + ∑ j ∈ Finset.range J, ((covOf j).card : ℝ) := hcardι
      _ ≤ 3 + (2 * (4 * δ) ^ (-beta) +
          16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) * ((4 * δ) ^ (gam - beta) / (1 - q))) := by
          linarith [hsum, hsumA, hsumB]
      _ ≤ 3 * δ ^ (-beta) + (2 * δ ^ (-beta) + 16 / (1 - q) * δ ^ (-beta)) := by
          have h3 : (3 : ℝ) ≤ 3 * δ ^ (-beta) := by linarith
          linarith [hA', hB']
      _ = (5 + 16 / (1 - q)) * δ ^ (-beta) := by ring

theorem rpow_pow_comm' {x : ℝ} (hx : 0 < x) (y : ℝ) (b : ℕ) :
    (x ^ y) ^ b = (x ^ b) ^ y := by
  have h := rpow_pow_comm hx y 1 b
  simpa using h

/-! ### The Minkowski exponent of the off-diagonal example -/

theorem hasUpperMinkowskiExponent_offDiagSet {beta gam : ℝ} (hbeta : 0 < beta)
    (hbg : beta < gam) (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) :
    HasUpperMinkowskiExponent (offDiagSet beta gam k0) beta := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  have hR0 : (0 : ℝ) < (offDiagRatio beta gam) ^ k0 := pow_pos (offDiagRatio_pos beta gam) k0
  have hR1 : (offDiagRatio beta gam) ^ k0 < 1 := by linarith
  have hq1 : ((offDiagRatio beta gam) ^ k0) ^ gam < 1 := Real.rpow_lt_one hR0.le hR1 hgam
  have hq0 : (0 : ℝ) < ((offDiagRatio beta gam) ^ k0) ^ gam := Real.rpow_pos_of_pos hR0 gam
  intro ε hε
  refine ⟨5 + 16 / (1 - ((offDiagRatio beta gam) ^ k0) ^ gam), ?_, ?_⟩
  · have hpos : 0 < 1 - ((offDiagRatio beta gam) ^ k0) ^ gam := by linarith
    have : 0 < 16 / (1 - ((offDiagRatio beta gam) ^ k0) ^ gam) := by positivity
    linarith
  intro δ hδ hδone
  obtain ⟨ι, hι, hcard⟩ := offDiagSet_minkowski_cover hbeta hbg hgam1 hk0pos hk0 hδ hδone
  refine ⟨ι, hι, le_trans hcard ?_⟩
  have hstep : δ ^ (-beta) ≤ δ ^ (-(beta + ε)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδone.le (by linarith)
  have hC : (0 : ℝ) ≤ 5 + 16 / (1 - ((offDiagRatio beta gam) ^ k0) ^ gam) := by
    have hpos : 0 < 1 - ((offDiagRatio beta gam) ^ k0) ^ gam := by linarith
    have : 0 < 16 / (1 - ((offDiagRatio beta gam) ^ k0) ^ gam) := by positivity
    linarith
  exact mul_le_mul_of_nonneg_left hstep hC

/-! ### The spectrum cover of the off-diagonal example -/

set_option maxHeartbeats 1000000 in
theorem offDiagSet_spectrum_cover {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam1 : gam ≤ 1) {k0 : ℕ} (_hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (hδt : δ ≤ b - a) (_ht1 : b - a ≤ 1) :
    ∃ ι : Finset ℝ, IsIntervalCover (offDiagSet beta gam k0 ∩ Icc a b) δ ι ∧
      (ι.card : ℝ) ≤
        (19 + 16 / (1 - ((offDiagRatio beta gam) ^ k0) ^ gam)) * ((b - a) / δ) ^ gam := by
  classical
  have hgam : 0 < gam := lt_trans hbeta hbg
  have htpos : 0 < b - a := lt_of_lt_of_le hδ hδt
  have hR0 : (0 : ℝ) < (offDiagRatio beta gam) ^ k0 := pow_pos (offDiagRatio_pos beta gam) k0
  have hR1 : (offDiagRatio beta gam) ^ k0 < 1 := by linarith
  set q : ℝ := ((offDiagRatio beta gam) ^ k0) ^ gam with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hR0 gam
  have hq1 : q < 1 := by
    rw [hqdef]
    exact Real.rpow_lt_one hR0.le hR1 hgam
  have hone_q : 0 < 1 - q := by linarith
  have hratio1 : (1 : ℝ) ≤ (b - a) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have hrpow1 : (1 : ℝ) ≤ ((b - a) / δ) ^ gam := Real.one_le_rpow hratio1 hgam.le
  -- the least index whose piece is shorter than `δ`
  have hexJ : ∃ n : ℕ, offDiagLen beta gam k0 n ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < 4 * δ) hR1
    refine ⟨n, ?_⟩
    rw [offDiagLen_eq_pow]
    linarith
  set J : ℕ := Nat.find hexJ with hJdef
  have hJspec : offDiagLen beta gam k0 J ≤ δ := Nat.find_spec hexJ
  have hJmin : ∀ j, j < J → δ < offDiagLen beta gam k0 j := by
    intro j hj
    exact not_le.mp (Nat.find_min hexJ hj)
  -- the per-piece covers of the localized pieces
  have hchoice : ∀ j : ℕ, j < J → ∃ ι : Finset ℝ,
      IsIntervalCover ((↑(offDiagPiece beta gam k0 j) : Set ℝ) ∩ Icc a b) δ ι ∧
        (ι.card : ℝ) ≤
          (if (b - a ≤ offDiagLen beta gam k0 j ∧
              ((offDiagPiece beta gam k0 j).filter (fun x => a ≤ x ∧ x ≤ b)).Nonempty)
            then 16 * ((b - a) / δ) ^ gam else 0) +
          (if b - a ≤ offDiagLen beta gam k0 j then 0
            else 16 * (offDiagLen beta gam k0 j / δ) ^ gam) := by
    intro j hj
    by_cases hbig : b - a ≤ offDiagLen beta gam k0 j
    · by_cases hne : ((offDiagPiece beta gam k0 j).filter (fun x => a ≤ x ∧ x ≤ b)).Nonempty
      · obtain ⟨ι, hι, hcard⟩ := cantorMid_assouad_cover hgam hgam1 (k0 * j)
          (1 + 2 * offDiagLen beta gam k0 j) (offDiagLen_pos k0 j)
          (δ := δ) (a := a) (b := b) hδ hδt hbig
        refine ⟨ι, hι, ?_⟩
        rw [if_pos ⟨hbig, hne⟩, if_pos hbig]
        linarith
      · refine ⟨∅, ?_, ?_⟩
        · intro x hx
          exfalso
          obtain ⟨hxpiece, hxab⟩ := hx
          refine hne ⟨x, ?_⟩
          rw [Finset.mem_filter]
          exact ⟨hxpiece, hxab.1, hxab.2⟩
        · rw [if_neg (by tauto), if_pos hbig]
          simp
    · obtain ⟨ι, hι, hcard⟩ :=
        offDiagPiece_cover_assouad hgam hgam1 k0 j hδ (le_of_lt (hJmin j hj))
      refine ⟨ι, ?_, ?_⟩
      · refine IsIntervalCover.mono ?_ hι
        exact Set.inter_subset_left
      · rw [if_neg (by tauto), if_neg hbig]
        linarith
  choose! covOf hcovIs hcovCard using hchoice
  set ι : Finset ℝ := ({1 + δ / 2, 1 + 3 * δ / 2, 1 + 5 * δ / 2} : Finset ℝ) ∪
    (Finset.range J).biUnion covOf with hιdef
  refine ⟨ι, ?_, ?_⟩
  · -- covering
    intro x hx
    obtain ⟨hxset, hxab⟩ := hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxset
    rcases Nat.lt_or_ge j J with hlt | hge
    · obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (hcovIs j hlt ⟨hj, hxab⟩)
      refine Set.mem_iUnion₂.mpr ⟨c, ?_, hxc⟩
      rw [hιdef]
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hlt, hc⟩)
    · obtain ⟨h1, h2⟩ := offDiagPiece_near_one hgam hgam1 hk0 hge hJspec x hj
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (cover_near_one hδ h1 h2)
      refine Set.mem_iUnion₂.mpr ⟨c, ?_, hxc⟩
      rw [hιdef]
      exact Finset.mem_union_left _ hc
  · -- cardinality
    have hcard3 : ({1 + δ / 2, 1 + 3 * δ / 2, 1 + 5 * δ / 2} : Finset ℝ).card ≤ 3 := by
      apply le_trans (Finset.card_insert_le _ _)
      have h2 : ({1 + 3 * δ / 2, 1 + 5 * δ / 2} : Finset ℝ).card ≤ 2 := by
        apply le_trans (Finset.card_insert_le _ _)
        simp
      omega
    have hcardι : (ι.card : ℝ) ≤ 3 + ∑ j ∈ Finset.range J, ((covOf j).card : ℝ) := by
      have hunion : ι.card ≤ ({1 + δ / 2, 1 + 3 * δ / 2, 1 + 5 * δ / 2} : Finset ℝ).card +
          ((Finset.range J).biUnion covOf).card := by
        rw [hιdef]
        exact Finset.card_union_le _ _
      have hbi : ((Finset.range J).biUnion covOf).card ≤
          ∑ j ∈ Finset.range J, (covOf j).card := Finset.card_biUnion_le
      have hnat : ι.card ≤ 3 + ∑ j ∈ Finset.range J, (covOf j).card := by omega
      calc (ι.card : ℝ) ≤ ((3 + ∑ j ∈ Finset.range J, (covOf j).card : ℕ) : ℝ) := by
            exact_mod_cast hnat
        _ = 3 + ∑ j ∈ Finset.range J, ((covOf j).card : ℝ) := by push_cast; ring
    have hsum : ∑ j ∈ Finset.range J, ((covOf j).card : ℝ) ≤
        (∑ j ∈ Finset.range J,
          (if (b - a ≤ offDiagLen beta gam k0 j ∧
              ((offDiagPiece beta gam k0 j).filter (fun x => a ≤ x ∧ x ≤ b)).Nonempty)
            then 16 * ((b - a) / δ) ^ gam else 0)) +
        (∑ j ∈ Finset.range J,
          (if b - a ≤ offDiagLen beta gam k0 j then 0
            else 16 * (offDiagLen beta gam k0 j / δ) ^ gam)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j hj => hcovCard j (Finset.mem_range.mp hj)
    -- at most one long piece meets the interval
    have hlong : ((Finset.range J).filter (fun j => b - a ≤ offDiagLen beta gam k0 j ∧
        ((offDiagPiece beta gam k0 j).filter (fun x => a ≤ x ∧ x ≤ b)).Nonempty)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro j1 hj1 j2 hj2
      by_contra hne
      -- the two pieces are separated by more than the length of the interval
      have hkey : ∀ i1 i2 : ℕ, i1 < i2 →
          (b - a ≤ offDiagLen beta gam k0 i1 ∧
            ((offDiagPiece beta gam k0 i1).filter (fun x => a ≤ x ∧ x ≤ b)).Nonempty) →
          (b - a ≤ offDiagLen beta gam k0 i2 ∧
            ((offDiagPiece beta gam k0 i2).filter (fun x => a ≤ x ∧ x ≤ b)).Nonempty) →
          False := by
        intro i1 i2 hlt ⟨hbig1, hne1⟩ ⟨hbig2, hne2⟩
        obtain ⟨x1, hx1⟩ := hne1
        obtain ⟨x2, hx2⟩ := hne2
        rw [Finset.mem_filter] at hx1 hx2
        obtain ⟨hx1piece, hx1a, hx1b⟩ := hx1
        obtain ⟨hx2piece, hx2a, hx2b⟩ := hx2
        obtain ⟨h1low, -⟩ := offDiagPiece_subset_Icc hgam hgam1 k0 i1 x1 hx1piece
        obtain ⟨-, h2up⟩ := offDiagPiece_subset_Icc hgam hgam1 k0 i2 x2 hx2piece
        have hchain : 3 * offDiagLen beta gam k0 i2 ≤ offDiagLen beta gam k0 i1 := by
          have hstep := offDiagLen_succ hk0 i1
          have hmono := offDiagLen_antitone hk0 (i1 + 1) i2 (by omega)
          have hpos := offDiagLen_pos (beta := beta) (gam := gam) k0 i2
          nlinarith [hstep, hmono, hpos]
        have hgapbig : offDiagLen beta gam k0 i1 ≤ b - a := by
          nlinarith [h1low, h2up, hx1b, hx2a, hchain]
        linarith [hbig1, hgapbig, offDiagLen_pos (beta := beta) (gam := gam) k0 i1]
      rw [Finset.mem_filter] at hj1 hj2
      rcases Nat.lt_or_ge j1 j2 with hlt | hge
      · exact hkey j1 j2 hlt hj1.2 hj2.2
      · rcases Nat.lt_or_ge j2 j1 with hlt2 | hge2
        · exact hkey j2 j1 hlt2 hj2.2 hj1.2
        · exact hne (by omega)
    have hsumA : (∑ j ∈ Finset.range J,
        (if (b - a ≤ offDiagLen beta gam k0 j ∧
            ((offDiagPiece beta gam k0 j).filter (fun x => a ≤ x ∧ x ≤ b)).Nonempty)
          then 16 * ((b - a) / δ) ^ gam else 0)) ≤ 16 * ((b - a) / δ) ^ gam := by
      rw [← Finset.sum_filter, Finset.sum_const]
      have hnn : (0 : ℝ) ≤ 16 * ((b - a) / δ) ^ gam := by positivity
      calc (((Finset.range J).filter (fun j => b - a ≤ offDiagLen beta gam k0 j ∧
              ((offDiagPiece beta gam k0 j).filter (fun x => a ≤ x ∧ x ≤ b)).Nonempty)).card •
            (16 * ((b - a) / δ) ^ gam))
          = (((Finset.range J).filter (fun j => b - a ≤ offDiagLen beta gam k0 j ∧
              ((offDiagPiece beta gam k0 j).filter (fun x => a ≤ x ∧ x ≤ b)).Nonempty)).card : ℝ) *
              (16 * ((b - a) / δ) ^ gam) := by
            rw [nsmul_eq_mul]
        _ ≤ 1 * (16 * ((b - a) / δ) ^ gam) := by
            apply mul_le_mul_of_nonneg_right _ hnn
            exact_mod_cast hlong
        _ = 16 * ((b - a) / δ) ^ gam := by ring
    -- the short pieces
    have hsumB : (∑ j ∈ Finset.range J,
        (if b - a ≤ offDiagLen beta gam k0 j then 0
          else 16 * (offDiagLen beta gam k0 j / δ) ^ gam)) ≤
        16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) * ((4 * (b - a)) ^ gam / (1 - q)) := by
      have hstep : ∀ j ∈ Finset.range J,
          (if b - a ≤ offDiagLen beta gam k0 j then 0
            else 16 * (offDiagLen beta gam k0 j / δ) ^ gam) ≤
          16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) *
            (if q ^ j ≤ (4 * (b - a)) ^ gam then q ^ j else 0) := by
        intro j _
        by_cases hbig : b - a ≤ offDiagLen beta gam k0 j
        · rw [if_pos hbig]
          positivity
        · rw [if_neg hbig]
          have hqle : q ^ j ≤ (4 * (b - a)) ^ gam := by
            have hlt : offDiagLen beta gam k0 j < b - a := not_le.mp hbig
            have h4 : ((offDiagRatio beta gam) ^ k0) ^ j ≤ 4 * (b - a) := by
              rw [offDiagLen_eq_pow] at hlt
              linarith
            have hqj : q ^ j = (((offDiagRatio beta gam) ^ k0) ^ j) ^ gam := by
              rw [hqdef]
              exact rpow_pow_comm' hR0 gam j
            rw [hqj]
            exact Real.rpow_le_rpow (by positivity) h4 hgam.le
          rw [if_pos hqle]
          have hdiv : (offDiagLen beta gam k0 j / δ) ^ gam
              = (4 : ℝ) ^ (-gam) * q ^ j * δ ^ (-gam) := by
            rw [Real.div_rpow (offDiagLen_pos k0 j).le hδ.le,
              offDiagLen_rpow_eq hgam k0 j, hqdef]
            rw [Real.rpow_neg hδ.le]
            field_simp
          rw [hdiv]
          ring_nf
          exact le_refl _
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.mul_sum]
      have hgeom := sum_ite_geom_decr_le hq0 hq1
        (by positivity : (0:ℝ) ≤ (4 * (b - a)) ^ gam) J
      have hcoef : (0 : ℝ) ≤ 16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) := by positivity
      exact mul_le_mul_of_nonneg_left hgeom hcoef
    -- collect
    have hB' : 16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) * ((4 * (b - a)) ^ gam / (1 - q))
        = 16 / (1 - q) * ((b - a) / δ) ^ gam := by
      have hsplit : (4 * (b - a)) ^ gam = (4 : ℝ) ^ gam * (b - a) ^ gam :=
        Real.mul_rpow (by norm_num) htpos.le
      have h4split : (4 : ℝ) ^ (-gam) * (4 : ℝ) ^ gam = 1 := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 4)]
        simp
      have hδsplit : δ ^ (-gam) * (b - a) ^ gam = ((b - a) / δ) ^ gam := by
        rw [Real.div_rpow htpos.le hδ.le, Real.rpow_neg hδ.le]
        field_simp
      calc 16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) * ((4 * (b - a)) ^ gam / (1 - q))
          = 16 * ((4 : ℝ) ^ (-gam) * (4 : ℝ) ^ gam) *
              (δ ^ (-gam) * (b - a) ^ gam) / (1 - q) := by
            rw [hsplit]
            ring
        _ = 16 * ((b - a) / δ) ^ gam / (1 - q) := by
            rw [h4split, hδsplit]
            ring
        _ = 16 / (1 - q) * ((b - a) / δ) ^ gam := by ring
    calc (ι.card : ℝ) ≤ 3 + ∑ j ∈ Finset.range J, ((covOf j).card : ℝ) := hcardι
      _ ≤ 3 + (16 * ((b - a) / δ) ^ gam +
          16 * (4 : ℝ) ^ (-gam) * δ ^ (-gam) * ((4 * (b - a)) ^ gam / (1 - q))) := by
          linarith [hsum, hsumA, hsumB]
      _ ≤ 3 * ((b - a) / δ) ^ gam + (16 * ((b - a) / δ) ^ gam +
          16 / (1 - q) * ((b - a) / δ) ^ gam) := by
          have h3 : (3 : ℝ) ≤ 3 * ((b - a) / δ) ^ gam := by linarith
          linarith [hB']
      _ = (19 + 16 / (1 - q)) * ((b - a) / δ) ^ gam := by ring

/-! ### Ruling out exponents by separated families -/

/-- A family of separated subsets whose cardinalities beat the covering bound rules out a
Minkowski exponent. -/
theorem not_hasUpperMinkowskiExponent_of_separated {F : Set ℝ} {beta' ε : ℝ} (hε : 0 < ε)
    (hfam : ∀ C : ℝ, 0 < C → ∃ (S : Finset ℝ) (δ : ℝ), 0 < δ ∧ δ < 1 ∧
      (∀ x ∈ S, x ∈ F) ∧ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ < |x - y|) ∧
      C * δ ^ (-(beta' + ε)) < (S.card : ℝ)) :
    ¬ HasUpperMinkowskiExponent F beta' := by
  intro hcon
  obtain ⟨C, hC, hcov⟩ := hcon ε hε
  obtain ⟨S, δ, hδ, hδ1, hSF, hsep, hbig⟩ := hfam C hC
  obtain ⟨ι, hι, hcard⟩ := hcov δ hδ hδ1
  have hlow := card_le_card_of_intervalCover_of_separated hι hSF hsep
  have hlow' : (S.card : ℝ) ≤ (ι.card : ℝ) := by exact_mod_cast hlow
  linarith

/-- The same for the upper Assouad spectrum. -/
theorem not_hasUpperAssouadSpectrumExponent_of_separated {F : Set ℝ} {θ gam' : ℝ}
    (hfam : ∀ C : ℝ, 0 < C → ∃ (S : Finset ℝ) (δ a b : ℝ),
      0 < δ ∧ δ < 1 ∧ 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ δ ^ θ ≤ b - a ∧
      (∀ x ∈ S, x ∈ F ∩ Icc a b) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ < |x - y|) ∧
      C * ((b - a) / δ) ^ gam' < (S.card : ℝ)) :
    ¬ HasUpperAssouadSpectrumExponent F θ gam' := by
  intro hcon
  obtain ⟨C, hC, hcov⟩ := hcon
  obtain ⟨S, δ, a, b, hδ, hδ1, ha, hab, hb, hscale, hSF, hsep, hbig⟩ := hfam C hC
  obtain ⟨ι, hι, hcard⟩ := hcov δ a b hδ hδ1 ha hab hb hscale
  have hlow := card_le_card_of_intervalCover_of_separated hι hSF hsep
  have hlow' : (S.card : ℝ) ≤ (ι.card : ℝ) := by exact_mod_cast hlow
  linarith

/-! ### The spectrum of the off-diagonal example, upper bound -/

theorem hasUpperAssouadSpectrumExponent_offDiagSet {beta gam : ℝ} (hbeta : 0 < beta)
    (hbg : beta < gam) (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) {θ : ℝ} (hθ1 : θ ≤ 1) :
    HasUpperAssouadSpectrumExponent (offDiagSet beta gam k0) θ gam := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  have hR0 : (0 : ℝ) < (offDiagRatio beta gam) ^ k0 := pow_pos (offDiagRatio_pos beta gam) k0
  have hR1 : (offDiagRatio beta gam) ^ k0 < 1 := by linarith
  have hq1 : ((offDiagRatio beta gam) ^ k0) ^ gam < 1 := Real.rpow_lt_one hR0.le hR1 hgam
  have hq0 : (0 : ℝ) < ((offDiagRatio beta gam) ^ k0) ^ gam := Real.rpow_pos_of_pos hR0 gam
  have hone_q : (0 : ℝ) < 1 - ((offDiagRatio beta gam) ^ k0) ^ gam := by linarith
  refine ⟨19 + 16 / (1 - ((offDiagRatio beta gam) ^ k0) ^ gam), ?_, ?_⟩
  · have : 0 < 16 / (1 - ((offDiagRatio beta gam) ^ k0) ^ gam) := by positivity
    linarith
  intro δ a b hδ hδone ha hab hb hscale
  have hδt : δ ≤ b - a := by
    have h1 : δ ≤ δ ^ θ := by
      calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
        _ ≤ δ ^ θ := Real.rpow_le_rpow_of_exponent_ge hδ hδone.le hθ1
    linarith
  have ht1 : b - a ≤ 1 := by linarith
  obtain ⟨ι, hι, hcard⟩ :=
    offDiagSet_spectrum_cover hbeta hbg hgam1 hk0pos hk0 hδ hab hδt ht1
  exact ⟨ι, hι, hcard⟩

/-! ### The separation scale as a geometric sequence -/

/-- The separation of the `j`-th piece is `4⁻¹ν^j` for the product ratio `ν`. -/
theorem offDiagSep_eq_pow {beta gam : ℝ} (k0 j : ℕ) :
    offDiagSep beta gam k0 j =
      (1 / 4) * ((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ j := by
  rw [offDiagSep, offDiagLen, mul_pow, ← pow_mul, ← pow_mul]
  ring

theorem offDiagNu_pos {beta gam : ℝ} (k0 : ℕ) :
    0 < (cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0 :=
  mul_pos (pow_pos (cantorRatio_pos gam) k0) (pow_pos (offDiagRatio_pos beta gam) k0)

theorem offDiagNu_lt_one {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam) (hgam1 : gam ≤ 1)
    {k0 : ℕ} (hk0pos : 1 ≤ k0) :
    (cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0 < 1 := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  have hmu : cantorRatio gam ≤ 1 / 2 := cantorRatio_le_half hgam hgam1
  have hmupos : 0 < cantorRatio gam := cantorRatio_pos gam
  have hrpos : 0 < offDiagRatio beta gam := offDiagRatio_pos beta gam
  have hr1 : offDiagRatio beta gam < 1 := offDiagRatio_lt_one hbeta hbg
  have hmupow : (cantorRatio gam) ^ k0 ≤ 1 / 2 := by
    calc (cantorRatio gam) ^ k0 ≤ (cantorRatio gam) ^ 1 :=
          pow_le_pow_of_le_one hmupos.le (by linarith) hk0pos
      _ = cantorRatio gam := pow_one _
      _ ≤ 1 / 2 := hmu
  have hrpow : (offDiagRatio beta gam) ^ k0 ≤ 1 :=
    pow_le_one₀ hrpos.le hr1.le
  have hmupowpos : 0 < (cantorRatio gam) ^ k0 := pow_pos hmupos k0
  have hrpowpos : 0 < (offDiagRatio beta gam) ^ k0 := pow_pos hrpos k0
  nlinarith [hmupow, hrpow, hmupowpos, hrpowpos]

/-! ### The Minkowski lower bound -/

set_option maxHeartbeats 1000000 in
theorem not_hasUpperMinkowskiExponent_offDiagSet {beta gam beta' : ℝ} (hbeta : 0 < beta)
    (hbg : beta < gam) (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hbeta'0 : 0 ≤ beta') (hlt : beta' < beta) :
    ¬ HasUpperMinkowskiExponent (offDiagSet beta gam k0) beta' := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  set ε : ℝ := (beta - beta') / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set beta'' : ℝ := beta' + ε with hb2def
  have hb2lt : beta'' < beta := by rw [hb2def, hεdef]; linarith
  have hb20 : 0 ≤ beta'' := by rw [hb2def]; linarith
  have hgap : 0 < beta - beta'' := by linarith
  refine not_hasUpperMinkowskiExponent_of_separated hε ?_
  intro C hC
  -- the threshold
  set K : ℝ := C * (8 : ℝ) ^ beta'' + 1 with hKdef
  have hK : 0 < K := by
    rw [hKdef]
    have : (0 : ℝ) < (8 : ℝ) ^ beta'' := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set t0 : ℝ := (1 / K) ^ (1 / (beta - beta'')) with ht0def
  have ht0 : 0 < t0 := Real.rpow_pos_of_pos (by positivity) _
  have hν : 0 < (cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0 := offDiagNu_pos k0
  have hν1 : (cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0 < 1 :=
    offDiagNu_lt_one hbeta hbg hgam1 hk0pos
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one ht0 hν1
  set s : ℝ := ((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ j with hsdef
  have hs0 : 0 < s := pow_pos hν j
  have hst0 : s < t0 := hj
  -- the separated family
  refine ⟨offDiagPiece beta gam k0 j, offDiagSep beta gam k0 j / 2, by
    have := offDiagSep_pos (beta := beta) (gam := gam) k0 j
    linarith, ?_, ?_, ?_, ?_⟩
  · -- the scale is below one
    have h1 : offDiagSep beta gam k0 j ≤ offDiagLen beta gam k0 j := by
      rw [offDiagSep]
      have hpow : (cantorRatio gam) ^ (k0 * j) ≤ 1 :=
        pow_le_one₀ (cantorRatio_pos gam).le (le_of_lt (lt_of_le_of_lt
          (cantorRatio_le_half hgam hgam1) (by norm_num)))
      have hlen := offDiagLen_pos (beta := beta) (gam := gam) k0 j
      nlinarith [hpow, hlen]
    have h2 : offDiagLen beta gam k0 j ≤ 1 / 4 :=
      offDiagLen_le_quarter hbeta hbg k0 j
    linarith
  · -- the points belong to the set
    intro x hx
    exact Set.mem_iUnion.mpr ⟨j, hx⟩
  · -- separation
    intro x hx y hy hxy
    have hsep := cantorMid_separated (cantorRatio_pos gam) (cantorRatio_le_half hgam hgam1)
      (k0 * j) (offDiagLen_pos (beta := beta) (gam := gam) k0 j).le hx hy hxy
    have hσ : offDiagSep beta gam k0 j =
        (cantorRatio gam) ^ (k0 * j) * offDiagLen beta gam k0 j := rfl
    rw [← hσ] at hsep
    have hpos := offDiagSep_pos (beta := beta) (gam := gam) k0 j
    linarith
  · -- the cardinality beats the covering bound
    have hcard : ((offDiagPiece beta gam k0 j).card : ℝ) = (4 * offDiagSep beta gam k0 j) ^ (-beta) := by
      rw [offDiagPiece_card hgam hgam1 k0 j, offDiagCount_eq hbeta hgam k0 j]
      push_cast
      ring
    have hs4 : 4 * offDiagSep beta gam k0 j = s := by
      rw [offDiagSep_eq_pow, hsdef]
      ring
    rw [hcard, hs4]
    -- the scale in terms of `s`
    have hδs : offDiagSep beta gam k0 j / 2 = s / 8 := by
      rw [offDiagSep_eq_pow, hsdef]
      ring
    rw [hδs]
    -- `s ^ (-(β'' )) * 8 ^ β''` versus `s ^ (-β)`
    have hsplit1 : (s / 8) ^ (-beta'') = s ^ (-beta'') * (8 : ℝ) ^ beta'' := by
      rw [Real.div_rpow hs0.le (by norm_num), Real.rpow_neg hs0.le,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 8)]
      field_simp
    have hsplit2 : s ^ (-beta) = s ^ (-beta'') * s ^ (-(beta - beta'')) := by
      rw [← Real.rpow_add hs0]
      congr 1
      ring
    have hbig : K < s ^ (-(beta - beta'')) := by
      have hspow : s ^ (beta - beta'') < 1 / K := by
        have hmono : s ^ (beta - beta'') < t0 ^ (beta - beta'') :=
          Real.rpow_lt_rpow hs0.le hst0 hgap
        have ht0pow : t0 ^ (beta - beta'') = 1 / K := by
          rw [ht0def, ← Real.rpow_mul (by positivity)]
          rw [one_div_mul_cancel (by linarith : beta - beta'' ≠ 0), Real.rpow_one]
        rw [ht0pow] at hmono
        exact hmono
      have hspos : 0 < s ^ (beta - beta'') := Real.rpow_pos_of_pos hs0 _
      have hinv : s ^ (-(beta - beta'')) = (s ^ (beta - beta''))⁻¹ :=
        Real.rpow_neg hs0.le _
      rw [hinv]
      rw [lt_inv_comm₀ hK hspos]
      calc s ^ (beta - beta'') < 1 / K := hspow
        _ = K⁻¹ := by rw [one_div]
    have hspos2 : 0 < s ^ (-beta'') := Real.rpow_pos_of_pos hs0 _
    have h8 : (0 : ℝ) < (8 : ℝ) ^ beta'' := Real.rpow_pos_of_pos (by norm_num) _
    rw [hsplit1, hsplit2]
    calc C * (s ^ (-beta'') * (8 : ℝ) ^ beta'')
        = (C * (8 : ℝ) ^ beta'') * s ^ (-beta'') := by ring
      _ < K * s ^ (-beta'') := by
          apply mul_lt_mul_of_pos_right _ hspos2
          rw [hKdef]
          linarith
      _ < s ^ (-(beta - beta'')) * s ^ (-beta'') := by
          exact mul_lt_mul_of_pos_right hbig hspos2
      _ = s ^ (-beta'') * s ^ (-(beta - beta'')) := by ring

/-! ### Eventual bounds for geometric sequences -/

theorem exists_le_pow_of_one_lt {B : ℝ} (hB : 1 < B) (K : ℝ) :
    ∃ j0 : ℕ, ∀ j : ℕ, j0 ≤ j → K ≤ B ^ j := by
  have hBpos : (0 : ℝ) < B := by linarith
  have hinvlt : B⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hB
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < 1 / (|K| + 1)) hinvlt
  refine ⟨n, fun j hj => ?_⟩
  have hstep : B ^ n ≤ B ^ j := pow_le_pow_right₀ hB.le hj
  have hBn : |K| + 1 < B ^ n := by
    have hpos : (0 : ℝ) < B ^ n := pow_pos hBpos n
    rw [inv_pow] at hn
    have habs : (0 : ℝ) < |K| + 1 := by positivity
    rw [inv_lt_iff_one_lt_mul₀' hpos] at hn
    have hmul := mul_lt_mul_of_pos_right hn habs
    have hsimp : (B ^ n * (1 / (|K| + 1))) * (|K| + 1) = B ^ n := by field_simp
    rw [hsimp, one_mul] at hmul
    exact hmul
  have hKle : K ≤ |K| := le_abs_self K
  linarith

theorem exists_pow_le_of_lt_one {b : ℝ} (hb0 : 0 < b) (hb : b < 1) {t : ℝ} (ht : 0 < t) :
    ∃ j0 : ℕ, ∀ j : ℕ, j0 ≤ j → b ^ j ≤ t := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ht hb
  refine ⟨n, fun j hj => ?_⟩
  have hstep : b ^ j ≤ b ^ n := pow_le_pow_of_le_one hb0.le hb.le hj
  linarith

/-! ### The product ratio and the ratio of the two scales -/

/-- The product ratio is `2^{-k₀/β}`. -/
theorem offDiagNu_eq {beta gam : ℝ} (hbeta : 0 < beta) (hgam : 0 < gam) (k0 : ℕ) :
    (cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0
      = (2 : ℝ) ^ (-(k0 : ℝ) / beta) := by
  have h1 := offDiagSep_eq_pow (beta := beta) (gam := gam) k0 1
  have h2 := offDiagSep_eq hbeta hgam k0 1
  rw [pow_one] at h1
  rw [h1] at h2
  have hcast : ((k0 * 1 : ℕ) : ℝ) = (k0 : ℝ) := by push_cast; ring
  rw [hcast] at h2
  linarith

/-- The `k₀`-th power of the length ratio is `2^{-k₀ gap}`. -/
theorem offDiagRatio_pow_eq {beta gam : ℝ} (k0 : ℕ) :
    (offDiagRatio beta gam) ^ k0 = (2 : ℝ) ^ (-(k0 : ℝ) * offDiagGap beta gam) := by
  rw [offDiagRatio, ← Real.rpow_natCast ((2 : ℝ) ^ (-offDiagGap beta gam)) k0,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

/-- Above the critical scale parameter the length ratio beats the separation ratio. -/
theorem one_lt_offDiagRatio_div_nu_rpow {beta gam θ : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    {k0 : ℕ} (hk0pos : 1 ≤ k0) (hθ : 1 - beta / gam < θ) :
    1 < (offDiagRatio beta gam) ^ k0 /
      ((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  have hnueq : (cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0
      = (2 : ℝ) ^ (-(k0 : ℝ) / beta) := offDiagNu_eq hbeta hgam k0
  have hRpeq : (offDiagRatio beta gam) ^ k0
      = (2 : ℝ) ^ (-(k0 : ℝ) * offDiagGap beta gam) := offDiagRatio_pow_eq k0
  have hdiv : (offDiagRatio beta gam) ^ k0 /
      ((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ
      = (2 : ℝ) ^ (-(k0 : ℝ) * offDiagGap beta gam - (-(k0 : ℝ) / beta) * θ) := by
    rw [hnueq, hRpeq, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
  rw [hdiv]
  refine (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, ?_⟩)
  have hk0R : (1 : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk0pos
  have hkey : 0 < θ / beta - 1 / beta + 1 / gam := by
    have hid : θ / beta - 1 / beta + 1 / gam = (θ * gam - gam + beta) / (beta * gam) := by
      field_simp
    rw [hid]
    refine div_pos ?_ (by positivity)
    have hmul : (1 - beta / gam) * gam < θ * gam := by
      apply mul_lt_mul_of_pos_right hθ hgam
    have hsimp : (1 - beta / gam) * gam = gam - beta := by
      field_simp
    rw [hsimp] at hmul
    linarith
  rw [offDiagGap]
  have hexp : -(k0 : ℝ) * (1 / beta - 1 / gam) - (-(k0 : ℝ) / beta) * θ
      = (k0 : ℝ) * (θ / beta - 1 / beta + 1 / gam) := by
    field_simp
    ring
  rw [hexp]
  have hk0pos' : (0 : ℝ) < (k0 : ℝ) := by linarith
  exact mul_pos hk0pos' hkey

/-! ### The spectrum lower bound for the off-diagonal example -/

set_option maxHeartbeats 1000000 in
theorem not_hasUpperAssouadSpectrumExponent_offDiagSet {beta gam gam' θ : ℝ}
    (hbeta : 0 < beta) (hbg : beta < gam) (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hθ : 1 - beta / gam < θ) (_hgam'0 : 0 ≤ gam') (hlt : gam' < gam) :
    ¬ HasUpperAssouadSpectrumExponent (offDiagSet beta gam k0) θ gam' := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  have hmu : 0 < cantorRatio gam := cantorRatio_pos gam
  have hmu2 : cantorRatio gam ≤ 1 / 2 := cantorRatio_le_half hgam hgam1
  have hmulone : cantorRatio gam < 1 := lt_of_le_of_lt hmu2 (by norm_num)
  have hmu0pos : (0 : ℝ) < (cantorRatio gam) ^ k0 := pow_pos hmu k0
  have hmu0lt : (cantorRatio gam) ^ k0 < 1 := pow_lt_one₀ hmu.le hmulone (by omega)
  have hRp0 : (0 : ℝ) < (offDiagRatio beta gam) ^ k0 := pow_pos (offDiagRatio_pos beta gam) k0
  have hnu0 : (0 : ℝ) < (cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0 :=
    offDiagNu_pos k0
  have hgapgam : 0 < gam - gam' := by linarith
  refine not_hasUpperAssouadSpectrumExponent_of_separated ?_
  intro C hC
  -- the threshold for the scale condition
  obtain ⟨j1, hj1⟩ := exists_le_pow_of_one_lt
    (one_lt_offDiagRatio_div_nu_rpow hbeta hbg hk0pos hθ) ((1 / 8 : ℝ) ^ θ / (1 / 4))
  -- the threshold for the cardinality condition
  set K2 : ℝ := C * (2 : ℝ) ^ gam' + 1 with hK2def
  have hK2 : 0 < K2 := by
    rw [hK2def]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ gam' := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set t2 : ℝ := (1 / K2) ^ (1 / (gam - gam')) with ht2def
  have ht2 : 0 < t2 := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨j2, hj2⟩ := exists_pow_le_of_lt_one hmu0pos hmu0lt ht2
  set j : ℕ := max j1 j2 with hjdef
  have hj1le : j1 ≤ j := le_max_left _ _
  have hj2le : j2 ≤ j := le_max_right _ _
  -- the data
  have hLpos : 0 < offDiagLen beta gam k0 j := offDiagLen_pos k0 j
  have hLquarter : offDiagLen beta gam k0 j ≤ 1 / 4 := offDiagLen_le_quarter hbeta hbg k0 j
  have hσpos : 0 < offDiagSep beta gam k0 j := offDiagSep_pos k0 j
  have hσL : offDiagSep beta gam k0 j ≤ offDiagLen beta gam k0 j := by
    rw [offDiagSep]
    have hpow : (cantorRatio gam) ^ (k0 * j) ≤ 1 := pow_le_one₀ hmu.le hmulone.le
    nlinarith [hpow, hLpos]
  have hmu0j : (cantorRatio gam) ^ (k0 * j) = ((cantorRatio gam) ^ k0) ^ j := by
    rw [← pow_mul]
  refine ⟨offDiagPiece beta gam k0 j, offDiagSep beta gam k0 j / 2,
    1 + 2 * offDiagLen beta gam k0 j, 1 + 3 * offDiagLen beta gam k0 j,
    by linarith, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · -- the scale condition `δ ^ θ ≤ b - a`
    have hdiff : (1 + 3 * offDiagLen beta gam k0 j) - (1 + 2 * offDiagLen beta gam k0 j)
        = offDiagLen beta gam k0 j := by ring
    rw [hdiff]
    have hδeq : offDiagSep beta gam k0 j / 2
        = (1 / 8) * ((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ j := by
      rw [offDiagSep_eq_pow]
      ring
    have hLeq : offDiagLen beta gam k0 j = (1 / 4) * ((offDiagRatio beta gam) ^ k0) ^ j :=
      offDiagLen_eq_pow k0 j
    rw [hδeq, hLeq]
    have hnujpos : (0 : ℝ) < (((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ) ^ j := by
      have : (0 : ℝ) < ((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ :=
        Real.rpow_pos_of_pos hnu0 θ
      positivity
    have hsplit : ((1 / 8 : ℝ) * ((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ j) ^ θ
        = (1 / 8 : ℝ) ^ θ *
          ((((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ) ^ j) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      exact (rpow_pow_comm' hnu0 θ j).symm
    rw [hsplit]
    have hj1' := hj1 j hj1le
    rw [div_pow] at hj1'
    -- rearrange
    have hkey : (1 / 8 : ℝ) ^ θ / (1 / 4) *
        (((((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ) ^ j)) ≤
        (((offDiagRatio beta gam) ^ k0) ^ j /
          ((((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ) ^ j)) *
          (((((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ) ^ j)) := by
      exact mul_le_mul_of_nonneg_right hj1' hnujpos.le
    rw [div_mul_cancel₀ _ hnujpos.ne'] at hkey
    have hfinal : (1 / 8 : ℝ) ^ θ *
        (((((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ) ^ j)) ≤
        (1 / 4 : ℝ) * (((offDiagRatio beta gam) ^ k0) ^ j) := by
      have h4 : (0 : ℝ) < 1 / 4 := by norm_num
      have := mul_le_mul_of_nonneg_left hkey h4.le
      calc (1 / 8 : ℝ) ^ θ *
            (((((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ) ^ j))
          = (1 / 4 : ℝ) * ((1 / 8 : ℝ) ^ θ / (1 / 4) *
              (((((cantorRatio gam) ^ k0 * (offDiagRatio beta gam) ^ k0) ^ θ) ^ j))) := by
            field_simp
        _ ≤ (1 / 4 : ℝ) * (((offDiagRatio beta gam) ^ k0) ^ j) := this
    exact hfinal
  · -- the points belong to the set and the interval
    intro x hx
    refine ⟨Set.mem_iUnion.mpr ⟨j, hx⟩, ?_⟩
    obtain ⟨h1, h2⟩ := offDiagPiece_subset_Icc hgam hgam1 k0 j x hx
    exact ⟨h1, h2⟩
  · -- separation
    intro x hx y hy hxy
    have hsep := cantorMid_separated hmu hmu2 (k0 * j) hLpos.le hx hy hxy
    have hσeq : offDiagSep beta gam k0 j
        = (cantorRatio gam) ^ (k0 * j) * offDiagLen beta gam k0 j := rfl
    rw [← hσeq] at hsep
    linarith
  · -- the cardinality condition
    have hcard : ((offDiagPiece beta gam k0 j).card : ℝ)
        = (((cantorRatio gam) ^ k0) ^ j) ^ (-gam) := by
      rw [offDiagPiece_card hgam hgam1 k0 j]
      push_cast
      rw [← hmu0j, ← cantorRatio_pow_rpow_neg hgam (k0 * j)]
    have hdiff : (1 + 3 * offDiagLen beta gam k0 j) - (1 + 2 * offDiagLen beta gam k0 j)
        = offDiagLen beta gam k0 j := by ring
    rw [hcard, hdiff]
    -- the ratio of the two scales
    have hratio : offDiagLen beta gam k0 j / (offDiagSep beta gam k0 j / 2)
        = 2 / ((cantorRatio gam) ^ k0) ^ j := by
      rw [offDiagSep, ← hmu0j]
      field_simp
    rw [hratio]
    -- the numerical comparison
    set w : ℝ := ((cantorRatio gam) ^ k0) ^ j with hwdef
    have hw0 : 0 < w := by
      rw [hwdef]
      positivity
    have hwt2 : w ≤ t2 := hj2 j hj2le
    have hwpow : w ^ (gam - gam') ≤ 1 / K2 := by
      have hmono : w ^ (gam - gam') ≤ t2 ^ (gam - gam') :=
        Real.rpow_le_rpow hw0.le hwt2 hgapgam.le
      have ht2pow : t2 ^ (gam - gam') = 1 / K2 := by
        rw [ht2def, ← Real.rpow_mul (by positivity)]
        rw [one_div_mul_cancel (by linarith : gam - gam' ≠ 0), Real.rpow_one]
      rw [ht2pow] at hmono
      exact hmono
    have hbig : K2 ≤ w ^ (-(gam - gam')) := by
      have hpos : 0 < w ^ (gam - gam') := Real.rpow_pos_of_pos hw0 _
      rw [Real.rpow_neg hw0.le]
      rw [le_inv_comm₀ hK2 hpos]
      calc w ^ (gam - gam') ≤ 1 / K2 := hwpow
        _ = K2⁻¹ := by rw [one_div]
    have hsplit1 : (2 / w) ^ gam' = (2 : ℝ) ^ gam' * w ^ (-gam') := by
      rw [Real.div_rpow (by norm_num) hw0.le, Real.rpow_neg hw0.le]
      field_simp
    have hsplit2 : w ^ (-gam) = w ^ (-gam') * w ^ (-(gam - gam')) := by
      rw [← Real.rpow_add hw0]
      congr 1
      ring
    have hwneg : 0 < w ^ (-gam') := Real.rpow_pos_of_pos hw0 _
    rw [hsplit1, hsplit2]
    calc C * ((2 : ℝ) ^ gam' * w ^ (-gam'))
        = (C * (2 : ℝ) ^ gam') * w ^ (-gam') := by ring
      _ < K2 * w ^ (-gam') := by
          refine mul_lt_mul_of_pos_right ?_ hwneg
          rw [hK2def]
          linarith
      _ ≤ w ^ (-(gam - gam')) * w ^ (-gam') := by
          exact mul_le_mul_of_nonneg_right hbig hwneg.le
      _ = w ^ (-gam') * w ^ (-(gam - gam')) := by ring

/-! ### The off-diagonal example is regular -/

theorem upperMinkowskiDimension_offDiagSet {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) :
    upperMinkowskiDimension (offDiagSet beta gam k0) = beta := by
  refine upperMinkowskiDimension_eq_of_bounds hbeta.le
    (hasUpperMinkowskiExponent_offDiagSet hbeta hbg hgam1 hk0pos hk0) ?_
  intro beta' hbeta'0 hlt
  exact not_hasUpperMinkowskiExponent_offDiagSet hbeta hbg hgam1 hk0pos hbeta'0 hlt

theorem upperAssouadSpectrum_offDiagSet_le {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) {θ : ℝ} (hθ1 : θ ≤ 1) :
    upperAssouadSpectrum (offDiagSet beta gam k0) θ ≤ gam := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  refine csInf_le ⟨0, fun g hg => hg.1⟩ ⟨hgam.le, ?_⟩
  exact hasUpperAssouadSpectrumExponent_offDiagSet hbeta hbg hgam1 hk0pos hk0 hθ1

theorem upperAssouadSpectrum_offDiagSet {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) {θ : ℝ}
    (hθ : 1 - beta / gam < θ) (hθ1 : θ ≤ 1) :
    upperAssouadSpectrum (offDiagSet beta gam k0) θ = gam := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  refine upperAssouadSpectrum_eq_of_bounds hgam.le
    (hasUpperAssouadSpectrumExponent_offDiagSet hbeta hbg hgam1 hk0pos hk0 hθ1) ?_
  intro gam' hgam'0 hlt
  exact not_hasUpperAssouadSpectrumExponent_offDiagSet hbeta hbg hgam1 hk0pos hθ hgam'0 hlt

theorem quasiAssouadDimension_offDiagSet {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) :
    quasiAssouadDimension (offDiagSet beta gam k0) = gam := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  have hcrit : 1 - beta / gam < 1 := by
    have : 0 < beta / gam := div_pos hbeta hgam
    linarith
  have hcrit0 : 0 ≤ 1 - beta / gam := by
    have hle : beta / gam ≤ 1 := by
      rw [div_le_one hgam]
      linarith
    linarith
  refine quasiAssouadDimension_eq_of_spectrum ?_ ?_
  · intro θ hθ0 hθ1
    exact upperAssouadSpectrum_offDiagSet_le hbeta hbg hgam1 hk0pos hk0 hθ1.le
  · intro ε hε
    -- pick a scale parameter above the critical one
    refine ⟨(1 - beta / gam + 1) / 2, by linarith, by linarith, ?_⟩
    rw [upperAssouadSpectrum_offDiagSet hbeta hbg hgam1 hk0pos hk0 (by linarith) (by linarith)]
    linarith

/-- **The off-diagonal example is `(β,γ)`-quasi-Assouad regular.** -/
theorem isQuasiAssouadRegular_offDiagSet {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) :
    IsQuasiAssouadRegular (offDiagSet beta gam k0) beta gam := by
  refine ⟨upperMinkowskiDimension_offDiagSet hbeta hbg hgam1 hk0pos hk0,
    quasiAssouadDimension_offDiagSet hbeta hbg hgam1 hk0pos hk0, Or.inr ?_⟩
  intro θ hθ0 hθ1 hθcrit
  exact upperAssouadSpectrum_offDiagSet hbeta hbg hgam1 hk0pos hk0 hθcrit hθ1.le

/-! ### Every admissible pair is realized -/

/-- **For every pair `0 ≤ β ≤ γ ≤ 1` with `β = 0 → γ = 0` there is an explicit
`(β,γ)`-quasi-Assouad regular subset of `[1,2]`.** -/
theorem exists_isQuasiAssouadRegular {beta gam : ℝ} (hbeta : 0 ≤ beta) (hbg : beta ≤ gam)
    (hgam1 : gam ≤ 1) (hzero : beta = 0 → gam = 0) :
    ∃ E : Set ℝ, E ⊆ Icc (1 : ℝ) 2 ∧ E.Nonempty ∧ IsQuasiAssouadRegular E beta gam := by
  rcases eq_or_lt_of_le hbeta with hb0 | hbpos
  · -- `β = 0`, hence `γ = 0`
    have hg0 : gam = 0 := hzero hb0.symm
    refine ⟨{1}, ?_, ⟨1, rfl⟩, ?_⟩
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨le_refl _, by norm_num⟩
    · rw [← hb0, hg0]
      exact isQuasiAssouadRegular_singleton 1
  · rcases eq_or_lt_of_le hbg with hbeq | hblt
    · -- the diagonal case
      subst hbeq
      refine ⟨cantorSet (cantorRatio beta) 1 1, ?_, ?_, ?_⟩
      · exact cantorSet_subset_Icc_one_two 1 (le_refl _) (by norm_num)
      · exact cantorSet_nonempty hbpos hgam1 1
      · exact isQuasiAssouadRegular_cantorSet hbpos hgam1 1 (le_refl _) (by norm_num)
    · -- the off-diagonal case
      have hgam : 0 < gam := lt_trans hbpos hblt
      have hr0 : 0 < offDiagRatio beta gam := offDiagRatio_pos beta gam
      have hr1 : offDiagRatio beta gam < 1 := offDiagRatio_lt_one hbpos hblt
      obtain ⟨k0, hk0⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ) < 1 / 3) hr1
      have hk0pos : 1 ≤ k0 := by
        rcases Nat.eq_zero_or_pos k0 with h0 | h
        · rw [h0] at hk0
          simp only [pow_zero] at hk0
          linarith
        · exact h
      refine ⟨offDiagSet beta gam k0, ?_, offDiagSet_nonempty k0, ?_⟩
      · exact offDiagSet_subset_Icc hbpos hblt hgam hgam1 k0
      · exact isQuasiAssouadRegular_offDiagSet hbpos hblt hgam1 hk0pos hk0.le


end

end Auto.Spherical.FractalDilations.RS
