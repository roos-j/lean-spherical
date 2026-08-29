/-
Roos--Seeger type-set characterization and Theorem 1.2 work.
All declarations use `Auto.Spherical.FractalDilations.RSTypeSetCharacterization`.
-/

import LeanSpherical.Auto.Spherical.FractalDilations.RSLowerBounds
import LeanSpherical.Auto.Spherical.FractalDilations.RSUpperBounds

namespace Auto.Spherical.FractalDilations.RSTypeSetCharacterization
open Auto.Spherical.FractalDilations.RSUpperBounds
open Auto.Spherical.FractalDilations.RSLowerBounds
open MeasureTheory Metric Set
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open scoped ENNReal NNReal Real FourierTransform Convolution

noncomputable section

/-! ## The type set

Theorem 1.2 of the paper describes which subsets of `[0,1]²` arise as closures of type sets.
The type set is the set of reciprocal exponent points for which the fractal spherical maximal
operator is of strong type. -/

/-- The type set `T_E` of the fractal spherical maximal operator, in the reciprocal coordinates
`(1/p, 1/q)` and in the Banach range `q ≥ 1` used throughout the repository. -/
def fractalTypeSet (d : ℕ) (E : Set ℝ) : Set ExponentPoint :=
  {z | ∃ p q : ℝ, 0 < p ∧ 1 ≤ q ∧ z = reciprocalExponentPoint p q ∧
    HasFractalSphericalStrongType d E p q}

/-! ### The interior of `Q` -/

/-- The four strict sharpness inequalities place a point in the interior of `Q(β,γ)`. -/
theorem mem_interior_Q_of_strict {d : ℕ} {beta gam : ℝ} {x : ExponentPoint}
    (hd : 2 ≤ d) (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1) (hbg : beta ≤ gam)
    (h1 : x.2 < x.1) (h2 : x.1 < (d : ℝ) * x.2)
    (h3 : (d : ℝ) * x.1 < (1 - beta) * x.2 + ((d : ℝ) - 1))
    (h4 : 0 < clusterEdgeFunctional d (beta / gam) beta x) :
    x ∈ interior (Q d beta gam) := by
  have hUopen : IsOpen {y : ExponentPoint | y.2 < y.1 ∧ y.1 < (d : ℝ) * y.2 ∧
      (d : ℝ) * y.1 < (1 - beta) * y.2 + ((d : ℝ) - 1) ∧
      0 < clusterEdgeFunctional d (beta / gam) beta y} := by
    have hset : {y : ExponentPoint | y.2 < y.1 ∧ y.1 < (d : ℝ) * y.2 ∧
        (d : ℝ) * y.1 < (1 - beta) * y.2 + ((d : ℝ) - 1) ∧
        0 < clusterEdgeFunctional d (beta / gam) beta y} =
        ((fun y : ExponentPoint => y.1 - y.2) ⁻¹' Ioi 0) ∩
          (((fun y : ExponentPoint => (d : ℝ) * y.2 - y.1) ⁻¹' Ioi 0) ∩
            (((fun y : ExponentPoint =>
                (1 - beta) * y.2 + ((d : ℝ) - 1) - (d : ℝ) * y.1) ⁻¹' Ioi 0) ∩
              ((fun y : ExponentPoint =>
                clusterEdgeFunctional d (beta / gam) beta y) ⁻¹' Ioi 0))) := by
      ext y
      simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioi, sub_pos]
    have hcontclu : Continuous fun y : ExponentPoint =>
        clusterEdgeFunctional d (beta / gam) beta y := by
      have hfun : (fun y : ExponentPoint => clusterEdgeFunctional d (beta / gam) beta y)
          = fun y : ExponentPoint => beta / gam / 2 * ((d : ℝ) - 1)
            + ((d : ℝ) - beta - ((d : ℝ) - 1) * (beta / gam) / 2) * y.2
            - (1 + beta / gam / 2 * ((d : ℝ) - 1)) * y.1 := by
        funext y
        simp only [clusterEdgeFunctional]
        ring
      rw [hfun]
      continuity
    rw [hset]
    refine IsOpen.inter ?_ (IsOpen.inter ?_ (IsOpen.inter ?_ ?_))
    · exact isOpen_Ioi.preimage (by continuity)
    · exact isOpen_Ioi.preimage (by continuity)
    · exact isOpen_Ioi.preimage (by continuity)
    · exact isOpen_Ioi.preimage hcontclu
  have hUsub : {y : ExponentPoint | y.2 < y.1 ∧ y.1 < (d : ℝ) * y.2 ∧
      (d : ℝ) * y.1 < (1 - beta) * y.2 + ((d : ℝ) - 1) ∧
      0 < clusterEdgeFunctional d (beta / gam) beta y} ⊆ Q d beta gam := by
    intro y hy
    rw [mem_Q_iff_not_sharpnessViolation hd hbeta hbeta1 hbg]
    intro hbad
    rcases hbad with hb | hb | hb | hb
    · exact absurd hb (not_lt.mpr hy.1.le)
    · exact absurd hb (not_lt.mpr hy.2.1.le)
    · exact absurd hb (not_lt.mpr hy.2.2.1.le)
    · exact absurd hb (not_lt.mpr hy.2.2.2.le)
  exact interior_maximal hUsub hUopen ⟨h1, h2, h3, h4⟩

/-- An elementary scaling lemma: a positive constant term, or a positive linear coefficient,
makes an affine function of a small positive parameter positive. -/
theorem exists_small_positive_affine {A X c0 : ℝ} (hA : 0 ≤ A) (hc0 : 0 < c0)
    (hpos : 0 < A ∨ 0 < X) : ∃ t : ℝ, 0 < t ∧ t ≤ c0 ∧ 0 < A + X * t := by
  rcases hpos with hA' | hX
  · have hden : (0 : ℝ) < 2 * (|X| + 1) := by positivity
    have hquot : (0 : ℝ) < A / (2 * (|X| + 1)) := div_pos hA' hden
    refine ⟨min c0 (A / (2 * (|X| + 1))), lt_min hc0 hquot, min_le_left _ _, ?_⟩
    have ht : (0 : ℝ) < min c0 (A / (2 * (|X| + 1))) := lt_min hc0 hquot
    have h1 : min c0 (A / (2 * (|X| + 1))) ≤ A / (2 * (|X| + 1)) := min_le_right _ _
    have h2 : |X * min c0 (A / (2 * (|X| + 1)))| ≤ A / 2 := by
      rw [abs_mul, abs_of_nonneg ht.le]
      have hstep : |X| * min c0 (A / (2 * (|X| + 1))) ≤ (|X| + 1) * (A / (2 * (|X| + 1))) := by
        apply mul_le_mul (by linarith) h1 ht.le (by positivity)
      have hval : (|X| + 1) * (A / (2 * (|X| + 1))) = A / 2 := by
        field_simp
      linarith [hstep, hval]
    have h3 := neg_abs_le (X * min c0 (A / (2 * (|X| + 1))))
    linarith
  · refine ⟨c0, hc0, le_refl _, ?_⟩
    have : 0 < X * c0 := mul_pos hX hc0
    linarith

/-- The interior of `Q(β,γ)` is nonempty. -/
theorem interior_Q_nonempty {d : ℕ} {beta gam : ℝ}
    (hd : 2 ≤ d) (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1) (hbg : beta ≤ gam) :
    (interior (Q d beta gam)).Nonempty := by
  have hD : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hc1 : (1 : ℝ) < (1 + (d : ℝ)) / 2 := by linarith
  have hcD : (1 + (d : ℝ)) / 2 < (d : ℝ) := by linarith
  have hcpos : (0 : ℝ) < (1 + (d : ℝ)) / 2 := by linarith
  have hal0 : (0 : ℝ) ≤ beta / gam := by
    rcases le_or_gt gam 0 with hg | hg
    · have hb0 : beta = 0 := le_antisymm (le_trans hbg hg) hbeta
      rw [hb0]
      simp
    · exact div_nonneg hbeta hg.le
  have hA0 : (0 : ℝ) ≤ beta / gam / 2 * ((d : ℝ) - 1) := by
    apply mul_nonneg (by linarith) (by linarith)
  have hc0pos : (0 : ℝ) < ((d : ℝ) - 1) / (2 * (d : ℝ) * ((1 + (d : ℝ)) / 2)) := by
    apply div_pos (by linarith) (by positivity)
  have hpos : 0 < beta / gam / 2 * ((d : ℝ) - 1) ∨
      0 < ((d : ℝ) - beta - ((d : ℝ) - 1) * (beta / gam) / 2) -
        (1 + beta / gam / 2 * ((d : ℝ) - 1)) * ((1 + (d : ℝ)) / 2) := by
    rcases eq_or_lt_of_le hal0 with hal | hal
    · -- `β / γ = 0` forces `β = 0`
      right
      have hb0 : beta = 0 := by
        by_contra hne
        have hbpos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hne)
        have hgpos : 0 < gam := lt_of_lt_of_le hbpos hbg
        have hpos2 : 0 < beta / gam := div_pos hbpos hgpos
        rw [← hal] at hpos2
        exact absurd hpos2 (lt_irrefl _)
      have hzero : beta / gam = 0 := hal.symm
      rw [hzero, hb0]
      norm_num
      linarith [hcD, hD]
    · left
      apply _root_.mul_pos (by linarith) (by linarith)
  obtain ⟨t, htpos, htle, hclu⟩ :=
    exists_small_positive_affine hA0 hc0pos hpos
  refine ⟨((1 + (d : ℝ)) / 2 * t, t), ?_⟩
  refine mem_interior_Q_of_strict hd hbeta hbeta1 hbg ?_ ?_ ?_ ?_
  · show t < (1 + (d : ℝ)) / 2 * t
    nlinarith [htpos, hc1]
  · show (1 + (d : ℝ)) / 2 * t < (d : ℝ) * t
    nlinarith [htpos, hcD]
  · show (d : ℝ) * ((1 + (d : ℝ)) / 2 * t) < (1 - beta) * t + ((d : ℝ) - 1)
    have hmul : (d : ℝ) * ((1 + (d : ℝ)) / 2) * t ≤ ((d : ℝ) - 1) / 2 := by
      have hval : (d : ℝ) * ((1 + (d : ℝ)) / 2) *
          (((d : ℝ) - 1) / (2 * (d : ℝ) * ((1 + (d : ℝ)) / 2))) = ((d : ℝ) - 1) / 2 := by
        field_simp
      calc (d : ℝ) * ((1 + (d : ℝ)) / 2) * t ≤
            (d : ℝ) * ((1 + (d : ℝ)) / 2) *
              (((d : ℝ) - 1) / (2 * (d : ℝ) * ((1 + (d : ℝ)) / 2))) := by
            apply mul_le_mul_of_nonneg_left htle (by positivity)
        _ = ((d : ℝ) - 1) / 2 := hval
    have hbt : 0 ≤ (1 - beta) * t := mul_nonneg (by linarith) htpos.le
    nlinarith [hmul, hbt]
  · show 0 < clusterEdgeFunctional d (beta / gam) beta ((1 + (d : ℝ)) / 2 * t, t)
    have hgoal : clusterEdgeFunctional d (beta / gam) beta ((1 + (d : ℝ)) / 2 * t, t)
        = beta / gam / 2 * ((d : ℝ) - 1) +
          (((d : ℝ) - beta - ((d : ℝ) - 1) * (beta / gam) / 2) -
            (1 + beta / gam / 2 * ((d : ℝ) - 1)) * ((1 + (d : ℝ)) / 2)) * t := by
      unfold clusterEdgeFunctional
      dsimp only
      ring
    rw [hgoal]
    exact hclu

/-! ### The type set contains the interior of `Q` -/

/-- Every interior point of `Q(β,γ)` is a point of strong type: this is Theorem 1.1 read in
the exponent plane. -/
theorem interior_Q_subset_fractalTypeSet
    {d : ℕ} {E : Set ℝ} {beta gam : ℝ} (hd : 2 ≤ d)
    (hE : E ⊆ Icc (1 : ℝ) 2)
    (hbeta : 0 ≤ beta) (hbg : beta ≤ gam) (hgam : gam ≤ 1)
    (hMink : upperMinkowskiDimension E = beta) (hquasi : quasiAssouadDimension E = gam) :
    interior (Q d beta gam) ⊆ fractalTypeSet d E := by
  intro x hx
  have hbeta1 : beta ≤ 1 := le_trans hbg hgam
  have hgamnn : (0 : ℝ) ≤ gam := le_trans hbeta hbg
  have hD : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h21 : x.2 < x.1 := strict_second_lt_first_of_mem_interior_Q hd hbeta1 hgamnn hx
  have hcap : x.1 < (d : ℝ) * x.2 :=
    strict_first_lt_natCast_mul_second_of_mem_interior_Q hd hbeta hbeta1 hgamnn hx
  have hone : x.1 < 1 := strict_first_lt_one_of_mem_interior_Q hd hbeta hbeta1 hbg hx
  have h2pos : 0 < x.2 := by
    by_contra hcon
    have hle : x.2 ≤ 0 := not_lt.mp hcon
    have : (d : ℝ) * x.2 ≤ x.2 := by nlinarith [hle, hD]
    linarith
  have h1pos : 0 < x.1 := lt_trans h2pos h21
  refine ⟨x.1⁻¹, x.2⁻¹, by positivity, ?_, ?_, ?_⟩
  · rw [le_inv_comm₀ (by norm_num) h2pos]
    linarith
  · rw [reciprocalExponentPoint, inv_inv, inv_inv]
  · refine theorem_one_unrestricted hd hE hbeta hbg hgam hMink hquasi (by positivity) ?_ ?_
    · rw [le_inv_comm₀ (by norm_num) h2pos]
      linarith
    · have hz : reciprocalExponentPoint x.1⁻¹ x.2⁻¹ = x := by
        rw [reciprocalExponentPoint, inv_inv, inv_inv]
      rw [hz]
      exact Or.inr hx

/-- `Q(β,γ)` is contained in the closure of the type set. -/
theorem Q_subset_closure_fractalTypeSet
    {d : ℕ} {E : Set ℝ} {beta gam : ℝ} (hd : 2 ≤ d)
    (hE : E ⊆ Icc (1 : ℝ) 2)
    (hbeta : 0 ≤ beta) (hbg : beta ≤ gam) (hgam : gam ≤ 1)
    (hMink : upperMinkowskiDimension E = beta) (hquasi : quasiAssouadDimension E = gam) :
    Q d beta gam ⊆ closure (fractalTypeSet d E) := by
  have hbeta1 : beta ≤ 1 := le_trans hbg hgam
  have hne := interior_Q_nonempty hd hbeta hbeta1 hbg
  have hclos : closure (interior (Q d beta gam)) = Q d beta gam := by
    rw [(convex_Q d beta gam).closure_interior_eq_closure_of_nonempty_interior hne]
    exact (isClosed_Q d beta gam).closure_eq
  calc Q d beta gam = closure (interior (Q d beta gam)) := hclos.symm
    _ ⊆ closure (fractalTypeSet d E) :=
      closure_mono (interior_Q_subset_fractalTypeSet hd hE hbeta hbg hgam hMink hquasi)

/-! ### The type set is contained in `Q` -/

/-- Strong type and unboundedness are incompatible. -/
theorem not_unbounded_of_hasFractalSphericalStrongType
    {d : ℕ} {E : Set ℝ} {p q : ℝ}
    (h : HasFractalSphericalStrongType d E p q) :
    ¬ FractalSphericalUnbounded d E p q := by
  intro hun
  obtain ⟨C, hC, hbound⟩ := h
  obtain ⟨f, hf1, hf2⟩ := hun C hC
  have h1 := (hbound f).2
  have h2 : ENNReal.ofReal C *
      eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C := by
    calc ENNReal.ofReal C * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal C * 1 := by gcongr
      _ = ENNReal.ofReal C := mul_one _
  exact absurd (lt_of_lt_of_le hf2 (le_trans h1 h2)) (lt_irrefl _)

/-- The Minkowski sharpness assertion of Theorem 2 of arXiv:1909.05389 confines the type set
to `Q(β,β)`. -/
theorem fractalTypeSet_subset_Q_self
    {d : ℕ} {E : Set ℝ} {beta : ℝ} (hd : 2 ≤ d)
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hMink : upperMinkowskiDimension E = beta) :
    fractalTypeSet d E ⊆ Q d beta beta := by
  intro z hz
  obtain ⟨p, q, hp, hq, hzeq, hst⟩ := hz
  by_contra hnot
  refine not_unbounded_of_hasFractalSphericalStrongType hst ?_
  refine Auto.Spherical.FractalDilations.AHRSUpperBounds.theorem_two_i hd E hE hEne
    ⟨hbeta, hbeta1⟩ hMink hp hq ?_
  rw [← hzeq]
  exact hnot

/-- For a quasi-Assouad regular set the sharpness assertion confines the type set to
`Q(β,γ)`. -/
theorem fractalTypeSet_subset_Q_of_regular
    {d : ℕ} {E : Set ℝ} {beta gam : ℝ} (hd : 2 ≤ d)
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    (hbg : 0 ≤ beta ∧ beta ≤ gam ∧ gam ≤ 1)
    (hreg : IsQuasiAssouadRegular E beta gam) :
    fractalTypeSet d E ⊆ Q d beta gam := by
  intro z hz
  obtain ⟨p, q, hp, hq, hzeq, hst⟩ := hz
  by_contra hnot
  refine not_unbounded_of_hasFractalSphericalStrongType hst ?_
  refine Auto.Spherical.FractalDilations.AHRSUpperBounds.theorem_two_iii hd E hE hEne hbg hreg
    hp hq ?_
  rw [← hzeq]
  exact hnot

/-! ### The type set of a quasi-Assouad regular set -/

/-- **The closure of the type set of a `(β,γ)`-quasi-Assouad regular set is exactly
`Q(β,γ)`.**  The inclusion `⊇` is Theorem 1.1; the inclusion `⊆` is the sharpness part of
Theorem 2 of arXiv:1909.05389. -/
theorem closure_fractalTypeSet_eq_Q_of_regular
    {d : ℕ} {E : Set ℝ} {beta gam : ℝ} (hd : 2 ≤ d)
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    (hbg : 0 ≤ beta ∧ beta ≤ gam ∧ gam ≤ 1)
    (hreg : IsQuasiAssouadRegular E beta gam) :
    closure (fractalTypeSet d E) = Q d beta gam := by
  obtain ⟨hbeta, hbetagam, hgam⟩ := hbg
  refine le_antisymm ?_ ?_
  · exact closure_minimal
      (fractalTypeSet_subset_Q_of_regular hd hE hEne ⟨hbeta, hbetagam, hgam⟩ hreg)
      (isClosed_Q d beta gam)
  · exact Q_subset_closure_fractalTypeSet hd hE hbeta hbetagam hgam hreg.1 hreg.2.1

/-! ### A uniform family of interior points of `Q` -/

/-- A positive constant term, or a positive linear coefficient, makes an affine function of a
small positive parameter positive, uniformly for small parameters. -/
theorem exists_bound_positive_affine {A X : ℝ} (hA : 0 ≤ A) (hpos : 0 < A ∨ 0 < X) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ t : ℝ, 0 < t → t ≤ t0 → 0 < A + X * t := by
  rcases hpos with hA' | hX
  · refine ⟨A / (2 * (|X| + 1)), by positivity, fun t htpos htle => ?_⟩
    have h2 : |X * t| ≤ A / 2 := by
      rw [abs_mul, abs_of_nonneg htpos.le]
      have hstep : |X| * t ≤ (|X| + 1) * (A / (2 * (|X| + 1))) :=
        mul_le_mul (by linarith) htle htpos.le (by positivity)
      have hval : (|X| + 1) * (A / (2 * (|X| + 1))) = A / 2 := by
        field_simp
      linarith
    have h3 := neg_abs_le (X * t)
    linarith
  · refine ⟨1, one_pos, fun t htpos _ => ?_⟩
    have hXt : 0 < X * t := mul_pos hX htpos
    linarith

/-- All sufficiently small points on the ray `t ↦ ((1+d)t/2, t)` lie in the interior of
`Q(β,γ)`. -/
theorem exists_pos_bound_mem_interior_Q {d : ℕ} {beta gam : ℝ}
    (hd : 2 ≤ d) (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1) (hbg : beta ≤ gam) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ t : ℝ, 0 < t → t ≤ t0 →
      ((1 + (d : ℝ)) / 2 * t, t) ∈ interior (Q d beta gam) := by
  have hD : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hc1 : (1 : ℝ) < (1 + (d : ℝ)) / 2 := by linarith
  have hcD : (1 + (d : ℝ)) / 2 < (d : ℝ) := by linarith
  have hcpos : (0 : ℝ) < (1 + (d : ℝ)) / 2 := by linarith
  have hal0 : (0 : ℝ) ≤ beta / gam := by
    rcases le_or_gt gam 0 with hg | hg
    · have hb0 : beta = 0 := le_antisymm (le_trans hbg hg) hbeta
      rw [hb0]
      simp
    · exact div_nonneg hbeta hg.le
  have hA0 : (0 : ℝ) ≤ beta / gam / 2 * ((d : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hpos : 0 < beta / gam / 2 * ((d : ℝ) - 1) ∨
      0 < ((d : ℝ) - beta - ((d : ℝ) - 1) * (beta / gam) / 2) -
        (1 + beta / gam / 2 * ((d : ℝ) - 1)) * ((1 + (d : ℝ)) / 2) := by
    rcases eq_or_lt_of_le hal0 with hal | hal
    · right
      have hb0 : beta = 0 := by
        by_contra hne
        have hbpos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hne)
        have hgpos : 0 < gam := lt_of_lt_of_le hbpos hbg
        have hpos2 : 0 < beta / gam := div_pos hbpos hgpos
        rw [← hal] at hpos2
        exact absurd hpos2 (lt_irrefl _)
      have hzero : beta / gam = 0 := hal.symm
      rw [hzero, hb0]
      norm_num
      linarith [hcD, hD]
    · left
      exact _root_.mul_pos (by linarith) (by linarith)
  obtain ⟨t1, ht1pos, ht1⟩ := exists_bound_positive_affine hA0 hpos
  refine ⟨min t1 (((d : ℝ) - 1) / (2 * (d : ℝ) * ((1 + (d : ℝ)) / 2))), ?_, ?_⟩
  · exact lt_min ht1pos (div_pos (by linarith) (by positivity))
  intro t htpos htle
  have htle1 : t ≤ t1 := le_trans htle (min_le_left _ _)
  have htle2 : t ≤ ((d : ℝ) - 1) / (2 * (d : ℝ) * ((1 + (d : ℝ)) / 2)) :=
    le_trans htle (min_le_right _ _)
  have hclu := ht1 t htpos htle1
  refine mem_interior_Q_of_strict hd hbeta hbeta1 hbg ?_ ?_ ?_ ?_
  · show t < (1 + (d : ℝ)) / 2 * t
    nlinarith [htpos, hc1]
  · show (1 + (d : ℝ)) / 2 * t < (d : ℝ) * t
    nlinarith [htpos, hcD]
  · show (d : ℝ) * ((1 + (d : ℝ)) / 2 * t) < (1 - beta) * t + ((d : ℝ) - 1)
    have hmul : (d : ℝ) * ((1 + (d : ℝ)) / 2) * t ≤ ((d : ℝ) - 1) / 2 := by
      have hval : (d : ℝ) * ((1 + (d : ℝ)) / 2) *
          (((d : ℝ) - 1) / (2 * (d : ℝ) * ((1 + (d : ℝ)) / 2))) = ((d : ℝ) - 1) / 2 := by
        field_simp
      calc (d : ℝ) * ((1 + (d : ℝ)) / 2) * t ≤
            (d : ℝ) * ((1 + (d : ℝ)) / 2) *
              (((d : ℝ) - 1) / (2 * (d : ℝ) * ((1 + (d : ℝ)) / 2))) := by
            exact mul_le_mul_of_nonneg_left htle2 (by positivity)
        _ = ((d : ℝ) - 1) / 2 := hval
    have hbt : 0 ≤ (1 - beta) * t := mul_nonneg (by linarith) htpos.le
    nlinarith [hmul, hbt]
  · show 0 < clusterEdgeFunctional d (beta / gam) beta ((1 + (d : ℝ)) / 2 * t, t)
    have hgoal : clusterEdgeFunctional d (beta / gam) beta ((1 + (d : ℝ)) / 2 * t, t)
        = beta / gam / 2 * ((d : ℝ) - 1) +
          (((d : ℝ) - beta - ((d : ℝ) - 1) * (beta / gam) / 2) -
            (1 + beta / gam / 2 * ((d : ℝ) - 1)) * ((1 + (d : ℝ)) / 2)) * t := by
      unfold clusterEdgeFunctional
      dsimp only
      ring
    rw [hgoal]
    exact hclu

/-- Finitely many regions `Q(β_j, γ_j)` have a common interior point. -/
theorem exists_common_mem_interior_Q {d : ℕ} {ι : Type*} {betas gams : ι → ℝ}
    (hd : 2 ≤ d) (s : Finset ι) (hs : s.Nonempty)
    (hbg : ∀ j ∈ s, 0 ≤ betas j ∧ betas j ≤ gams j ∧ gams j ≤ 1) :
    ∃ z : ExponentPoint, ∀ j ∈ s, z ∈ interior (Q d (betas j) (gams j)) := by
  classical
  have hchoice : ∀ j ∈ s, ∃ t0 : ℝ, 0 < t0 ∧ ∀ t : ℝ, 0 < t → t ≤ t0 →
      ((1 + (d : ℝ)) / 2 * t, t) ∈ interior (Q d (betas j) (gams j)) := by
    intro j hj
    obtain ⟨hb, hbg', hg⟩ := hbg j hj
    exact exists_pos_bound_mem_interior_Q hd hb (le_trans hbg' hg) hbg'
  choose! t0 ht0pos ht0 using hchoice
  have hpos : 0 < s.inf' hs t0 := (Finset.lt_inf'_iff hs).mpr fun i hi => ht0pos i hi
  refine ⟨((1 + (d : ℝ)) / 2 * (s.inf' hs t0), s.inf' hs t0), fun j hj => ?_⟩
  exact ht0 j hj _ hpos (Finset.inf'_le _ hj)

/-- The closure of the intersection of the interiors is the intersection of the regions. -/
theorem closure_biInter_interior_Q_eq {d : ℕ} {ι : Type*} {betas gams : ι → ℝ}
    (hd : 2 ≤ d) (s : Finset ι) (hs : s.Nonempty)
    (hbg : ∀ j ∈ s, 0 ≤ betas j ∧ betas j ≤ gams j ∧ gams j ≤ 1) :
    closure (⋂ j ∈ s, interior (Q d (betas j) (gams j))) =
      ⋂ j ∈ s, Q d (betas j) (gams j) := by
  refine le_antisymm ?_ ?_
  · refine closure_minimal ?_
      (isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_Q d _ _)
    exact Set.iInter₂_mono fun j _ => interior_subset
  · intro x hx
    obtain ⟨y, hy⟩ := exists_common_mem_interior_Q hd s hs hbg
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hDnn : (0 : ℝ) ≤ dist y x := dist_nonneg
    have hden : (0 : ℝ) < 2 * (dist y x + 1) := by positivity
    have hquot : (0 : ℝ) < ε / (2 * (dist y x + 1)) := div_pos hε hden
    refine ⟨min 1 (ε / (2 * (dist y x + 1))) • y +
      (1 - min 1 (ε / (2 * (dist y x + 1)))) • x, ?_, ?_⟩
    · refine Set.mem_iInter₂.mpr fun j hj => ?_
      refine (convex_Q d (betas j) (gams j)).combo_interior_self_mem_interior (hy j hj)
        (Set.mem_iInter₂.mp hx j hj) (lt_min one_pos hquot) ?_ (by ring)
      have : min 1 (ε / (2 * (dist y x + 1))) ≤ 1 := min_le_left _ _
      linarith
    · have hapos : (0 : ℝ) < min 1 (ε / (2 * (dist y x + 1))) := lt_min one_pos hquot
      have hale : min 1 (ε / (2 * (dist y x + 1))) ≤ ε / (2 * (dist y x + 1)) :=
        min_le_right _ _
      have hval : min 1 (ε / (2 * (dist y x + 1))) • y +
          (1 - min 1 (ε / (2 * (dist y x + 1)))) • x - x =
          min 1 (ε / (2 * (dist y x + 1))) • (y - x) := by
        module
      rw [dist_comm, dist_eq_norm, hval, norm_smul, Real.norm_eq_abs, abs_of_nonneg hapos.le,
        ← dist_eq_norm]
      have hstep : min 1 (ε / (2 * (dist y x + 1))) * dist y x ≤
          (ε / (2 * (dist y x + 1))) * dist y x :=
        mul_le_mul_of_nonneg_right hale hDnn
      have hstep2 : (ε / (2 * (dist y x + 1))) * dist y x < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        nlinarith [hε, hDnn]
      linarith

/-! ## Finite unions of dilation sets

The type set of a finite union is the intersection of the type sets: the maximal operator of a
union is dominated by the sum of the individual maximal operators, and dominates each of them.
For finite unions of quasi-Assouad regular sets this gives Theorem 1.3 of the paper. -/

/-- The maximal operator over a union is dominated by the sum of the two maximal operators. -/
theorem fractalSphericalMaximalReal_union_le
    {d : ℕ} (hd : 0 < d) {E F : Set ℝ} (hE : E ⊆ Ioi (0 : ℝ)) (hF : F ⊆ Ioi (0 : ℝ))
    (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    fractalSphericalMaximalReal d (E ∪ F) f x ≤
      fractalSphericalMaximalReal d E f x + fractalSphericalMaximalReal d F f x := by
  have hEtop : fractalSphericalMaximal d E ((f : Euclidean d → ℂ)) x ≠ ⊤ :=
    fractalSphericalMaximal_ne_top hd E hE f x
  have hFtop : fractalSphericalMaximal d F ((f : Euclidean d → ℂ)) x ≠ ⊤ :=
    fractalSphericalMaximal_ne_top hd F hF f x
  have hUtop : fractalSphericalMaximal d (E ∪ F) ((f : Euclidean d → ℂ)) x ≠ ⊤ :=
    fractalSphericalMaximal_ne_top hd (E ∪ F) (union_subset hE hF) f x
  have hle : fractalSphericalMaximal d (E ∪ F) ((f : Euclidean d → ℂ)) x ≤
      fractalSphericalMaximal d E ((f : Euclidean d → ℂ)) x +
        fractalSphericalMaximal d F ((f : Euclidean d → ℂ)) x := by
    refine iSup_le fun t => ?_
    rcases t.2 with ht | ht
    · exact le_trans
        (normalizedSphericalAverage_le_fractalSphericalMaximal E ((f : Euclidean d → ℂ)) ht x)
        le_self_add
    · exact le_trans
        (normalizedSphericalAverage_le_fractalSphericalMaximal F ((f : Euclidean d → ℂ)) ht x)
        le_add_self
  unfold fractalSphericalMaximalReal
  rw [← ENNReal.toReal_add hEtop hFtop]
  exact (ENNReal.toReal_le_toReal hUtop (ENNReal.add_ne_top.mpr ⟨hEtop, hFtop⟩)).mpr hle

/-- Strong type is inherited by finite unions. -/
theorem hasFractalSphericalStrongType_union
    {d : ℕ} (hd : 0 < d) {E F : Set ℝ} {p q : ℝ} (hq : 1 ≤ q)
    (hEpos : E ⊆ Ioi (0 : ℝ)) (hFpos : F ⊆ Ioi (0 : ℝ))
    (hE : HasFractalSphericalStrongType d E p q)
    (hF : HasFractalSphericalStrongType d F p q) :
    HasFractalSphericalStrongType d (E ∪ F) p q := by
  obtain ⟨C1, hC1, hb1⟩ := hE
  obtain ⟨C2, hC2, hb2⟩ := hF
  have hqone : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hq
  refine ⟨C1 + C2, by linarith, fun f => ?_⟩
  have hmeasU : AEStronglyMeasurable (fractalSphericalMaximalReal d (E ∪ F) f) volume :=
    (measurable_fractalSphericalMaximalReal (E ∪ F) f).aestronglyMeasurable
  have hmeas1 : AEStronglyMeasurable (fractalSphericalMaximalReal d E f) volume :=
    (measurable_fractalSphericalMaximalReal E f).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fractalSphericalMaximalReal d F f) volume :=
    (measurable_fractalSphericalMaximalReal F f).aestronglyMeasurable
  have hbound : eLpNorm (fractalSphericalMaximalReal d (E ∪ F) f)
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (C1 + C2) *
        eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume := by
    have hstep1 : eLpNorm (fractalSphericalMaximalReal d (E ∪ F) f) (ENNReal.ofReal q) volume ≤
        eLpNorm (fractalSphericalMaximalReal d E f + fractalSphericalMaximalReal d F f)
          (ENNReal.ofReal q) volume := by
      apply eLpNorm_mono_enorm
      intro x
      have hpoint := fractalSphericalMaximalReal_union_le hd hEpos hFpos f x
      have h1 : 0 ≤ fractalSphericalMaximalReal d E f x := ENNReal.toReal_nonneg
      have h2 : 0 ≤ fractalSphericalMaximalReal d F f x := ENNReal.toReal_nonneg
      have h0 : 0 ≤ fractalSphericalMaximalReal d (E ∪ F) f x := ENNReal.toReal_nonneg
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg h0,
        abs_of_nonneg (by simpa [Pi.add_apply] using add_nonneg h1 h2 :
          (0:ℝ) ≤ (fractalSphericalMaximalReal d E f + fractalSphericalMaximalReal d F f) x)]
      exact ENNReal.ofReal_le_ofReal (by simpa [Pi.add_apply] using hpoint)
    have hstep2 := eLpNorm_add_le hmeas1 hmeas2 hqone
    have hstep3 : eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume +
          eLpNorm (fractalSphericalMaximalReal d F f) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (C1 + C2) *
          eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume := by
      have h1 := (hb1 f).2
      have h2 := (hb2 f).2
      calc eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume +
            eLpNorm (fractalSphericalMaximalReal d F f) (ENNReal.ofReal q) volume ≤
            ENNReal.ofReal C1 * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume +
              ENNReal.ofReal C2 *
                eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume := add_le_add h1 h2
        _ = ENNReal.ofReal (C1 + C2) *
            eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume := by
          rw [ENNReal.ofReal_add hC1.le hC2.le, add_mul]
    exact le_trans hstep1 (le_trans hstep2 hstep3)
  refine ⟨⟨hmeasU, ?_⟩, hbound⟩
  refine lt_of_le_of_lt hbound ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp (ENNReal.ofReal p) volume).2

/-- Strong type is inherited by finite unions indexed by a `Finset`. -/
theorem hasFractalSphericalStrongType_biUnion
    {d : ℕ} {ι : Type*} [DecidableEq ι] {Es : ι → Set ℝ} {p q : ℝ}
    (hd : 0 < d) (hq : 1 ≤ q) (s : Finset ι)
    (hpos : ∀ j ∈ s, Es j ⊆ Ioi (0 : ℝ))
    (h : ∀ j ∈ s, HasFractalSphericalStrongType d (Es j) p q) :
    HasFractalSphericalStrongType d (⋃ j ∈ s, Es j) p q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hasFractalSphericalStrongType_empty d p q
  | insert a s ha ih =>
      have hposa : Es a ⊆ Ioi (0 : ℝ) := hpos a (Finset.mem_insert_self a s)
      have hposs : ∀ j ∈ s, Es j ⊆ Ioi (0 : ℝ) := fun j hj =>
        hpos j (Finset.mem_insert_of_mem hj)
      have hsa : HasFractalSphericalStrongType d (Es a) p q :=
        h a (Finset.mem_insert_self a s)
      have hss : ∀ j ∈ s, HasFractalSphericalStrongType d (Es j) p q := fun j hj =>
        h j (Finset.mem_insert_of_mem hj)
      have hrest := ih hposs hss
      have hunion : (⋃ j ∈ insert a s, Es j) = Es a ∪ ⋃ j ∈ s, Es j := by
        simp
      rw [hunion]
      refine hasFractalSphericalStrongType_union hd hq hposa ?_ hsa hrest
      intro t ht
      obtain ⟨j, hj, hjt⟩ := Set.mem_iUnion₂.mp ht
      exact hposs j hj hjt

/-- The type set is antitone in the dilation set. -/
theorem fractalTypeSet_mono
    {d : ℕ} (hd : 0 < d) {E F : Set ℝ} (hEF : E ⊆ F) (hFpos : F ⊆ Ioi (0 : ℝ)) :
    fractalTypeSet d F ⊆ fractalTypeSet d E := by
  intro z hz
  obtain ⟨p, q, hp, hq, hzeq, hst⟩ := hz
  exact ⟨p, q, hp, hq, hzeq,
    Auto.Spherical.FractalDilations.AHRSUpperBounds.HasFractalSphericalStrongType.mono_radii
      hd hEF hFpos hst⟩

/-! ### Theorem 1.3: finite unions of quasi-Assouad regular sets -/

/-- **Theorem 1.3 of Roos--Seeger.**  For a finite union of quasi-Assouad regular sets the
closure of the type set is the intersection of the corresponding regions, hence a closed convex
polygon. -/
theorem closure_fractalTypeSet_biUnion_eq_iInter
    {d : ℕ} {ι : Type*} [DecidableEq ι] {Es : ι → Set ℝ} {betas gams : ι → ℝ}
    (hd : 2 ≤ d) (s : Finset ι) (hs : s.Nonempty)
    (hE : ∀ j ∈ s, Es j ⊆ Icc (1 : ℝ) 2) (hEne : ∀ j ∈ s, (Es j).Nonempty)
    (hbg : ∀ j ∈ s, 0 ≤ betas j ∧ betas j ≤ gams j ∧ gams j ≤ 1)
    (hreg : ∀ j ∈ s, IsQuasiAssouadRegular (Es j) (betas j) (gams j)) :
    closure (fractalTypeSet d (⋃ j ∈ s, Es j)) = ⋂ j ∈ s, Q d (betas j) (gams j) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hpos : ∀ j ∈ s, Es j ⊆ Ioi (0 : ℝ) := by
    intro j hj t ht
    have := hE j hj ht
    exact lt_of_lt_of_le zero_lt_one this.1
  have hUpos : (⋃ j ∈ s, Es j) ⊆ Ioi (0 : ℝ) := by
    intro t ht
    obtain ⟨j, hj, hjt⟩ := Set.mem_iUnion₂.mp ht
    exact hpos j hj hjt
  refine le_antisymm ?_ ?_
  · -- the union is at least as large as each piece, so its type set is contained in each `Q`
    refine closure_minimal ?_ ?_
    · intro z hz
      refine Set.mem_iInter₂.mpr fun j hj => ?_
      have hsub : Es j ⊆ ⋃ i ∈ s, Es i := fun t ht => Set.mem_iUnion₂.mpr ⟨j, hj, ht⟩
      have hz' : z ∈ fractalTypeSet d (Es j) :=
        fractalTypeSet_mono hdpos hsub hUpos hz
      exact fractalTypeSet_subset_Q_of_regular hd (hE j hj) (hEne j hj) (hbg j hj)
        (hreg j hj) hz'
    · exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_Q d _ _
  · -- conversely the intersection of the interiors consists of points of strong type
    have hint : ∀ j ∈ s, interior (Q d (betas j) (gams j)) ⊆ fractalTypeSet d (Es j) := by
      intro j hj
      obtain ⟨hb, hbg', hg⟩ := hbg j hj
      exact interior_Q_subset_fractalTypeSet hd (hE j hj) hb hbg' hg
        (hreg j hj).1 (hreg j hj).2.1
    have hsubset : (⋂ j ∈ s, interior (Q d (betas j) (gams j))) ⊆
        fractalTypeSet d (⋃ j ∈ s, Es j) := by
      intro z hz
      obtain ⟨j0, hj0⟩ := hs
      have hzj0 := Set.mem_iInter₂.mp hz j0 hj0
      obtain ⟨p, q, hp, hq, hzeq, -⟩ := hint j0 hj0 hzj0
      refine ⟨p, q, hp, hq, hzeq, ?_⟩
      refine hasFractalSphericalStrongType_biUnion hdpos hq s hpos ?_
      intro j hj
      have hzj := Set.mem_iInter₂.mp hz j hj
      obtain ⟨p', q', hp', hq', hzeq', hst'⟩ := hint j hj hzj
      have heq := hzeq.symm.trans hzeq'
      have hpp : p = p' := by
        have h := (Prod.ext_iff.mp heq).1
        simp only [reciprocalExponentPoint] at h
        exact inv_injective h
      have hqq : q = q' := by
        have h := (Prod.ext_iff.mp heq).2
        simp only [reciprocalExponentPoint] at h
        exact inv_injective h
      rw [← hpp, ← hqq] at hst'
      exact hst'
    have hclos : closure (⋂ j ∈ s, interior (Q d (betas j) (gams j))) =
        ⋂ j ∈ s, Q d (betas j) (gams j) :=
      closure_biInter_interior_Q_eq hd s hs hbg
    calc (⋂ j ∈ s, Q d (betas j) (gams j)) =
          closure (⋂ j ∈ s, interior (Q d (betas j) (gams j))) := hclos.symm
      _ ⊆ closure (fractalTypeSet d (⋃ j ∈ s, Es j)) := closure_mono hsubset

/-- **The closure of the type set realizes every region `Q(β,γ)`.** -/
theorem exists_closure_fractalTypeSet_eq_Q {d : ℕ} (hd : 2 ≤ d) {beta gam : ℝ}
    (hbeta : 0 ≤ beta) (hbg : beta ≤ gam) (hgam1 : gam ≤ 1) (hzero : beta = 0 → gam = 0) :
    ∃ E : Set ℝ, E ⊆ Icc (1 : ℝ) 2 ∧ E.Nonempty ∧
      closure (fractalTypeSet d E) = Q d beta gam := by
  obtain ⟨E, hE, hEne, hreg⟩ := exists_isQuasiAssouadRegular hbeta hbg hgam1 hzero
  exact ⟨E, hE, hEne,
    closure_fractalTypeSet_eq_Q_of_regular hd hE hEne ⟨hbeta, hbg, hgam1⟩ hreg⟩

/-! ### The region at `β = 0` does not see `γ` -/

theorem Q_zero_beta_eq {d : ℕ} (hd : 2 ≤ d) {gam : ℝ} (hgam : 0 ≤ gam) :
    Q d 0 gam = Q d 0 0 := by
  ext x
  rw [mem_Q_iff_not_sharpnessViolation hd (le_refl (0:ℝ)) (by norm_num) hgam,
    mem_Q_iff_not_sharpnessViolation hd (le_refl (0:ℝ)) (by norm_num) (le_refl (0:ℝ))]
  have hcl : clusterEdgeFunctional d ((0:ℝ) / gam) 0 x
      = clusterEdgeFunctional d ((0:ℝ) / 0) 0 x := by
    rw [zero_div, zero_div]
  rw [SharpnessViolation, SharpnessViolation, hcl]

/-! ### Realizing a single region without the degenerate hypothesis -/

theorem exists_closure_fractalTypeSet_eq_Q' {d : ℕ} (hd : 2 ≤ d) {beta gam : ℝ}
    (hbeta : 0 ≤ beta) (hbg : beta ≤ gam) (hgam1 : gam ≤ 1) :
    ∃ E : Set ℝ, E ⊆ Icc (1 : ℝ) 2 ∧ E.Nonempty ∧
      closure (fractalTypeSet d E) = Q d beta gam := by
  rcases eq_or_lt_of_le hbeta with hb0 | hbpos
  · -- `β = 0`: the single-radius example realizes `Q(0,0) = Q(0,γ)`
    obtain ⟨E, hE, hEne, hclos⟩ :=
      exists_closure_fractalTypeSet_eq_Q hd (le_refl (0:ℝ)) (le_refl (0:ℝ))
        (by norm_num : (0:ℝ) ≤ 1) (fun _ => rfl)
    refine ⟨E, hE, hEne, ?_⟩
    rw [hclos, ← hb0]
    exact (Q_zero_beta_eq hd (hb0 ▸ hbg)).symm
  · exact exists_closure_fractalTypeSet_eq_Q hd hbeta hbg hgam1
      (fun h => absurd h (by linarith))

/-! ### Theorem 1.2 for polygons: every finite intersection is a type set -/

/-- **Every finite intersection of regions `Q(βⱼ,γⱼ)` is the closure of a type set.**  This is the
polygonal case of Theorem 1.2(i), obtained from Theorem 1.3 and the examples of §6. -/
theorem exists_closure_fractalTypeSet_eq_biInter {d : ℕ} {ι : Type*} [DecidableEq ι]
    (hd : 2 ≤ d) (s : Finset ι) (hs : s.Nonempty) (betas gams : ι → ℝ)
    (hbg : ∀ j ∈ s, 0 ≤ betas j ∧ betas j ≤ gams j ∧ gams j ≤ 1) :
    ∃ E : Set ℝ, E ⊆ Icc (1 : ℝ) 2 ∧ E.Nonempty ∧
      closure (fractalTypeSet d E) = ⋂ j ∈ s, Q d (betas j) (gams j) := by
  classical
  -- choose a regular set for each index, replacing a degenerate pair by `(0,0)`
  have hchoice : ∀ j ∈ s, ∃ Ej : Set ℝ, Ej ⊆ Icc (1 : ℝ) 2 ∧ Ej.Nonempty ∧
      ∃ b g : ℝ, 0 ≤ b ∧ b ≤ g ∧ g ≤ 1 ∧ IsQuasiAssouadRegular Ej b g ∧
        Q d b g = Q d (betas j) (gams j) := by
    intro j hj
    obtain ⟨hb, hbgj, hg⟩ := hbg j hj
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · obtain ⟨Ej, hEj, hEjne, hreg⟩ :=
        exists_isQuasiAssouadRegular (le_refl (0:ℝ)) (le_refl (0:ℝ))
          (by norm_num : (0:ℝ) ≤ 1) (fun _ => rfl)
      refine ⟨Ej, hEj, hEjne, 0, 0, le_refl _, le_refl _, by norm_num, hreg, ?_⟩
      rw [← hb0]
      exact (Q_zero_beta_eq hd (hb0 ▸ hbgj)).symm
    · obtain ⟨Ej, hEj, hEjne, hreg⟩ :=
        exists_isQuasiAssouadRegular hb hbgj hg (fun h => absurd h (by linarith))
      exact ⟨Ej, hEj, hEjne, betas j, gams j, hb, hbgj, hg, hreg, rfl⟩
  choose! Es hEs hEsne bs gs hbs hbgs hgs hregs hQs using hchoice
  refine ⟨⋃ j ∈ s, Es j, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    exact hEs j hj hxj
  · obtain ⟨j0, hj0⟩ := hs
    obtain ⟨x, hx⟩ := hEsne j0 hj0
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨j0, hj0, hx⟩⟩
  · have hbi := closure_fractalTypeSet_biUnion_eq_iInter (Es := Es) (betas := bs) (gams := gs)
      hd s hs (fun j hj => hEs j hj) (fun j hj => hEsne j hj)
      (fun j hj => ⟨hbs j hj, hbgs j hj, hgs j hj⟩) (fun j hj => hregs j hj)
    rw [hbi]
    refine Set.iInter₂_congr ?_
    intro j hj
    exact hQs j hj

open Auto.Spherical.FractalDilations.Auxiliary
/-! ### The trivial necessary condition `p ≤ q` -/

/-- A strong type point of the fractal spherical maximal operator has `p ≤ q`.  This is the
first sharpness assertion of Theorem 2 of arXiv:1909.05389, read off from the region `Q`. -/
theorem le_of_hasFractalSphericalStrongType {d : ℕ} {E : Set ℝ} {p q : ℝ} (hd : 2 ≤ d)
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) (hp : 0 < p) (hq : 1 ≤ q)
    (hst : HasFractalSphericalStrongType d E p q) : p ≤ q := by
  have hmem : reciprocalExponentPoint p q ∈ fractalTypeSet d E :=
    ⟨p, q, hp, hq, rfl, hst⟩
  have hsub := fractalTypeSet_subset_Q_self hd hE hEne
    (upperMinkowskiDimension_nonneg_of_subset_Icc hE)
    (upperMinkowskiDimension_le_one_of_subset_Icc hE) rfl
  have hQ := hsub hmem
  have hQ' := not_sharpnessViolation_of_mem_Q hd
    (upperMinkowskiDimension_nonneg_of_subset_Icc hE)
    (upperMinkowskiDimension_le_one_of_subset_Icc hE)
    (le_refl (upperMinkowskiDimension E)) hQ
  rw [SharpnessViolation] at hQ'
  have hfirst : ¬ ((reciprocalExponentPoint p q).1 < (reciprocalExponentPoint p q).2) := by
    intro h
    exact hQ' (Or.inl h)
  have hle : q⁻¹ ≤ p⁻¹ := not_lt.mp hfirst
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact (inv_le_inv₀ hq0 hp).mp hle

/-! ### Lyapunov interpolation of output norms -/

/-- **Lyapunov's inequality.**  The `L^q` norm at an intermediate exponent is dominated by the
geometric mean of the two endpoint norms. -/
theorem eLpNorm_le_rpow_mul_rpow_of_inv_eq {d : ℕ} {g : Euclidean d → ℝ}
    (hg : AEMeasurable g (volume : Measure (Euclidean d)))
    {q0 q1 q lam : ℝ} (hq0 : 0 < q0) (hq1 : 0 < q1) (hq : 0 < q)
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hrel : q⁻¹ = (1 - lam) * q0⁻¹ + lam * q1⁻¹) :
    eLpNorm g (ENNReal.ofReal q) volume
      ≤ (eLpNorm g (ENNReal.ofReal q0) volume) ^ (1 - lam)
        * (eLpNorm g (ENNReal.ofReal q1) volume) ^ lam := by
  have hlam1' : 0 < 1 - lam := by linarith
  have hq0' : q0 ≠ 0 := ne_of_gt hq0
  have hq1' : q1 ≠ 0 := ne_of_gt hq1
  have hqne : q ≠ 0 := ne_of_gt hq
  have hlamne : lam ≠ 0 := ne_of_gt hlam0
  have hlamne' : 1 - lam ≠ 0 := ne_of_gt hlam1'
  set u : ℝ := q0 / (q * (1 - lam)) with hudef
  set v : ℝ := q1 / (q * lam) with hvdef
  have hupos : 0 < u := by rw [hudef]; exact div_pos hq0 (by positivity)
  have hvpos : 0 < v := by rw [hvdef]; exact div_pos hq1 (by positivity)
  have hu1 : u⁻¹ = q * (1 - lam) * q0⁻¹ := by rw [hudef]; field_simp
  have hv1 : v⁻¹ = q * lam * q1⁻¹ := by rw [hvdef]; field_simp
  have hconj : Real.HolderConjugate u v := by
    refine ⟨?_, hupos, hvpos⟩
    have hsum : q * (1 - lam) * q0⁻¹ + q * lam * q1⁻¹
        = q * ((1 - lam) * q0⁻¹ + lam * q1⁻¹) := by ring
    rw [hu1, hv1, inv_one, hsum, ← hrel, mul_inv_cancel₀ hqne]
  -- the two factors of the pointwise splitting
  set F : Euclidean d → ℝ≥0∞ := fun x => ‖g x‖ₑ ^ (q * (1 - lam)) with hFdef
  set G : Euclidean d → ℝ≥0∞ := fun x => ‖g x‖ₑ ^ (q * lam) with hGdef
  have hFmeas : AEMeasurable F (volume : Measure (Euclidean d)) := by
    rw [hFdef]
    exact (ENNReal.continuous_rpow_const).measurable.comp_aemeasurable hg.enorm
  have hGmeas : AEMeasurable G (volume : Measure (Euclidean d)) := by
    rw [hGdef]
    exact (ENNReal.continuous_rpow_const).measurable.comp_aemeasurable hg.enorm
  have hprod : ∀ x, (F * G) x = ‖g x‖ₑ ^ q := by
    intro x
    rw [hFdef, hGdef]
    simp only [Pi.mul_apply]
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    congr 1
    ring
  have hFu : ∀ x, F x ^ u = ‖g x‖ₑ ^ q0 := by
    intro x
    rw [hFdef]
    simp only
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [hudef]
    field_simp
  have hGv : ∀ x, G x ^ v = ‖g x‖ₑ ^ q1 := by
    intro x
    rw [hGdef]
    simp only
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [hvdef]
    field_simp
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume : Measure (Euclidean d)) hconj hFmeas hGmeas
  rw [lintegral_congr hprod, lintegral_congr hFu, lintegral_congr hGv] at hholder
  -- take q-th roots
  set A : ℝ≥0∞ := ∫⁻ x : Euclidean d, ‖g x‖ₑ ^ q0 with hAdef
  set B : ℝ≥0∞ := ∫⁻ x : Euclidean d, ‖g x‖ₑ ^ q1 with hBdef
  have hmain : (∫⁻ x : Euclidean d, ‖g x‖ₑ ^ q) ^ q⁻¹
      ≤ (A ^ (1 / u) * B ^ (1 / v)) ^ q⁻¹ :=
    ENNReal.rpow_le_rpow hholder (by positivity)
  rw [eLpNorm_ofReal_eq hq, eLpNorm_ofReal_eq hq0, eLpNorm_ofReal_eq hq1, ← hAdef, ← hBdef,
    one_div q]
  refine hmain.trans (le_of_eq ?_)
  have he0 : (1 / u) * q⁻¹ = (1 / q0) * (1 - lam) := by
    rw [hudef]
    field_simp
  have he1 : (1 / v) * q⁻¹ = (1 / q1) * lam := by
    rw [hvdef]
    field_simp
  have hL : (A ^ (1 / u) * B ^ (1 / v)) ^ q⁻¹ = A ^ ((1 / u) * q⁻¹) * B ^ ((1 / v) * q⁻¹) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ q⁻¹), ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
  have hR : (A ^ (1 / q0)) ^ (1 - lam) * (B ^ (1 / q1)) ^ lam
      = A ^ ((1 / q0) * (1 - lam)) * B ^ ((1 / q1) * lam) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  rw [hL, hR, he0, he1]

/-! ### Interpolation of two strong types at a common input exponent -/

/-- **Same-input interpolation.**  Two strong estimates with the same input exponent give the
strong estimate at every intermediate output exponent. -/
theorem hasFractalSphericalStrongType_interp_same_input {d : ℕ} {E : Set ℝ}
    {p q0 q1 q lam : ℝ} (hq0 : 0 < q0) (hq1 : 0 < q1) (hq : 0 < q)
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hrel : q⁻¹ = (1 - lam) * q0⁻¹ + lam * q1⁻¹)
    (h0 : HasFractalSphericalStrongType d E p q0)
    (h1 : HasFractalSphericalStrongType d E p q1) :
    HasFractalSphericalStrongType d E p q := by
  obtain ⟨C0, hC0, hb0⟩ := h0
  obtain ⟨C1, hC1, hb1⟩ := h1
  have hlam1' : 0 < 1 - lam := by linarith
  refine ⟨C0 ^ (1 - lam) * C1 ^ lam, by positivity, fun f => ?_⟩
  obtain ⟨hmem0, hbound0⟩ := hb0 f
  obtain ⟨hmem1, hbound1⟩ := hb1 f
  have hmeas : AEMeasurable (fractalSphericalMaximalReal d E f)
      (volume : Measure (Euclidean d)) := hmem0.1.aemeasurable
  have hlyap := eLpNorm_le_rpow_mul_rpow_of_inv_eq (g := fractalSphericalMaximalReal d E f)
    hmeas hq0 hq1 hq hlam0 hlam1 hrel
  -- the interpolated bound
  have hbound : eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q) volume
      ≤ ENNReal.ofReal (C0 ^ (1 - lam) * C1 ^ lam)
        * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume := by
    refine hlyap.trans ?_
    have h0' : (eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q0) volume)
          ^ (1 - lam)
        ≤ (ENNReal.ofReal C0 * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume)
          ^ (1 - lam) := ENNReal.rpow_le_rpow hbound0 hlam1'.le
    have h1' : (eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q1) volume) ^ lam
        ≤ (ENNReal.ofReal C1 * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume)
          ^ lam := ENNReal.rpow_le_rpow hbound1 hlam0.le
    refine le_trans (mul_le_mul' h0' h1') (le_of_eq ?_)
    set Y : ℝ≥0∞ := eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume with hYdef
    have hY : Y ^ (1 - lam) * Y ^ lam = Y := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hlam1'.le hlam0.le]
      simp
    have hC : ENNReal.ofReal C0 ^ (1 - lam) * ENNReal.ofReal C1 ^ lam
        = ENNReal.ofReal (C0 ^ (1 - lam) * C1 ^ lam) := by
      rw [ENNReal.ofReal_rpow_of_pos hC0, ENNReal.ofReal_rpow_of_pos hC1,
        ← ENNReal.ofReal_mul (by positivity)]
    calc (ENNReal.ofReal C0 * Y) ^ (1 - lam) * (ENNReal.ofReal C1 * Y) ^ lam
        = (ENNReal.ofReal C0 ^ (1 - lam) * Y ^ (1 - lam))
          * (ENNReal.ofReal C1 ^ lam * Y ^ lam) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hlam1'.le, ENNReal.mul_rpow_of_nonneg _ _ hlam0.le]
      _ = (ENNReal.ofReal C0 ^ (1 - lam) * ENNReal.ofReal C1 ^ lam)
          * (Y ^ (1 - lam) * Y ^ lam) := by ring
      _ = ENNReal.ofReal (C0 ^ (1 - lam) * C1 ^ lam) * Y := by rw [hC, hY]
  refine ⟨⟨hmem0.1, ?_⟩, hbound⟩
  -- finiteness of the interpolated norm
  refine lt_of_le_of_lt hlyap ?_
  have h0top : (eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q0) volume)
      ^ (1 - lam) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hlam1'.le (ne_of_lt hmem0.2)
  have h1top : (eLpNorm (fractalSphericalMaximalReal d E f) (ENNReal.ofReal q1) volume)
      ^ lam ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hlam0.le (ne_of_lt hmem1.2)
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr h0top) (lt_top_iff_ne_top.mpr h1top)

/-! ### Inversion of the half line -/

/-- The substitution `t = 1/s` on the half line. -/
theorem lintegral_Ioi_comp_inv (u : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioi (0 : ℝ), u t)
      = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((s ^ 2)⁻¹) * u s⁻¹ := by
  have himg : (fun x : ℝ => x⁻¹) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact inv_pos.mpr hx
    · intro hy
      exact ⟨y⁻¹, inv_pos.mpr hy, inv_inv y⟩
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) (Ioi (0 : ℝ)) x := by
    intro x hx
    exact (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt
  have hanti : AntitoneOn (fun y : ℝ => y⁻¹) (Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    exact (inv_le_inv₀ hb ha).mpr hab
  have hchange := lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
    (f := fun y : ℝ => y⁻¹) (f' := fun x : ℝ => -(x ^ 2)⁻¹) measurableSet_Ioi hderiv hanti u
  rw [himg] at hchange
  rw [hchange]
  refine lintegral_congr fun s => ?_
  congr 1
  rw [neg_neg]

/-! ### The two weighted tails at a negative amplitude exponent -/

/-- The weighted high-amplitude tail for a negative amplitude exponent, obtained from the
positive case by the substitution `t = 1/s`. -/
theorem lintegral_highTail_rpow_le_of_neg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] (u : α → ℝ) (hu : Measurable u) (hunn : ∀ x, 0 ≤ u x)
    {p0 p m c r0 J : ℝ} (hp0 : 0 < p0) (hp0p : p0 < p) (hm : m < 0) (hc : 0 < c)
    (hr0 : 1 ≤ r0) (hJ0 : 0 < J)
    (hJ : (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) ≤ ENNReal.ofReal J) :
    (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x in {x | c * t ^ m ≤ u x}, (ENNReal.ofReal (u x)) ^ p0 ∂μ) ^ r0
          * (ENNReal.ofReal t) ^ (m * (p - p0) * r0 - 1))
      ≤ ENNReal.ofReal (c ^ ((p0 - p) * r0) * J ^ r0 / (-m * (p - p0))) := by
  set m' : ℝ := -m with hm'def
  have hm' : 0 < m' := by rw [hm'def]; linarith
  rw [lintegral_Ioi_comp_inv]
  have hpt : ∀ s : ℝ, s ∈ Ioi (0 : ℝ) →
      ENNReal.ofReal ((s ^ 2)⁻¹) *
          ((∫⁻ x in {x | c * (s⁻¹) ^ m ≤ u x}, (ENNReal.ofReal (u x)) ^ p0 ∂μ) ^ r0
            * (ENNReal.ofReal s⁻¹) ^ (m * (p - p0) * r0 - 1))
        = (∫⁻ x in {x | c * s ^ m' ≤ u x}, (ENNReal.ofReal (u x)) ^ p0 ∂μ) ^ r0
            * (ENNReal.ofReal s) ^ (m' * (p - p0) * r0 - 1) := by
    intro s hs
    have hspos : 0 < s := hs
    have hsne : ENNReal.ofReal s ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hspos
    have hstop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
    have hinvm : (s⁻¹) ^ m = s ^ m' := by
      rw [Real.inv_rpow hspos.le, hm'def, Real.rpow_neg hspos.le]
    have hinvE : (ENNReal.ofReal s⁻¹) ^ (m * (p - p0) * r0 - 1)
        = (ENNReal.ofReal s) ^ (-(m * (p - p0) * r0 - 1)) := by
      rw [ENNReal.ofReal_inv_of_pos hspos, ← ENNReal.rpow_neg_one,
        ← ENNReal.rpow_mul]
      congr 1
      ring
    have hpow2 : (s : ℝ) ^ (2 : ℝ) = s ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have hsq : ENNReal.ofReal ((s ^ 2)⁻¹) = (ENNReal.ofReal s) ^ (-2 : ℝ) := by
      rw [ENNReal.rpow_neg, ENNReal.ofReal_rpow_of_pos hspos, hpow2,
        ENNReal.ofReal_inv_of_pos (pow_pos hspos 2)]
    rw [hinvm, hinvE, hsq]
    rw [show (m' * (p - p0) * r0 - 1 : ℝ)
        = (-2) + (-(m * (p - p0) * r0 - 1)) by rw [hm'def]; ring]
    rw [ENNReal.rpow_add _ _ hsne hstop]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  exact lintegral_highTail_rpow_le u hu hunn hp0 hp0p hm' hc hr0 hJ0 hJ

/-- The weighted low-amplitude tail for a negative amplitude exponent. -/
theorem lintegral_lowTail_rpow_le_of_neg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] (u : α → ℝ) (hu : Measurable u) (hunn : ∀ x, 0 ≤ u x)
    {p1 p m c r1 J : ℝ} (g : ℝ → α → ℝ) (hgnn : ∀ t x, 0 ≤ g t x)
    (hg1 : ∀ t x, 0 < t → g t x ≤ u x)
    (hg2 : ∀ t x, 0 < t → g t x ≤ c * t ^ m)
    (hp : 0 < p) (hpp1 : p < p1) (hm : m < 0) (hc : 0 < c)
    (hr1 : 1 ≤ r1) (hJ0 : 0 < J)
    (hJ : (∫⁻ x, (ENNReal.ofReal (u x)) ^ p ∂μ) ≤ ENNReal.ofReal J) :
    (∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, (ENNReal.ofReal (g t x)) ^ p1 ∂μ) ^ r1
        * (ENNReal.ofReal t) ^ (m * (p - p1) * r1 - 1))
      ≤ ENNReal.ofReal (c ^ ((p1 - p) * r1) * J ^ r1
          * (1 / (-m * (p1 - p)) + 1 / (-m * p))) := by
  set m' : ℝ := -m with hm'def
  have hm' : 0 < m' := by rw [hm'def]; linarith
  set g' : ℝ → α → ℝ := fun s x => g s⁻¹ x with hg'def
  have hg'nn : ∀ s x, 0 ≤ g' s x := fun s x => hgnn _ _
  have hg'1 : ∀ s x, 0 < s → g' s x ≤ u x := by
    intro s x hs
    exact hg1 s⁻¹ x (inv_pos.mpr hs)
  have hg'2 : ∀ s x, 0 < s → g' s x ≤ c * s ^ m' := by
    intro s x hs
    have h := hg2 s⁻¹ x (inv_pos.mpr hs)
    have hinvm : (s⁻¹) ^ m = s ^ m' := by
      rw [Real.inv_rpow hs.le, hm'def, Real.rpow_neg hs.le]
    rw [hinvm] at h
    exact h
  rw [lintegral_Ioi_comp_inv]
  have hpt : ∀ s : ℝ, s ∈ Ioi (0 : ℝ) →
      ENNReal.ofReal ((s ^ 2)⁻¹) *
          ((∫⁻ x, (ENNReal.ofReal (g s⁻¹ x)) ^ p1 ∂μ) ^ r1
            * (ENNReal.ofReal s⁻¹) ^ (m * (p - p1) * r1 - 1))
        = (∫⁻ x, (ENNReal.ofReal (g' s x)) ^ p1 ∂μ) ^ r1
            * (ENNReal.ofReal s) ^ (m' * (p - p1) * r1 - 1) := by
    intro s hs
    have hspos : 0 < s := hs
    have hsne : ENNReal.ofReal s ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hspos
    have hstop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
    have hinvE : (ENNReal.ofReal s⁻¹) ^ (m * (p - p1) * r1 - 1)
        = (ENNReal.ofReal s) ^ (-(m * (p - p1) * r1 - 1)) := by
      rw [ENNReal.ofReal_inv_of_pos hspos, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul]
      congr 1
      ring
    have hpow2 : (s : ℝ) ^ (2 : ℝ) = s ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have hsq : ENNReal.ofReal ((s ^ 2)⁻¹) = (ENNReal.ofReal s) ^ (-2 : ℝ) := by
      rw [ENNReal.rpow_neg, ENNReal.ofReal_rpow_of_pos hspos, hpow2,
        ENNReal.ofReal_inv_of_pos (pow_pos hspos 2)]
    rw [hinvE, hsq, hg'def]
    simp only
    rw [show (m' * (p - p1) * r1 - 1 : ℝ)
        = (-2) + (-(m * (p - p1) * r1 - 1)) by rw [hm'def]; ring]
    rw [ENNReal.rpow_add _ _ hsne hstop]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  exact lintegral_lowTail_rpow_le u hu hunn g' hg'nn hg'1 hg'2 hp hpp1 hm' hc hr1 hJ0 hJ

/-! ### The two operator tails at a negative amplitude exponent -/

theorem twoPair_high_tail_le_of_neg {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ)
    (low high : ℝ → SchwartzMap (Euclidean d) ℂ)
    (hlow : ∀ t x, low t x = ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x)
    (hhigh : ∀ t, high t = f - low t)
    {p0 p q q0 m J : ℝ} (hp0 : 0 < p0) (hp0p : p0 < p) (hm : m < 0)
    (hr0 : 1 ≤ q0 / p0) (hJ0 : 0 < J)
    (hJ : (∫⁻ x : (Euclidean d), (ENNReal.ofReal ‖f x‖) ^ p) ≤ ENNReal.ofReal J)
    (hweight : q - q0 = m * (p - p0) * (q0 / p0)) :
    (∫⁻ t in Ioi (0 : ℝ),
        (eLpNorm ((high (t ^ m) : (Euclidean d) → ℂ)) (ENNReal.ofReal p0) volume) ^ q0
          * (ENNReal.ofReal t) ^ (q - q0 - 1))
      ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ ((p0 - p) * (q0 / p0)) * J ^ (q0 / p0)
          / (-m * (p - p0))) := by
  set r0 : ℝ := q0 / p0 with hr0def
  set u : (Euclidean d) → ℝ := fun x => ‖f x‖ with hudef
  have hu : Measurable u := f.continuous.norm.measurable
  have hunn : ∀ x, 0 ≤ u x := fun x => norm_nonneg _
  have hmain := lintegral_highTail_rpow_le_of_neg u hu hunn
    (p0 := p0) (p := p) (m := m) (c := 1 / 4) (r0 := r0) (J := J)
    hp0 hp0p hm (by norm_num) hr0 hJ0 hJ
  refine le_trans (lintegral_mono_ae ?_) hmain
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htm : 0 < t ^ m := Real.rpow_pos_of_pos ht m
  have hset : MeasurableSet {x : (Euclidean d) | (1 / 4 : ℝ) * t ^ m ≤ u x} :=
    measurableSet_le measurable_const hu
  have hinner : (∫⁻ x : (Euclidean d), (ENNReal.ofReal ‖high (t ^ m) x‖) ^ p0)
      ≤ ∫⁻ x in {x | (1 / 4 : ℝ) * t ^ m ≤ u x}, (ENNReal.ofReal (u x)) ^ p0 := by
    rw [← lintegral_indicator hset]
    refine lintegral_mono fun x => ?_
    by_cases hx : (1 / 4 : ℝ) * t ^ m ≤ u x
    · have hmem : x ∈ {x : (Euclidean d) | (1 / 4 : ℝ) * t ^ m ≤ u x} := hx
      rw [Set.indicator_of_mem hmem]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
        (smooth_high_norm_le f (low (t ^ m)) (high (t ^ m)) (hlow (t ^ m))
          (hhigh (t ^ m)) x)) hp0.le
    · have hnotmem : x ∉ {x : (Euclidean d) | (1 / 4 : ℝ) * t ^ m ≤ u x} := hx
      have hle : ‖f x‖ ≤ t ^ m / 4 := by
        have hlt := not_le.mp hx
        rw [hudef] at hlt
        simp only at hlt
        linarith
      rw [smooth_high_eq_zero_of_norm_le_quarter f (low (t ^ m)) (high (t ^ m)) htm
        (hlow (t ^ m)) (hhigh (t ^ m)) x hle]
      simp [ENNReal.zero_rpow_of_pos hp0]
  calc (eLpNorm ((high (t ^ m) : (Euclidean d) → ℂ)) (ENNReal.ofReal p0) volume) ^ q0
        * (ENNReal.ofReal t) ^ (q - q0 - 1)
      = (∫⁻ x : (Euclidean d), (ENNReal.ofReal ‖high (t ^ m) x‖) ^ p0) ^ r0
          * (ENNReal.ofReal t) ^ (q - q0 - 1) := by
        rw [eLpNorm_rpow_eq hp0, hr0def]
    _ ≤ (∫⁻ x in {x | (1 / 4 : ℝ) * t ^ m ≤ u x}, (ENNReal.ofReal (u x)) ^ p0) ^ r0
          * (ENNReal.ofReal t) ^ (m * (p - p0) * r0 - 1) := by
        rw [show q - q0 - 1 = m * (p - p0) * r0 - 1 by rw [← hweight]]
        exact mul_le_mul' (ENNReal.rpow_le_rpow hinner (by linarith)) (le_refl _)

theorem twoPair_low_tail_le_of_neg {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ)
    (low : ℝ → SchwartzMap (Euclidean d) ℂ)
    (hlow : ∀ t x, low t x = ((smooth_half_height_bump ((t⁻¹ : ℝ) • f x) : ℝ) : ℂ) • f x)
    {p1 p q q1 m J : ℝ} (hp : 0 < p) (hpp1 : p < p1) (hm : m < 0)
    (hr1 : 1 ≤ q1 / p1) (hJ0 : 0 < J)
    (hJ : (∫⁻ x : (Euclidean d), (ENNReal.ofReal ‖f x‖) ^ p) ≤ ENNReal.ofReal J)
    (hweight : q - q1 = m * (p - p1) * (q1 / p1)) :
    (∫⁻ t in Ioi (0 : ℝ),
        (eLpNorm ((low (t ^ m) : (Euclidean d) → ℂ)) (ENNReal.ofReal p1) volume) ^ q1
          * (ENNReal.ofReal t) ^ (q - q1 - 1))
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p1 - p) * (q1 / p1)) * J ^ (q1 / p1)
          * (1 / (-m * (p1 - p)) + 1 / (-m * p))) := by
  set r1 : ℝ := q1 / p1 with hr1def
  set u : (Euclidean d) → ℝ := fun x => ‖f x‖ with hudef
  have hu : Measurable u := f.continuous.norm.measurable
  have hunn : ∀ x, 0 ≤ u x := fun x => norm_nonneg _
  have hp1 : 0 < p1 := by linarith
  have hmain := lintegral_lowTail_rpow_le_of_neg u hu hunn
    (p1 := p1) (p := p) (m := m) (c := 1 / 2) (r1 := r1) (J := J)
    (fun t x => ‖low (t ^ m) x‖) (fun t x => norm_nonneg _)
    (fun t x ht => smooth_low_norm_le f (low (t ^ m)) (hlow (t ^ m)) x)
    (fun t x ht => by
      have htm : 0 < t ^ m := Real.rpow_pos_of_pos ht m
      have h := smooth_low_norm_le_half_height f (low (t ^ m)) htm (hlow (t ^ m)) x
      linarith)
    hp hpp1 hm (by norm_num) hr1 hJ0 hJ
  refine le_trans (lintegral_mono_ae ?_) hmain
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [eLpNorm_rpow_eq hp1, ← hr1def,
    show q - q1 - 1 = m * (p - p1) * r1 - 1 by rw [← hweight]]

/-! ### Two-pair interpolation along a segment of negative slope -/

set_option maxHeartbeats 1000000 in
theorem exists_twoPair_interpolation_const_of_neg {d : ℕ}
    {p0 q0 p1 q1 p q m : ℝ}
    (hp0 : 0 < p0) (hp0p : p0 < p) (hpp1 : p < p1)
    (hq1 : 0 < q1) (hq1q : q1 < q) (hqq0 : q < q0)
    (hr0 : 1 ≤ q0 / p0) (hr1 : 1 ≤ q1 / p1) (hm : m < 0)
    (hm0 : q - q0 = m * (p - p0) * (q0 / p0))
    (hm1 : q - q1 = m * (p - p1) * (q1 / p1))
    (hcol : (q0 / p0) * ((q1 - q) / (q1 - q0)) + (q1 / p1) * ((q - q0) / (q1 - q0))
      = q / p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : SchwartzMap (Euclidean d) ℂ → (Euclidean d) → ℝ,
      (∀ g x, 0 ≤ T g x) →
      (∀ g h : SchwartzMap (Euclidean d) ℂ, ∀ x, T (g + h) x ≤ T g x + T h x) →
      (∀ g, AEStronglyMeasurable (T g) (volume : Measure (Euclidean d))) →
      (∀ x, T 0 x = 0) →
      ∀ B0 B1 : ℝ, 0 < B0 → 0 < B1 →
      (∀ g : SchwartzMap (Euclidean d) ℂ, eLpNorm (T g) (ENNReal.ofReal q0) volume
        ≤ ENNReal.ofReal B0 * eLpNorm ((g : (Euclidean d) → ℂ)) (ENNReal.ofReal p0) volume) →
      (∀ g : SchwartzMap (Euclidean d) ℂ, eLpNorm (T g) (ENNReal.ofReal q1) volume
        ≤ ENNReal.ofReal B1 * eLpNorm ((g : (Euclidean d) → ℂ)) (ENNReal.ofReal p1) volume) →
      ∀ f : SchwartzMap (Euclidean d) ℂ, eLpNorm (T f) (ENNReal.ofReal q) volume
        ≤ ENNReal.ofReal (C * B0 ^ (q0 * ((q1 - q) / (q1 - q0)) / q)
              * B1 ^ (q1 * ((q - q0) / (q1 - q0)) / q))
          * eLpNorm ((f : (Euclidean d) → ℂ)) (ENNReal.ofReal p) volume := by
  have hp : 0 < p := lt_trans hp0 hp0p
  have hp1 : 0 < p1 := lt_trans hp hpp1
  have hq : 0 < q := lt_trans hq1 hq1q
  have hq0 : 0 < q0 := lt_trans hq hqq0
  have hqden : q1 - q0 < 0 := by linarith
  have hqdne : q1 - q0 ≠ 0 := by linarith
  have hqdne' : q0 - q1 ≠ 0 := by linarith
  have hmneg : 0 < -m := by linarith
  set r0 : ℝ := q0 / p0 with hr0def
  set r1 : ℝ := q1 / p1 with hr1def
  set w0 : ℝ := (q1 - q) / (q1 - q0) with hw0def
  set w1 : ℝ := (q - q0) / (q1 - q0) with hw1def
  have hw0pos : 0 < w0 := by
    rw [hw0def]
    exact div_pos_iff.mpr (Or.inr ⟨by linarith, hqden⟩)
  have hw1pos : 0 < w1 := by
    rw [hw1def]
    exact div_pos_iff.mpr (Or.inr ⟨by linarith, hqden⟩)
  set a0 : ℝ := twoPairA0 p0 p q0 (-m) with ha0def
  set a1 : ℝ := twoPairA1 p1 p q1 (-m) with ha1def
  have ha0 : 0 < a0 := by rw [ha0def]; exact twoPairA0_pos hp0p hmneg
  have ha1 : 0 < a1 := by rw [ha1def]; exact twoPairA1_pos hp hpp1 hmneg
  set G : ℝ := ((2:ℝ) ^ q0 * a0) ^ w0 * ((2:ℝ) ^ q1 * a1) ^ w1 with hGdef
  have hGpos : 0 < G := by
    rw [hGdef]
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨(2 * q * G) ^ q⁻¹, Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro T hTnonneg hTsub hTmeas hTzero B0 B1 hB0 hB1 hs0 hs1 f
  -- the vanishing case
  by_cases hfz : f = 0
  · have hTf0 : T f = fun _ => 0 := by
      rw [hfz]
      funext x
      exact hTzero x
    rw [hTf0]
    have : eLpNorm (fun _ : (Euclidean d) => (0:ℝ)) (ENNReal.ofReal q) volume = 0 := by
      simp
    rw [this]
    simp
  -- the main case
  have hJint : Integrable (fun x : (Euclidean d) => ‖f x‖ ^ p) volume :=
    Auto.Spherical.FractalDilations.AHRSUpperBounds.q4_schwartz_integrable_norm_rpow f hp
  set J : ℝ := ∫ x : (Euclidean d), ‖f x‖ ^ p with hJdef
  have hJnn : 0 ≤ J := by
    rw [hJdef]
    exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hJeq : (∫⁻ x : (Euclidean d), (ENNReal.ofReal ‖f x‖) ^ p) = ENNReal.ofReal J := by
    have h1 : (∫⁻ x : (Euclidean d), (ENNReal.ofReal ‖f x‖) ^ p)
        = ∫⁻ x : (Euclidean d), ENNReal.ofReal (‖f x‖ ^ p) := by
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
    rw [h1, hJdef]
    exact (ofReal_integral_eq_lintegral_ofReal hJint
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)).symm
  have hJpos : 0 < J := by
    rcases hJnn.eq_or_lt with h0 | hpos
    · exfalso
      have hzero : ∀ x : (Euclidean d), ‖f x‖ ^ p = 0 := by
        have hcont : Continuous fun x : (Euclidean d) => ‖f x‖ ^ p := by
          refine (Real.continuous_rpow_const hp.le).comp f.continuous.norm
        refine fun x => ?_
        have hnonneg : ∀ y : (Euclidean d), 0 ≤ ‖f y‖ ^ p := fun y =>
          Real.rpow_nonneg (norm_nonneg _) _
        have := (integral_eq_zero_iff_of_nonneg hnonneg hJint).mp (by rw [← hJdef, ← h0])
        have hx := hcont.ae_eq_iff_eq volume (continuous_const (y := (0:ℝ))) |>.mp this
        exact congrFun hx x
      have hf0 : f = 0 := by
        refine SchwartzMap.ext fun x => ?_
        have h := hzero x
        have : ‖f x‖ = 0 := by
          by_contra hne
          have hpos' : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
          exact absurd h (ne_of_gt (Real.rpow_pos_of_pos hpos' p))
        simpa using this
      exact hfz hf0
    · exact hpos
  have hfnorm : eLpNorm ((f : (Euclidean d) → ℂ)) (ENNReal.ofReal p) volume
      = ENNReal.ofReal (J ^ p⁻¹) := by
    rw [eLpNorm_ofReal_eq hp]
    have h1 : (∫⁻ x : (Euclidean d), ‖(f : (Euclidean d) → ℂ) x‖ₑ ^ p) = ENNReal.ofReal J := by
      rw [← hJeq]
      refine lintegral_congr fun x => ?_
      rw [← ofReal_norm]
    rw [h1, ENNReal.ofReal_rpow_of_pos hJpos]
    congr 1
    rw [one_div]
  -- the smooth amplitude split
  obtain ⟨low, high, hlow, hhigh, hsplitpt⟩ := exists_schwartz_smooth_low_high_family f
  have htail0 := twoPair_high_tail_le_of_neg f low high hlow hhigh hp0 hp0p hm hr0 hJpos
    (le_of_eq hJeq) hm0
  have htail1 := twoPair_low_tail_le_of_neg f low hlow hp hpp1 hm hr1 hJpos
    (le_of_eq hJeq) hm1
  -- the two tails in the normalized form
  have hmpow : Measurable (fun t : ℝ => t ^ m) := measurable_id.pow_const m
  have htail0' : (∫⁻ t in Ioi (0 : ℝ),
      (eLpNorm ((high (t ^ m) : (Euclidean d) → ℂ)) (ENNReal.ofReal p0) volume) ^ q0
        * (ENNReal.ofReal t) ^ (q - q0 - 1))
      ≤ ENNReal.ofReal (a0 * J ^ r0) := by
    refine htail0.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [ha0def, twoPairA0, ← hr0def]
    ring
  have htail1' : (∫⁻ t in Ioi (0 : ℝ),
      (eLpNorm ((low (t ^ m) : (Euclidean d) → ℂ)) (ENNReal.ofReal p1) volume) ^ q1
        * (ENNReal.ofReal t) ^ (q - q1 - 1))
      ≤ ENNReal.ofReal (a1 * J ^ r1) := by
    refine htail1.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [ha1def, twoPairA1, ← hr1def]
    ring
  -- measurability of the two profiles
  have hmeas0 : Measurable (fun t : ℝ =>
      (eLpNorm ((high (t ^ m) : (Euclidean d) → ℂ)) (ENNReal.ofReal p0) volume) ^ q0) := by
    have h : Measurable (fun t : ℝ =>
        (eLpNorm ((high t : (Euclidean d) → ℂ)) (ENNReal.ofReal p0) volume) ^ q0) := by
      have heq : (fun t : ℝ => (eLpNorm ((high t : (Euclidean d) → ℂ)) (ENNReal.ofReal p0) volume) ^ q0)
          = fun t : ℝ => (∫⁻ x : (Euclidean d), (ENNReal.ofReal ‖high t x‖) ^ p0) ^ (q0 / p0) := by
        funext t
        exact eLpNorm_rpow_eq hp0
      rw [heq]
      exact ENNReal.continuous_rpow_const.measurable.comp
        (measurable_smooth_high_profile_lintegrals f low high hlow hhigh p0)
    exact h.comp hmpow
  have hmeas1 : Measurable (fun t : ℝ =>
      (eLpNorm ((low (t ^ m) : (Euclidean d) → ℂ)) (ENNReal.ofReal p1) volume) ^ q1) := by
    have h : Measurable (fun t : ℝ =>
        (eLpNorm ((low t : (Euclidean d) → ℂ)) (ENNReal.ofReal p1) volume) ^ q1) := by
      have heq : (fun t : ℝ => (eLpNorm ((low t : (Euclidean d) → ℂ)) (ENNReal.ofReal p1) volume) ^ q1)
          = fun t : ℝ => (∫⁻ x : (Euclidean d), (ENNReal.ofReal ‖low t x‖) ^ p1) ^ (q1 / p1) := by
        funext t
        exact eLpNorm_rpow_eq hp1
      rw [heq]
      exact ENNReal.continuous_rpow_const.measurable.comp
        (measurable_smooth_low_profile_lintegrals f low hlow p1)
    exact h.comp hmpow
  -- the split identity
  have hsplitfam : ∀ t : ℝ, f = low (t ^ m) + high (t ^ m) := by
    intro t
    refine SchwartzMap.ext fun x => ?_
    have h := hsplitpt (t ^ m) x
    simpa using h
  -- the balancing scale
  set X0 : ℝ := ((2:ℝ) ^ q0 * a0) * B0 ^ q0 * J ^ r0 with hX0def
  set X1 : ℝ := ((2:ℝ) ^ q1 * a1) * B1 ^ q1 * J ^ r1 with hX1def
  have hX0pos : 0 < X0 := by
    rw [hX0def]
    have h1 : (0:ℝ) < (2:ℝ) ^ q0 := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0:ℝ) < B0 ^ q0 := Real.rpow_pos_of_pos hB0 _
    have h3 : (0:ℝ) < J ^ r0 := Real.rpow_pos_of_pos hJpos _
    positivity
  have hX1pos : 0 < X1 := by
    rw [hX1def]
    have h1 : (0:ℝ) < (2:ℝ) ^ q1 := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0:ℝ) < B1 ^ q1 := Real.rpow_pos_of_pos hB1 _
    have h3 : (0:ℝ) < J ^ r1 := Real.rpow_pos_of_pos hJpos _
    positivity
  set sc : ℝ := (X0 / X1) ^ (q1 - q0)⁻¹ with hscdef
  have hscpos : 0 < sc := by
    rw [hscdef]
    exact Real.rpow_pos_of_pos (div_pos hX0pos hX1pos) _
  -- the two-pair moment estimate
  have hmoment := Auto.Spherical.MSSBase.sourceOutput_two_pair_marcinkiewicz_moment_of_strong_endpoints_and_scaled_split_tails
    (D := (Set.univ : Set (SchwartzMap (Euclidean d) ℂ)))
    (eval := fun g : SchwartzMap (Euclidean d) ℂ => (g : (Euclidean d) → ℂ)) (T := T)
    (μ := (volume : Measure (Euclidean d))) (ν := (volume : Measure (Euclidean d)))
    (fun g x => hTnonneg g x) (fun g h _ _ x => hTsub g h x) (fun g _ => hTmeas g)
    hq0 hq1 hq (ENNReal.ofReal B0) (ENNReal.ofReal B1)
    (fun g _ => hs0 g) (fun g _ => hs1 g) f (hTmeas f).aemeasurable
    (fun t => low (t ^ m)) (fun t => high (t ^ m))
    (fun t => Set.mem_univ _) (fun t => Set.mem_univ _) hsplitfam
    hmeas1 hmeas0 (ENNReal.ofReal (a0 * J ^ r0)) (ENNReal.ofReal (a1 * J ^ r1))
    htail0' htail1' sc hscpos
  -- identify the coefficient
  have hcoeff : Auto.Spherical.MSSBase.sourceOutputTwoPairMarcinkiewiczMomentCoefficient q q0 q1
      ((ENNReal.ofReal B0) ^ q0) ((ENNReal.ofReal B1) ^ q1)
      ((ENNReal.ofReal sc) ^ (q0 - q) * ENNReal.ofReal (a0 * J ^ r0))
      ((ENNReal.ofReal sc) ^ (q1 - q) * ENNReal.ofReal (a1 * J ^ r1))
      = ENNReal.ofReal (q * (X0 * sc ^ (q0 - q) + X1 * sc ^ (q1 - q))) := by
    have hterm0 : (ENNReal.ofReal 2) ^ q0 * ((ENNReal.ofReal B0) ^ q0)
        * ((ENNReal.ofReal sc) ^ (q0 - q) * ENNReal.ofReal (a0 * J ^ r0))
        = ENNReal.ofReal (X0 * sc ^ (q0 - q)) := by
      rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 2),
        ENNReal.ofReal_rpow_of_pos hB0, ENNReal.ofReal_rpow_of_pos hscpos,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hX0def]
      ring
    have hterm1 : (ENNReal.ofReal 2) ^ q1 * ((ENNReal.ofReal B1) ^ q1)
        * ((ENNReal.ofReal sc) ^ (q1 - q) * ENNReal.ofReal (a1 * J ^ r1))
        = ENNReal.ofReal (X1 * sc ^ (q1 - q)) := by
      rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 2),
        ENNReal.ofReal_rpow_of_pos hB1, ENNReal.ofReal_rpow_of_pos hscpos,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hX1def]
      ring
    rw [Auto.Spherical.MSSBase.sourceOutputTwoPairMarcinkiewiczMomentCoefficient,
      hterm0, hterm1, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul hq.le]
  rw [hcoeff] at hmoment
  -- balance the two terms
  have hsceq : (X1 / X0) ^ (q0 - q1)⁻¹ = sc := by
    rw [hscdef, show X1 / X0 = (X0 / X1)⁻¹ from (inv_div X0 X1).symm,
      Real.inv_rpow (le_of_lt (div_pos hX0pos hX1pos)),
      ← Real.rpow_neg (le_of_lt (div_pos hX0pos hX1pos))]
    congr 1
    field_simp
    ring
  have hbal0 := balance_two_terms hX1pos hX0pos hq1q hqq0
  rw [hsceq] at hbal0
  have hw0eq : (q - q1) / (q0 - q1) = w0 := by
    rw [hw0def]
    field_simp
    ring
  have hw1eq : (q0 - q) / (q0 - q1) = w1 := by
    rw [hw1def]
    field_simp
    ring
  have hbal : X0 * sc ^ (q0 - q) + X1 * sc ^ (q1 - q) = 2 * (X0 ^ w0 * X1 ^ w1) := by
    rw [show X0 * sc ^ (q0 - q) + X1 * sc ^ (q1 - q)
        = X1 * sc ^ (q1 - q) + X0 * sc ^ (q0 - q) by ring, hbal0, hw0eq, hw1eq]
    ring
  rw [hbal] at hmoment
  -- expand the geometric mean
  have hexp := geom_mean_expand (A0 := (2:ℝ) ^ q0 * a0) (A1 := (2:ℝ) ^ q1 * a1)
    (B0 := B0) (B1 := B1) (J := J) (q0 := q0) (q1 := q1) (r0 := r0) (r1 := r1)
    (w0 := w0) (w1 := w1)
    (by positivity) (by positivity) hB0 hB1 hJpos
  rw [← hX0def, ← hX1def, ← hGdef] at hexp
  have hcolJ : r0 * w0 + r1 * w1 = q / p := by
    rw [hr0def, hr1def, hw0def, hw1def]
    exact hcol
  rw [hcolJ] at hexp
  rw [hexp] at hmoment
  -- take the q-th root
  have hfinal := Auto.Spherical.MSSBase.sourceOutput_eLpNorm_le_of_nonnegative_moment
    T f hq (hTnonneg f) _ hmoment
  refine hfinal.trans (le_of_eq ?_)
  have hJqp : (0:ℝ) < J ^ (q / p) := Real.rpow_pos_of_pos hJpos _
  rw [ENNReal.ofReal_rpow_of_pos (by positivity :
    (0:ℝ) < q * (2 * (G * (B0 ^ (q0 * w0) * B1 ^ (q1 * w1)) * J ^ (q / p))))]
  rw [hfnorm, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hreal : q * (2 * (G * (B0 ^ (q0 * w0) * B1 ^ (q1 * w1)) * J ^ (q / p)))
      = (2 * q * G) * (B0 ^ (q0 * w0) * B1 ^ (q1 * w1)) * J ^ (q / p) := by ring
  rw [hreal]
  have hroot := root_of_balanced (G := 2 * q * G) (B0 := B0) (B1 := B1)
    (J := J ^ (q / p)) (q := q)
    (e0 := q0 * w0 / q) (e1 := q1 * w1 / q) (f0 := q0 * w0) (f1 := q1 * w1)
    (by positivity) hB0 hB1 hJqp hq rfl rfl
  rw [hroot]
  have hJroot : (J ^ (q / p)) ^ q⁻¹ = J ^ p⁻¹ := by
    rw [← Real.rpow_mul hJpos.le]
    congr 1
    field_simp
  rw [hJroot]
  have he0 : q0 * w0 / q = q0 * ((q1 - q) / (q1 - q0)) / q := by rw [hw0def]
  have he1 : q1 * w1 / q = q1 * ((q - q0) / (q1 - q0)) / q := by rw [hw1def]
  rw [he0, he1]
  ring

/-! ### Finiteness of Schwartz input norms -/

theorem eLpNorm_schwartz_ne_top {d : ℕ} {p : ℝ} (hp : 0 < p)
    (f : SchwartzMap (Euclidean d) ℂ) :
    eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume ≠ ⊤ := by
  have hJint : Integrable (fun x : Euclidean d => ‖f x‖ ^ p) volume :=
    Auto.Spherical.FractalDilations.AHRSUpperBounds.q4_schwartz_integrable_norm_rpow f hp
  rw [eLpNorm_ofReal_eq hp]
  have hconv : (∫⁻ x : Euclidean d, ‖(f : Euclidean d → ℂ) x‖ₑ ^ p)
      = ENNReal.ofReal (∫ x : Euclidean d, ‖f x‖ ^ p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hJint
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  rw [hconv]
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top

/-! ### Elementary properties of the fractal maximal operator as an operator -/

theorem fractalSphericalMaximalReal_nonneg' {d : ℕ} (E : Set ℝ)
    (f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    0 ≤ fractalSphericalMaximalReal d E f x := by
  unfold fractalSphericalMaximalReal
  exact ENNReal.toReal_nonneg

/-! ### Interpolation at a common output exponent -/

/-- **Same-output interpolation of strong types.** -/
theorem hasFractalSphericalStrongType_interp_same_output {d : ℕ} {E : Set ℝ}
    (hd : 0 < d) (hEpos : E ⊆ Ioi (0 : ℝ)) {p0 p1 p q : ℝ}
    (hp0 : 0 < p0) (hp0p : p0 < p) (hpp1 : p < p1) (hq : 1 ≤ q)
    (h0 : HasFractalSphericalStrongType d E p0 q)
    (h1 : HasFractalSphericalStrongType d E p1 q) :
    HasFractalSphericalStrongType d E p q := by
  obtain ⟨C0, hC0, hb0⟩ := h0
  obtain ⟨C1, hC1, hb1⟩ := h1
  refine ⟨C0 * (4 : ℝ) ^ ((p - p0) / p0) + C1 * (2 : ℝ) ^ ((p - p1) / p1), by positivity,
    fun f => ?_⟩
  have hmain := memLp_and_eLpNorm_schwartz_of_two_strong_inputs_same_output
    (fractalSphericalMaximalReal d E)
    (fun g => (measurable_fractalSphericalMaximalReal E g).aestronglyMeasurable)
    (fun g x => fractalSphericalMaximalReal_nonneg' E g x)
    (fun g h x => Auto.Spherical.FractalDilations.AHRSLowerBounds.fractalSphericalMaximalReal_schwartz_add_le hd E hEpos g h x)
    (by funext x; exact Auto.Spherical.FractalDilations.AHRSLowerBounds.fractalSphericalMaximalReal_zero E x)
    hp0 hp0p hpp1 hq (ENNReal.ofReal C0) (ENNReal.ofReal C1) hb0 hb1 f
  obtain ⟨hmem, hbd⟩ := hmain
  refine ⟨hmem, hbd.trans (le_of_eq ?_)⟩
  congr 1
  rw [sameOutputInputInterpolationConstant, ← ENNReal.ofReal_mul hC0.le,
    ← ENNReal.ofReal_mul hC1.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-! ### Interpolation along a segment of positive slope -/

/-- **Two-pair interpolation of strong types, positive slope.** -/
theorem hasFractalSphericalStrongType_interp_twoPair {d : ℕ} {E : Set ℝ}
    (hd : 0 < d) (hEpos : E ⊆ Ioi (0 : ℝ)) {p0 q0 p1 q1 p q m : ℝ}
    (hp0 : 0 < p0) (hp0p : p0 < p) (hpp1 : p < p1)
    (hq0 : 0 < q0) (hq0q : q0 < q) (hqq1 : q < q1)
    (hr0 : 1 ≤ q0 / p0) (hr1 : 1 ≤ q1 / p1) (hm : 0 < m)
    (hm0 : q - q0 = m * (p - p0) * (q0 / p0))
    (hm1 : q - q1 = m * (p - p1) * (q1 / p1))
    (hcol : (q0 / p0) * ((q1 - q) / (q1 - q0)) + (q1 / p1) * ((q - q0) / (q1 - q0))
      = q / p)
    (h0 : HasFractalSphericalStrongType d E p0 q0)
    (h1 : HasFractalSphericalStrongType d E p1 q1) :
    HasFractalSphericalStrongType d E p q := by
  have hp : 0 < p := lt_trans hp0 hp0p
  obtain ⟨C0, hC0, hb0⟩ := h0
  obtain ⟨C1, hC1, hb1⟩ := h1
  obtain ⟨C, hCpos, hC⟩ := exists_twoPair_interpolation_const (d := d)
    hp0 hp0p hpp1 hq0 hq0q hqq1 hr0 hr1 hm hm0 hm1 hcol
  refine ⟨C * C0 ^ (q0 * ((q1 - q) / (q1 - q0)) / q)
      * C1 ^ (q1 * ((q - q0) / (q1 - q0)) / q), by positivity, fun f => ?_⟩
  have hbd := hC (fractalSphericalMaximalReal d E)
    (fun g x => fractalSphericalMaximalReal_nonneg' E g x)
    (fun g h x => Auto.Spherical.FractalDilations.AHRSLowerBounds.fractalSphericalMaximalReal_schwartz_add_le hd E hEpos g h x)
    (fun g => (measurable_fractalSphericalMaximalReal E g).aestronglyMeasurable)
    (fun x => Auto.Spherical.FractalDilations.AHRSLowerBounds.fractalSphericalMaximalReal_zero E x)
    C0 C1 hC0 hC1 (fun g => (hb0 g).2) (fun g => (hb1 g).2) f
  refine ⟨⟨(hb0 f).1.1, ?_⟩, hbd⟩
  refine lt_of_le_of_lt hbd ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr (eLpNorm_schwartz_ne_top hp f))

/-- **Two-pair interpolation of strong types, negative slope.** -/
theorem hasFractalSphericalStrongType_interp_twoPair_neg {d : ℕ} {E : Set ℝ}
    (hd : 0 < d) (hEpos : E ⊆ Ioi (0 : ℝ)) {p0 q0 p1 q1 p q m : ℝ}
    (hp0 : 0 < p0) (hp0p : p0 < p) (hpp1 : p < p1)
    (hq1 : 0 < q1) (hq1q : q1 < q) (hqq0 : q < q0)
    (hr0 : 1 ≤ q0 / p0) (hr1 : 1 ≤ q1 / p1) (hm : m < 0)
    (hm0 : q - q0 = m * (p - p0) * (q0 / p0))
    (hm1 : q - q1 = m * (p - p1) * (q1 / p1))
    (hcol : (q0 / p0) * ((q1 - q) / (q1 - q0)) + (q1 / p1) * ((q - q0) / (q1 - q0))
      = q / p)
    (h0 : HasFractalSphericalStrongType d E p0 q0)
    (h1 : HasFractalSphericalStrongType d E p1 q1) :
    HasFractalSphericalStrongType d E p q := by
  have hp : 0 < p := lt_trans hp0 hp0p
  obtain ⟨C0, hC0, hb0⟩ := h0
  obtain ⟨C1, hC1, hb1⟩ := h1
  obtain ⟨C, hCpos, hC⟩ := exists_twoPair_interpolation_const_of_neg (d := d)
    hp0 hp0p hpp1 hq1 hq1q hqq0 hr0 hr1 hm hm0 hm1 hcol
  refine ⟨C * C0 ^ (q0 * ((q1 - q) / (q1 - q0)) / q)
      * C1 ^ (q1 * ((q - q0) / (q1 - q0)) / q), by positivity, fun f => ?_⟩
  have hbd := hC (fractalSphericalMaximalReal d E)
    (fun g x => fractalSphericalMaximalReal_nonneg' E g x)
    (fun g h x => Auto.Spherical.FractalDilations.AHRSLowerBounds.fractalSphericalMaximalReal_schwartz_add_le hd E hEpos g h x)
    (fun g => (measurable_fractalSphericalMaximalReal E g).aestronglyMeasurable)
    (fun x => Auto.Spherical.FractalDilations.AHRSLowerBounds.fractalSphericalMaximalReal_zero E x)
    C0 C1 hC0 hC1 (fun g => (hb0 g).2) (fun g => (hb1 g).2) f
  refine ⟨⟨(hb0 f).1.1, ?_⟩, hbd⟩
  refine lt_of_le_of_lt hbd ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr (eLpNorm_schwartz_ne_top hp f))

/-! ### Interpolation along a segment with increasing input exponent -/

/-- **Interpolation of strong types along a segment of the reciprocal diagram.**  The two
endpoints are ordered by their input exponents; the three collinear cases (vertical, positive
slope, negative slope) are handled by the three interpolation devices. -/
theorem hasFractalSphericalStrongType_interp_of_lt {d : ℕ} {E : Set ℝ}
    (hd : 0 < d) (hEpos : E ⊆ Ioi (0 : ℝ)) {p0 q0 p1 q1 p q lam : ℝ}
    (hp0 : 0 < p0) (hp1 : 0 < p1) (hq0one : 1 ≤ q0) (hq1one : 1 ≤ q1)
    (hpq0 : p0 ≤ q0) (hpq1 : p1 ≤ q1) (hp01 : p0 < p1)
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hpa : p⁻¹ = (1 - lam) * p0⁻¹ + lam * p1⁻¹)
    (hqb : q⁻¹ = (1 - lam) * q0⁻¹ + lam * q1⁻¹)
    (h0 : HasFractalSphericalStrongType d E p0 q0)
    (h1 : HasFractalSphericalStrongType d E p1 q1) :
    HasFractalSphericalStrongType d E p q := by
  have hq0 : 0 < q0 := lt_of_lt_of_le zero_lt_one hq0one
  have hq1 : 0 < q1 := lt_of_lt_of_le zero_lt_one hq1one
  have hlam1' : 0 < 1 - lam := by linarith
  have hpinv : 0 < p⁻¹ := by
    rw [hpa]
    exact add_pos (mul_pos hlam1' (inv_pos.mpr hp0)) (mul_pos hlam0 (inv_pos.mpr hp1))
  have hp : 0 < p := inv_pos.mp hpinv
  have hqinv : 0 < q⁻¹ := by
    rw [hqb]
    exact add_pos (mul_pos hlam1' (inv_pos.mpr hq0)) (mul_pos hlam0 (inv_pos.mpr hq1))
  have hq : 0 < q := inv_pos.mp hqinv
  have hpne : p ≠ 0 := ne_of_gt hp
  have hqne : q ≠ 0 := ne_of_gt hq
  have hp0ne : p0 ≠ 0 := ne_of_gt hp0
  have hp1ne : p1 ≠ 0 := ne_of_gt hp1
  have hq0ne : q0 ≠ 0 := ne_of_gt hq0
  have hq1ne : q1 ≠ 0 := ne_of_gt hq1
  -- the output exponent is at least one
  have hq0inv : q0⁻¹ ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hq0one (le_of_lt (inv_pos.mpr hq0))
    rw [mul_one, inv_mul_cancel₀ hq0ne] at hmul
    exact hmul
  have hq1inv : q1⁻¹ ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hq1one (le_of_lt (inv_pos.mpr hq1))
    rw [mul_one, inv_mul_cancel₀ hq1ne] at hmul
    exact hmul
  have hqinvle : q⁻¹ ≤ 1 := by
    rw [hqb]
    have t0 := mul_le_mul_of_nonneg_left hq0inv hlam1'.le
    have t1 := mul_le_mul_of_nonneg_left hq1inv hlam0.le
    rw [mul_one] at t0 t1
    linarith
  have hqone : 1 ≤ q := by
    have hmul := mul_le_mul_of_nonneg_left hqinvle hq.le
    rw [mul_one, mul_inv_cancel₀ hqne] at hmul
    exact hmul
  -- the reciprocal gaps
  set Da : ℝ := p0⁻¹ - p1⁻¹ with hDadef
  set Db : ℝ := q0⁻¹ - q1⁻¹ with hDbdef
  have hDapos : 0 < Da := by
    rw [hDadef]
    have hinv : p1⁻¹ < p0⁻¹ := (inv_lt_inv₀ hp1 hp0).mpr hp01
    linarith
  have hDane : Da ≠ 0 := ne_of_gt hDapos
  -- the four difference identities
  have hdp0 : p - p0 = p * p0 * (lam * Da) := by
    have hstep : p0⁻¹ - p⁻¹ = lam * Da := by rw [hpa, hDadef]; ring
    have hbase : p - p0 = p * p0 * (p0⁻¹ - p⁻¹) := by field_simp
    rw [hbase, hstep]
  have hdp1 : p - p1 = -(p * p1 * ((1 - lam) * Da)) := by
    have hstep : p1⁻¹ - p⁻¹ = -((1 - lam) * Da) := by rw [hpa, hDadef]; ring
    have hbase : p - p1 = p * p1 * (p1⁻¹ - p⁻¹) := by field_simp
    rw [hbase, hstep]
    ring
  have hdq0 : q - q0 = q * q0 * (lam * Db) := by
    have hstep : q0⁻¹ - q⁻¹ = lam * Db := by rw [hqb, hDbdef]; ring
    have hbase : q - q0 = q * q0 * (q0⁻¹ - q⁻¹) := by field_simp
    rw [hbase, hstep]
  have hdq1 : q - q1 = -(q * q1 * ((1 - lam) * Db)) := by
    have hstep : q1⁻¹ - q⁻¹ = -((1 - lam) * Db) := by rw [hqb, hDbdef]; ring
    have hbase : q - q1 = q * q1 * (q1⁻¹ - q⁻¹) := by field_simp
    rw [hbase, hstep]
    ring
  -- the input exponent is strictly between the endpoints
  have hp0p : p0 < p := by
    have hpos : 0 < p * p0 * (lam * Da) :=
      mul_pos (mul_pos hp hp0) (mul_pos hlam0 hDapos)
    linarith [hdp0]
  have hpp1 : p < p1 := by
    have hpos : 0 < p * p1 * ((1 - lam) * Da) :=
      mul_pos (mul_pos hp hp1) (mul_pos hlam1' hDapos)
    linarith [hdp1]
  have hr0 : 1 ≤ q0 / p0 := (one_le_div hp0).mpr hpq0
  have hr1 : 1 ≤ q1 / p1 := (one_le_div hp1).mpr hpq1
  -- the amplitude-scale identities
  have hm0 : q - q0 = ((q / p) * (Db / Da)) * (p - p0) * (q0 / p0) := by
    rw [hdq0, hdp0]
    field_simp
  have hm1 : q - q1 = ((q / p) * (Db / Da)) * (p - p1) * (q1 / p1) := by
    rw [hdq1, hdp1]
    field_simp
  have hq10 : q1 - q0 = q0 * q1 * Db := by
    rw [hDbdef]
    field_simp
  have hq1q : q1 - q = q * q1 * ((1 - lam) * Db) := by linarith [hdq1]
  have hcolgen : Db ≠ 0 →
      (q0 / p0) * ((q1 - q) / (q1 - q0)) + (q1 / p1) * ((q - q0) / (q1 - q0)) = q / p := by
    intro hDbne
    rw [hq1q, hdq0, hq10, div_eq_mul_inv q p, hpa]
    field_simp
  rcases lt_trichotomy Db 0 with hDbneg | hDbzero | hDbpos
  · -- negative slope
    have hDbne : Db ≠ 0 := ne_of_lt hDbneg
    have hqq0 : q < q0 := by
      have hneg : q * q0 * (lam * Db) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hq hq0) (mul_neg_of_pos_of_neg hlam0 hDbneg)
      linarith [hdq0]
    have hq1q' : q1 < q := by
      have hneg : q * q1 * ((1 - lam) * Db) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hq hq1) (mul_neg_of_pos_of_neg hlam1' hDbneg)
      linarith [hdq1]
    have hmneg : (q / p) * (Db / Da) < 0 := by
      have h1 : 0 < q / p := div_pos hq hp
      have h2 : Db / Da < 0 := div_neg_of_neg_of_pos hDbneg hDapos
      exact mul_neg_of_pos_of_neg h1 h2
    exact hasFractalSphericalStrongType_interp_twoPair_neg hd hEpos hp0 hp0p hpp1
      hq1 hq1q' hqq0 hr0 hr1 hmneg hm0 hm1 (hcolgen hDbne) h0 h1
  · -- equal output exponents
    have hq01 : q0 = q1 := by
      have hinv : q0⁻¹ = q1⁻¹ := by
        rw [hDbdef] at hDbzero
        linarith
      have := congrArg (fun x : ℝ => x⁻¹) hinv
      simpa using this
    have hqeq : q = q0 := by
      have hinv : q⁻¹ = q0⁻¹ := by
        rw [hqb, ← hq01]
        ring
      have := congrArg (fun x : ℝ => x⁻¹) hinv
      simpa using this
    rw [hqeq]
    refine hasFractalSphericalStrongType_interp_same_output hd hEpos hp0 hp0p hpp1
      hq0one h0 ?_
    rw [hq01]
    exact h1
  · -- positive slope
    have hDbne : Db ≠ 0 := ne_of_gt hDbpos
    have hq0q : q0 < q := by
      have hpos : 0 < q * q0 * (lam * Db) :=
        mul_pos (mul_pos hq hq0) (mul_pos hlam0 hDbpos)
      linarith [hdq0]
    have hqq1 : q < q1 := by
      have hpos : 0 < q * q1 * ((1 - lam) * Db) :=
        mul_pos (mul_pos hq hq1) (mul_pos hlam1' hDbpos)
      linarith [hdq1]
    have hmpos : 0 < (q / p) * (Db / Da) :=
      mul_pos (div_pos hq hp) (div_pos hDbpos hDapos)
    exact hasFractalSphericalStrongType_interp_twoPair hd hEpos hp0 hp0p hpp1
      hq0 hq0q hqq1 hr0 hr1 hmpos hm0 hm1 (hcolgen hDbne) h0 h1

/-! ### Interpolation of strong types, unordered form -/

/-- **Interpolation of strong types.**  If the fractal spherical maximal operator is of strong
type at two exponent pairs, then it is of strong type at every pair whose reciprocal point lies
on the segment joining the two reciprocal points. -/
theorem hasFractalSphericalStrongType_interp {d : ℕ} {E : Set ℝ}
    (hd : 0 < d) (hEpos : E ⊆ Ioi (0 : ℝ)) {p0 q0 p1 q1 p q lam : ℝ}
    (hp0 : 0 < p0) (hp1 : 0 < p1) (hq0one : 1 ≤ q0) (hq1one : 1 ≤ q1)
    (hpq0 : p0 ≤ q0) (hpq1 : p1 ≤ q1)
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hpa : p⁻¹ = (1 - lam) * p0⁻¹ + lam * p1⁻¹)
    (hqb : q⁻¹ = (1 - lam) * q0⁻¹ + lam * q1⁻¹)
    (h0 : HasFractalSphericalStrongType d E p0 q0)
    (h1 : HasFractalSphericalStrongType d E p1 q1) :
    HasFractalSphericalStrongType d E p q := by
  have hq0 : 0 < q0 := lt_of_lt_of_le zero_lt_one hq0one
  have hq1 : 0 < q1 := lt_of_lt_of_le zero_lt_one hq1one
  have hlam1' : 0 < 1 - lam := by linarith
  rcases lt_trichotomy p0 p1 with hlt | heq | hgt
  · exact hasFractalSphericalStrongType_interp_of_lt hd hEpos hp0 hp1 hq0one hq1one
      hpq0 hpq1 hlt hlam0 hlam1 hpa hqb h0 h1
  · -- equal input exponents
    have hpinveq : p⁻¹ = p0⁻¹ := by
      rw [hpa, ← heq]
      ring
    have hpeq : p = p0 := by
      have := congrArg (fun x : ℝ => x⁻¹) hpinveq
      simpa using this
    have hqinv : 0 < q⁻¹ := by
      rw [hqb]
      exact add_pos (mul_pos hlam1' (inv_pos.mpr hq0)) (mul_pos hlam0 (inv_pos.mpr hq1))
    have hq : 0 < q := inv_pos.mp hqinv
    have h1' : HasFractalSphericalStrongType d E p0 q1 := by
      rw [heq]
      exact h1
    rw [hpeq]
    exact hasFractalSphericalStrongType_interp_same_input hq0 hq1 hq hlam0 hlam1 hqb h0 h1'
  · -- the reversed segment
    refine hasFractalSphericalStrongType_interp_of_lt hd hEpos hp1 hp0 hq1one hq0one
      hpq1 hpq0 hgt (lam := 1 - lam) (by linarith) (by linarith) ?_ ?_ h1 h0
    · rw [hpa]; ring
    · rw [hqb]; ring

/-! ### Convexity of the type set -/

/-- **The type set is convex.**  This is the interpolation half of Theorem 1.2(i). -/
theorem convex_fractalTypeSet {d : ℕ} {E : Set ℝ} (hd : 2 ≤ d)
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) :
    Convex ℝ (fractalTypeSet d E) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hEpos : E ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le zero_lt_one (hE ht).1
  rintro z0 ⟨p0, q0, hp0, hq0one, hz0, hst0⟩ z1 ⟨p1, q1, hp1, hq1one, hz1, hst1⟩ a b ha hb hab
  have hq0 : 0 < q0 := lt_of_lt_of_le zero_lt_one hq0one
  have hq1 : 0 < q1 := lt_of_lt_of_le zero_lt_one hq1one
  have hpq0 : p0 ≤ q0 := le_of_hasFractalSphericalStrongType hd hE hEne hp0 hq0one hst0
  have hpq1 : p1 ≤ q1 := le_of_hasFractalSphericalStrongType hd hE hEne hp1 hq1one hst1
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · -- `a = 0`
    have hb1 : b = 1 := by linarith
    have hzero : a • z0 + b • z1 = z1 := by
      rw [← ha0, hb1, zero_smul, one_smul, zero_add]
    rw [hzero]
    exact ⟨p1, q1, hp1, hq1one, hz1, hst1⟩
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · -- `b = 0`
    have ha1 : a = 1 := by linarith
    have hzero : a • z0 + b • z1 = z0 := by
      rw [← hb0, ha1, zero_smul, one_smul, add_zero]
    rw [hzero]
    exact ⟨p0, q0, hp0, hq0one, hz0, hst0⟩
  -- the interior of the segment
  have haeq : a = 1 - b := by linarith
  have hb1 : b < 1 := by linarith
  set P : ℝ := (1 - b) * p0⁻¹ + b * p1⁻¹ with hPdef
  set Q : ℝ := (1 - b) * q0⁻¹ + b * q1⁻¹ with hQdef
  have hb1' : 0 < 1 - b := by linarith
  have hPpos : 0 < P := by
    rw [hPdef]
    exact add_pos (mul_pos hb1' (inv_pos.mpr hp0)) (mul_pos hbpos (inv_pos.mpr hp1))
  have hQpos : 0 < Q := by
    rw [hQdef]
    exact add_pos (mul_pos hb1' (inv_pos.mpr hq0)) (mul_pos hbpos (inv_pos.mpr hq1))
  have hPinv : (P⁻¹)⁻¹ = P := inv_inv P
  have hQinv : (Q⁻¹)⁻¹ = Q := inv_inv Q
  -- the interpolated point is the reciprocal point of the interpolated exponents
  have hpoint : a • z0 + b • z1 = reciprocalExponentPoint P⁻¹ Q⁻¹ := by
    rw [hz0, hz1, reciprocalExponentPoint, reciprocalExponentPoint, reciprocalExponentPoint,
      haeq]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [hPinv, hPdef]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hQinv, hQdef]
  -- the output exponent is at least one
  have hq0inv : q0⁻¹ ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hq0one (le_of_lt (inv_pos.mpr hq0))
    rw [mul_one, inv_mul_cancel₀ (ne_of_gt hq0)] at hmul
    exact hmul
  have hq1inv : q1⁻¹ ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hq1one (le_of_lt (inv_pos.mpr hq1))
    rw [mul_one, inv_mul_cancel₀ (ne_of_gt hq1)] at hmul
    exact hmul
  have hQle : Q ≤ 1 := by
    rw [hQdef]
    have t0 := mul_le_mul_of_nonneg_left hq0inv hb1'.le
    have t1 := mul_le_mul_of_nonneg_left hq1inv hbpos.le
    rw [mul_one] at t0 t1
    linarith
  have hQinvone : 1 ≤ Q⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_left hQle (le_of_lt (inv_pos.mpr hQpos))
    rw [mul_one, inv_mul_cancel₀ (ne_of_gt hQpos)] at hmul
    exact hmul
  rw [hpoint]
  refine ⟨P⁻¹, Q⁻¹, inv_pos.mpr hPpos, hQinvone, rfl, ?_⟩
  exact hasFractalSphericalStrongType_interp hdpos hEpos hp0 hp1 hq0one hq1one hpq0 hpq1
    hbpos hb1 (by rw [hPinv, hPdef]) (by rw [hQinv, hQdef]) hst0 hst1

/-- **The closure of the type set is convex.** -/
theorem convex_closure_fractalTypeSet {d : ℕ} {E : Set ℝ} (hd : 2 ≤ d)
    (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) :
    Convex ℝ (closure (fractalTypeSet d E)) :=
  (convex_fractalTypeSet hd hE hEne).closure

open MeasureTheory Set ENNReal
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSLowerBounds
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.Auxiliary
open Auto.Spherical.FractalDilations.AHRSLowerBounds
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSLowerBounds
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSLowerBounds
open Auto.Spherical.FractalDilations.AHRSLowerBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSLowerBounds
open MeasureTheory Set



/-! ### The band-rate form of the interior estimate -/

/-- A geometric dyadic band rate at the exponent pair `(p,q)`: the `j`-th absolute dyadic
bandpass piece of the maximal operator obeys an `L^p → L^q` estimate with a constant decaying
geometrically in `j`.  This is the form of Corollary 2.5 of arXiv:2004.00984 that the
construction of §7 needs. -/
def HasAbsoluteBandRate {d : Nat} (E : Set Real) (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0) (p q : Real) : Prop :=
  ∃ C rho : ENNReal, C < ⊤ ∧ rho < 1 ∧ ∀ j : Nat, 1 ≤ j →
    ∀ f : SchwartzMap (Euclidean d) Complex,
      MemLp (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume ≤
        (C * rho ^ j) * eLpNorm (f : Euclidean d → Complex) (ENNReal.ofReal p) volume

set_option maxHeartbeats 1000000 in
theorem q4_interior_band_rate_of_two_le_input
    {d : Nat} {E : Set Real} {beta gamma p q : Real}
    (hd : 3 ≤ d ∨ d = 2 ∧ gamma ≤ 1 / 2)
    (hE : E ⊆ Icc (1 : Real) 2) (hEne : E.Nonempty)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) (hgamma_one : gamma ≤ 1)
    (hbeta_gamma : beta ≤ gamma)
    (hMinkowski : upperMinkowskiDimension E = beta)
    (hquasi : quasiAssouadDimension E = gamma)
    (hp : 2 ≤ p) (hpq : p < q)
    (hcap : q < (d : Real) * p)
    (hcrit : beta < ((d : Real) - 1) * (p - 1))
    (phi psi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean d, ‖phi xi‖ ≤ 1)
    (hphiRadial : IsNormRadial (phi : Euclidean d → Complex))
    (hpsi : ∀ eta : Euclidean d, psi eta =
      phi (((2 : Real) ^ (0 + 1))⁻¹ • eta) - phi (((2 : Real) ^ 0)⁻¹ • eta)) :
    HasAbsoluteBandRate E phi hphiOne hphiZero p q := by
  have hd2 : 2 ≤ d := by rcases hd with h | ⟨h, _⟩ <;> omega
  have hD : (2 : Real) ≤ (d : Real) := by exact_mod_cast hd2
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  -- the below exponent
  obtain ⟨qq, hqqgt, hqqlow, hqqone, hqqmax⟩ :
      ∃ qq : Real, q < qq ∧ 1 / (d : Real) < p / qq ∧ p / qq < 1 ∧
        (3 ≤ d → p / qq <
          (((d : Real) - 1) / 2) / ((((d : Real) - 1) / 2) + gamma)) := by
    have hthetamax : 0 < (((d : Real) - 1) / 2) / ((((d : Real) - 1) / 2) + gamma) := by
      apply div_pos (by linarith)
      nlinarith
    rcases hd with hd3 | ⟨hd2', hgh⟩
    · have hD3 : (3 : Real) ≤ (d : Real) := by exact_mod_cast hd3
      have hdpos : (0 : Real) < (d : Real) := by linarith
      set A : Real := ((d : Real) - 1) / 2 with hAdef
      set tm : Real := A / (A + gamma) with htmdef
      have hApos : 0 < A := by rw [hAdef]; linarith
      have hAg : 0 < A + gamma := by linarith
      have htmpos : 0 < tm := by rw [htmdef]; exact div_pos hApos hAg
      have htmone : tm ≤ 1 := by
        rw [htmdef, div_le_one hAg]
        linarith
      have htmlow : 1 < (d : Real) * tm := by
        have hkey : A + gamma < (d : Real) * A := by
          rw [hAdef]
          nlinarith
        rw [htmdef, ← mul_div_assoc, lt_div_iff₀ hAg]
        nlinarith
      have hptm : p ≤ p / tm := by
        rw [le_div_iff₀ htmpos]
        nlinarith
      have hptmlt : p / tm < (d : Real) * p := by
        rw [div_lt_iff₀ htmpos]
        nlinarith
      set M : Real := max q (p / tm) with hMdef
      have hMq : q ≤ M := le_max_left _ _
      have hMpt : p / tm ≤ M := le_max_right _ _
      have hMlt : M < (d : Real) * p := max_lt hcap hptmlt
      refine ⟨(M + (d : Real) * p) / 2, ?_, ?_, ?_, ?_⟩
      · linarith
      · rw [div_lt_div_iff₀ hdpos (by linarith)]
        linarith
      · rw [div_lt_one (by linarith)]
        linarith
      · intro _
        rw [div_lt_iff₀ (by linarith)]
        have h1 : p / tm < (M + (d : Real) * p) / 2 := by linarith
        have h2 : tm * (p / tm) = p := mul_div_cancel₀ p htmpos.ne'
        have h3 := mul_lt_mul_of_pos_left h1 htmpos
        rw [h2] at h3
        linarith
    · subst hd2'
      have h2c : ((2 : Nat) : Real) = 2 := by norm_num
      have hcap2 : q < 2 * p := by
        have h := hcap
        rw [h2c] at h
        linarith
      set M : Real := max q p with hMdef
      have hMq : q ≤ M := le_max_left _ _
      have hMp : p ≤ M := le_max_right _ _
      have hMlt : M < 2 * p := max_lt hcap2 (by linarith)
      refine ⟨(M + 2 * p) / 2, ?_, ?_, ?_, ?_⟩
      · linarith
      · rw [h2c, div_lt_div_iff₀ (by norm_num) (by linarith)]
        linarith
      · rw [div_lt_one (by linarith)]
        linarith
      · intro h3
        omega
  have hqq0 : 0 < qq := by linarith
  -- the below rate
  obtain ⟨C1, rho1, hC1, hrho1, hrate1⟩ :
      ∃ C rho : ENNReal, C < ⊤ ∧ rho < 1 ∧
        ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Auto.Spherical.SurfaceMeasureDecay.Euclidean d) Complex,
          MemLp (fractalDyadicBandpassMaximal d E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
            (ENNReal.ofReal qq) volume ∧
          eLpNorm (fractalDyadicBandpassMaximal d E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
            (ENNReal.ofReal qq) volume ≤
            (C * rho ^ j) *
              eLpNorm (f : Auto.Spherical.SurfaceMeasureDecay.Euclidean d → Complex)
                (ENNReal.ofReal p) volume := by
    rcases eq_or_lt_of_le hp with hpeq | hplt
    · subst hpeq
      exact exists_q4_ltwo_sector_dyadic_rate hd hE hEne hgamma hquasi
        phi hphiOne hphiZero hphiNorm hphiRadial hqq0 hqqlow hqqone hqqmax
    · exact exists_q4_sector_dyadic_rate hd hE hEne hgamma hquasi
        phi hphiOne hphiZero hphiNorm hphiRadial hplt hqq0 hqqlow hqqone hqqmax
  -- the above rate
  obtain ⟨C0, rho0, hC0, hrho0, hrate0⟩ :=
    exists_q2_diagonal_dyadic_rate (d := d) (E := E) (beta := beta)
      (by
        rcases hd with h | ⟨h, hg⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, by linarith⟩)
      hE hEne hbeta hMinkowski phi psi hphiOne hphiZero hphiNorm hpsi hp1 hcrit
  -- interpolate at the common input exponent
  obtain ⟨C, rho, hCtop, hrho, hrate⟩ :=
    memLp_and_eLpNorm_schwartz_of_two_strong_output_dyadic_rates
      (d := d)
      (fun j g => fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g)
      (fun j g => (measurable_fractalDyadicBandpassMaximal E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g).aestronglyMeasurable)
      (fun j g x => fractalDyadicBandpassMaximal_nonneg E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g x)
      (p := p) (q0 := p) (q := q) (q1 := qq) hp0 hp0 hpq hqqgt
      hC0 hC1 hrho0 hrho1
      (fun j hj f => hrate0 j f) hrate1
  exact ⟨C, rho, hCtop, hrho, hrate⟩

set_option maxHeartbeats 1000000 in
theorem q4_interior_band_rate_of_sum_gt_one
    {d : Nat} {E : Set Real} {beta gamma p q : Real}
    (hd : 3 ≤ d ∨ d = 2 ∧ gamma ≤ 1 / 2)
    (hE : E ⊆ Icc (1 : Real) 2) (hEne : E.Nonempty)
    (hbeta : 0 ≤ beta)
    (hMinkowski : upperMinkowskiDimension E = beta)
    (hp1 : 1 < p) (hp2 : p < 2) (hpq : p < q)
    (hsum : q < p / (p - 1))
    (hannulus : (d : Real) * (1 / p) < (1 - beta) * (1 / q) + ((d : Real) - 1))
    (hcrit : beta < ((d : Real) - 1) * (p - 1))
    (phi psi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean d, ‖phi xi‖ ≤ 1)
    (hphiRadial : IsNormRadial (phi : Euclidean d → Complex))
    (hpsi : ∀ eta : Euclidean d, psi eta =
      phi (((2 : Real) ^ (0 + 1))⁻¹ • eta) - phi (((2 : Real) ^ 0)⁻¹ • eta)) :
    HasAbsoluteBandRate E phi hphiOne hphiZero p q := by
  have hd2 : 2 ≤ d := by rcases hd with h | ⟨h, _⟩ <;> omega
  have hD : (2 : Real) ≤ (d : Real) := by exact_mod_cast hd2
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  set s : Real := 1 + q * (p - 1) / p with hsdef
  have hsm : s - 1 = q * (p - 1) / p := by rw [hsdef]; ring
  have hps : p < s := by
    have h : p - 1 < q * (p - 1) / p := by
      rw [lt_div_iff₀ hp0]
      nlinarith
    rw [hsdef]
    linarith
  have hs2 : s < 2 := by
    have hqp : q * (p - 1) < p := (lt_div_iff₀ hpm).mp hsum
    have h : q * (p - 1) / p < 1 := by
      rw [div_lt_one hp0]
      exact hqp
    rw [hsdef]
    linarith
  have hs1 : 1 < s := lt_trans hp1 hps
  have hqeq : q = p * (s - 1) / (p - 1) := by
    rw [hsm]
    field_simp
  set c1 : Real := ((d : Real) - 1) * (s - 1) - beta with hc1def
  set c2 : Real := (1 - beta) * (1 / q) + ((d : Real) - 1) - (d : Real) * (1 / p)
    with hc2def
  have hc1 : 0 < c1 := by
    rw [hc1def]
    have h1 : (p - 1) < s - 1 := by linarith
    nlinarith
  have hc2 : 0 < c2 := by rw [hc2def]; linarith
  set m : Real := min c1 (c2 * q) / 4 with hmdef
  have hm : 0 < m := by
    rw [hmdef]
    have : 0 < min c1 (c2 * q) := lt_min hc1 (by positivity)
    linarith
  have hmc1 : 2 * m < c1 := by
    rw [hmdef]
    have : min c1 (c2 * q) ≤ c1 := min_le_left _ _
    linarith
  have hmc2 : 2 * m < c2 * q := by
    rw [hmdef]
    have : min c1 (c2 * q) ≤ c2 * q := min_le_right _ _
    linarith
  have hM : HasUpperMinkowskiExponent E (beta + m) :=
    hasUpperMinkowskiExponent_add_of_upperMinkowskiDimension_eq hE hMinkowski hm
  have halpha : 0 ≤ beta + m := by linarith
  have hcritical : beta + m + m < ((d : Real) - 1) * (s - 1) := by
    rw [hc1def] at hmc1
    linarith
  have hgainReal : q < s + (((d : Real) - 1) * s - ((d : Real) - 1) -
      (beta + m + m)) := by
    have hkey : beta + 2 * m < 1 + ((d : Real) - 1) * q - (d : Real) * q / p := by
      have hexp : c2 * q = (1 - beta) + ((d : Real) - 1) * q - (d : Real) * q / p := by
        rw [hc2def]
        field_simp
      rw [hexp] at hmc2
      linarith
    have hsq : (d : Real) * s = (d : Real) + (d : Real) * q -
        (d : Real) * q / p := by
      rw [hsdef]
      field_simp
      ring
    nlinarith
  -- the crossed rate at (p, q)
  obtain ⟨C, rho, hC, hCtop, hrho0, hrho, hrate⟩ :
      ∃ C rho : ENNReal, 0 < C ∧ C < ⊤ ∧ 0 < rho ∧ rho < 1 ∧
        ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Auto.Spherical.SurfaceMeasureDecay.Euclidean d) Complex,
          MemLp (fractalDyadicBandpassMaximal d E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
            (ENNReal.ofReal q) volume ∧
          eLpNorm (fractalDyadicBandpassMaximal d E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
            (ENNReal.ofReal q) volume ≤
            C * rho ^ j *
              eLpNorm (f : Auto.Spherical.SurfaceMeasureDecay.Euclidean d → Complex)
                (ENNReal.ofReal p) volume := by
    rcases hd with hd3 | ⟨hd2', hgh⟩
    · obtain ⟨n, rfl⟩ : ∃ n : Nat, d = n + 1 := ⟨d - 1, by omega⟩
      have hcast : ((n : Nat) : Real) = ((n + 1 : Nat) : Real) - 1 := by
        push_cast
        ring
      obtain ⟨C, rho, hC, hCtop, hrho0, hrho, hrate⟩ :=
        minkowski_t123_physical_crossed_dyadic_rate_of_hasUpperMinkowskiExponent
          (n := n) (alpha := beta + m) (eta := m) (p := p) (q := q) (s := s)
          (by omega) hE hEne halpha hM
          hp1 hps hs2 hm (by rw [hcast]; exact hcritical) hqeq
          (by
            unfold q2PhysicalMinkowskiKappaWithLoss
            rw [hcast]
            linarith [hgainReal])
          phi psi hphiOne hphiZero hphiNorm hpsi
      exact ⟨C, rho, hC, hCtop, hrho0, hrho, hrate⟩
    · subst hd2'
      obtain ⟨C, rho, hC, hCtop, hrho0, hrho, hrate⟩ :=
        minkowski_t123_physical_crossed_planar_dyadic_rate_of_hasUpperMinkowskiExponent
          (alpha := beta + m) (eta := m) (p := p) (q := q) (s := s)
          hE hEne halpha hM hp1 hps hs2 hm
          (by
            have hone : ((2 : Nat) : Real) - 1 = 1 := by norm_num
            nlinarith [hcritical])
          hqeq
          (by
            unfold q2PhysicalMinkowskiKappaWithLoss
            have hone : ((1 : Nat) : Real) = 1 := by norm_num
            rw [hone]
            have h2 : ((2 : Nat) : Real) = 2 := by norm_num
            rw [h2] at hgainReal
            linarith [hgainReal])
          phi psi hphiOne hphiZero hphiNorm hpsi
      exact ⟨C, rho, hC, hCtop, hrho0, hrho, hrate⟩
  refine ⟨C, rho, hCtop, hrho, ?_⟩
  intro j hj f
  obtain ⟨hmem, hbound⟩ := hrate j hj f
  exact ⟨hmem, by simpa only [mul_assoc] using hbound⟩

set_option maxHeartbeats 1000000 in
theorem q4_interior_band_rate_of_strict_lower_sector
    {d : Nat} {E : Set Real} {gamma p q : Real}
    (hd : 3 ≤ d ∨ d = 2 ∧ gamma ≤ 1 / 2)
    (hE : E ⊆ Icc (1 : Real) 2) (hEne : E.Nonempty)
    (hgamma : 0 ≤ gamma)
    (hquasi : quasiAssouadDimension E = gamma)
    {beta : Real} (hbeta : 0 ≤ beta) (hbeta_gamma : beta ≤ gamma)
    (hgamma_one : gamma ≤ 1)
    (hp1 : 1 < p) (hp2 : p < 2) (hpq : p < q)
    (hcap : q < (d : Real) * p)
    (hslope : p / (q * (p - 1)) <
      (((d : Real) - 1) / 2) / ((((d : Real) - 1) / 2) + gamma))
    (phi psi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean d, ‖phi xi‖ ≤ 1)
    (hphiRadial : IsNormRadial (phi : Euclidean d → Complex))
    (hpsi : ∀ eta : Euclidean d, psi eta =
      phi (((2 : Real) ^ (0 + 1))⁻¹ • eta) - phi (((2 : Real) ^ 0)⁻¹ • eta)) :
    HasAbsoluteBandRate E phi hphiOne hphiZero p q := by
  have hd2 : 2 ≤ d := by rcases hd with h | ⟨h, _⟩ <;> omega
  have hD : (2 : Real) ≤ (d : Real) := by exact_mod_cast hd2
  have hDpos : (0 : Real) < (d : Real) := by linarith
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  set A : Real := ((d : Real) - 1) / 2 with hAdef
  set tm : Real := A / (A + gamma) with htmdef
  have hApos : 0 < A := by rw [hAdef]; linarith
  have hAg : 0 < A + gamma := by linarith
  have htmpos : 0 < tm := by rw [htmdef]; exact div_pos hApos hAg
  have htmone : tm ≤ 1 := by rw [htmdef, div_le_one hAg]; linarith
  set ts : Real := p / (q * (p - 1)) with htsdef
  have htspos : 0 < ts := by rw [htsdef]; positivity
  have htsmax : ts < tm := hslope
  have htsone : ts < 1 := lt_of_lt_of_le htsmax htmone
  set kappa : Real := (d : Real) - q / p with hkdef
  have hkpos : 0 < kappa := by
    rw [hkdef, sub_pos, div_lt_iff₀ hp0]
    linarith
  have hkle : kappa < (d : Real) := by
    rw [hkdef]
    have : 0 < q / p := by positivity
    linarith
  set delta : Real := kappa / (4 * (d : Real)) with hddef
  set eta : Real := kappa / 4 with hedef
  have hdpos : 0 < delta := by rw [hddef]; positivity
  have hepos : 0 < eta := by rw [hedef]; positivity
  have hdhalf : delta < 1 / 2 := by
    rw [hddef, div_lt_iff₀ (by positivity)]
    linarith
  set t1 : Real := ts * (1 - delta) with ht1def
  set t0 : Real := (ts + tm) / 2 with ht0def
  have ht1pos : 0 < t1 := by rw [ht1def]; nlinarith
  have ht1ts : t1 < ts := by rw [ht1def]; nlinarith
  have ht1one : t1 < 1 := lt_trans ht1ts htsone
  have ht0pos : 0 < t0 := by rw [ht0def]; linarith
  have ht0ts : ts < t0 := by rw [ht0def]; linarith
  have ht0tm : t0 < tm := by rw [ht0def]; linarith
  have ht0one : t0 < 1 := lt_of_lt_of_le ht0tm htmone
  -- gap exponents
  have hgap : ∀ t : Real, 0 < t → t < tm → q4GapExponent d gamma t < 0 := by
    intro t htpos httm
    unfold q4GapExponent
    rw [htmdef, hAdef, lt_div_iff₀ hAg] at httm
    nlinarith
  -- output bracketing
  have hout : ∀ t : Real, 0 < t →
      q4LowerWeakOutputExponent p (2 / t) = p / (t * (p - 1)) := by
    intro t htpos
    unfold q4LowerWeakOutputExponent
    field_simp
  have hq0q : q4LowerWeakOutputExponent p (2 / t0) < q := by
    rw [hout t0 ht0pos, div_lt_iff₀ (by positivity)]
    rw [htsdef, div_lt_iff₀ (by positivity)] at ht0ts
    nlinarith
  have ht1val : t1 * (p - 1) = p * (1 - delta) / q := by
    rw [ht1def, htsdef]
    field_simp
  have hqq1 : q < q4LowerWeakOutputExponent p (2 / t1) := by
    rw [hout t1 ht1pos, lt_div_iff₀ (mul_pos ht1pos hpm), ht1val]
    have hcancel : q * (p * (1 - delta) / q) = p * (1 - delta) := by
      field_simp
    rw [hcancel]
    nlinarith
  -- the net exponent
  set S : Real := (1 / q) * (1 / (t1 * (p - 1)) - (d : Real) + eta) with hSdef
  have hinv1 : 1 / (t1 * (p - 1)) = (q / p) / (1 - delta) := by
    rw [ht1def, htsdef]
    field_simp
  have hSneg : S < 0 := by
    rw [hSdef, hinv1]
    have hbound : (q / p) / (1 - delta) < (d : Real) - eta := by
      rw [div_lt_iff₀ (by linarith)]
      have hqp : q / p = (d : Real) - kappa := by rw [hkdef]; ring
      rw [hqp]
      have hexpand : ((d : Real) - eta) * (1 - delta) =
          (d : Real) - kappa / 2 + kappa ^ 2 / (16 * (d : Real)) := by
        rw [hedef, hddef]
        field_simp
        ring
      rw [hexpand]
      have hpos : 0 < kappa ^ 2 / (16 * (d : Real)) := by positivity
      linarith
    have : 1 / q > 0 := by positivity
    nlinarith
  have hS0 : (2 / t0) * (q4FrequencyExponentWithSubpowerLoss d t0 eta / 2) +
      q4LowerWeakTailExponent p (2 / t0) ≤ q * S := by
    rw [q4_lower_net_exponent_eq hp1 ht0pos, hSdef]
    have hqS : q * ((1 / q) * (1 / (t1 * (p - 1)) - (d : Real) + eta)) =
        1 / (t1 * (p - 1)) - (d : Real) + eta := by
      field_simp
    rw [hqS]
    have hmono : 1 / (t0 * (p - 1)) ≤ 1 / (t1 * (p - 1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    linarith
  have hS1 : (2 / t1) * (q4FrequencyExponentWithSubpowerLoss d t1 eta / 2) +
      q4LowerWeakTailExponent p (2 / t1) ≤ q * S := by
    rw [q4_lower_net_exponent_eq hp1 ht1pos, hSdef]
    have hqS : q * ((1 / q) * (1 / (t1 * (p - 1)) - (d : Real) + eta)) =
        1 / (t1 * (p - 1)) - (d : Real) + eta := by
      field_simp
    rw [hqS]
  obtain ⟨Ccover, hCcover, hcov⟩ :=
    exists_hasSubpowerAssouadCoverBound_of_quasiAssouadDimension_eq hE hquasi hepos
  obtain ⟨C, hC, hrate⟩ :=
    exists_q4_lower_sector_explicit_dyadic_rate hd hE hEne hgamma hepos.le
      hCcover.le hcov phi hphiOne hphiZero hphiNorm hphiRadial hp1 hp2 hq0
      ht0pos ht0one ht1pos ht1one (hgap t0 ht0pos ht0tm) (hgap t1 ht1pos
        (lt_trans ht1ts htsmax)) hq0q hqq1 hS0 hS1
  refine ⟨_, _, hC, ?_, hrate⟩
  refine ENNReal.ofReal_lt_one.mpr ?_
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hSneg

set_option maxHeartbeats 4000000 in
theorem q4_interior_band_rate_of_loss_gain
    {d : Nat} {E : Set Real} {beta gamma p q : Real}
    (hd : 3 ≤ d ∨ d = 2 ∧ gamma ≤ 1 / 2)
    (hE : E ⊆ Icc (1 : Real) 2) (hEne : E.Nonempty)
    (hbeta : 0 ≤ beta) (hgamma : 0 < gamma) (hgamma_one : gamma ≤ 1)
    (hMinkowski : upperMinkowskiDimension E = beta)
    (hquasi : quasiAssouadDimension E = gamma)
    (hp1 : 1 < p) (hp2 : p < 2) (hpq : p < q)
    (hsum : p / (p - 1) < q)
    (hQ3 : p / (p - 1) < (d : Real) + 1 - beta)
    (hbalance : (((d : Real) - 1) / 2) / ((((d : Real) - 1) / 2) + gamma) *
      (1 - 1 / p) ≤ 1 / q)
    (hcluster : 0 < clusterEdgeFunctional d (beta / gamma) beta (1 / p, 1 / q))
    (phi psi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean d, ‖phi xi‖ ≤ 1)
    (hphiRadial : IsNormRadial (phi : Euclidean d → Complex))
    (hpsi : ∀ eta : Euclidean d, psi eta =
      phi (((2 : Real) ^ (0 + 1))⁻¹ • eta) - phi (((2 : Real) ^ 0)⁻¹ • eta)) :
    HasAbsoluteBandRate E phi hphiOne hphiZero p q := by
  have hd2 : 2 ≤ d := by rcases hd with h | ⟨h, _⟩ <;> omega
  have hD : (2 : Real) ≤ (d : Real) := by exact_mod_cast hd2
  have hDpos : (0 : Real) < (d : Real) := by linarith
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  set w : Real := 1 - 1 / p with hwdef
  set y : Real := 1 / q with hydef
  have hwpos : 0 < w := by
    rw [hwdef, sub_pos, div_lt_one hp0]
    linarith
  have hwone : w < 1 := by
    rw [hwdef]
    have : 0 < 1 / p := by positivity
    linarith
  have hypos : 0 < y := by rw [hydef]; positivity
  have hyone : y < 1 := by
    rw [hydef, div_lt_one hq0]
    linarith
  have hwy : y < w := by
    rw [hydef, hwdef]
    have hconj : 1 - 1 / p = (p - 1) / p := by field_simp
    rw [hconj, div_lt_div_iff₀ hq0 hp0]
    have := (div_lt_iff₀ hpm).mp hsum
    linarith
  set A : Real := ((d : Real) - 1) / 2 with hAdef
  have hApos : 0 < A := by rw [hAdef]; linarith
  have hAg : 0 < A + gamma := by linarith
  set tm : Real := A / (A + gamma) with htmdef
  have htmpos : 0 < tm := by rw [htmdef]; exact div_pos hApos hAg
  have htmone : tm ≤ 1 := by rw [htmdef, div_le_one hAg]; linarith
  have hbal : tm * w ≤ y := by rw [htmdef, hAdef, hwdef, hydef] at *; exact hbalance
  set c : Real := clusterEdgeFunctional d (beta / gamma) beta (1 - w, y) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    have hx : (1 : Real) - w = 1 / p := by rw [hwdef]; ring
    rw [hx]
    exact hcluster
  set P : Real := w * gamma * c / (A + gamma) with hPdef
  have hPpos : 0 < P := by
    rw [hPdef]
    exact div_pos (mul_pos (mul_pos hwpos hgamma) hcpos) hAg
  -- the small parameters
  set slack3 : Real := ((d : Real) + 1 - beta) * w - 1 with hs3def
  have hslack3 : 0 < slack3 := by
    rw [hs3def, sub_pos]
    have hwv : w = (p - 1) / p := by rw [hwdef]; field_simp
    have hQ3' : p < ((d : Real) + 1 - beta) * (p - 1) := (div_lt_iff₀ hpm).mp hQ3
    rw [hwv, ← mul_div_assoc, lt_div_iff₀ hp0]
    linarith
  set eps : Real := min (P / 8) (slack3 / 2) with hepsdef
  set eta : Real := P / 8 with hetadef
  set rho : Real := min (tm / 6) (P * tm / (24 * (1 + (d : Real)))) with hrhodef
  have hepspos : 0 < eps := by
    rw [hepsdef]
    exact lt_min (by positivity) (by positivity)
  have hetapos : 0 < eta := by rw [hetadef]; positivity
  have hrhopos : 0 < rho := by
    rw [hrhodef]
    exact lt_min (by positivity) (by positivity)
  have hepsP : eps ≤ P / 8 := by rw [hepsdef]; exact min_le_left _ _
  have hepsS : eps ≤ slack3 / 2 := by rw [hepsdef]; exact min_le_right _ _
  have hrhotm : rho ≤ tm / 6 := by rw [hrhodef]; exact min_le_left _ _
  have hrhoP : rho ≤ P * tm / (24 * (1 + (d : Real))) := by
    rw [hrhodef]; exact min_le_right _ _
  -- shell parameters
  set t0 : Real := tm - rho with ht0def
  set t1 : Real := tm - 3 * rho with ht1def
  set u : Real := (tm - 2 * rho) * w with hudef
  have ht1pos : 0 < t1 := by rw [ht1def]; linarith
  have ht1t0 : t1 < t0 := by rw [ht1def, ht0def]; linarith
  have ht0tm : t0 < tm := by rw [ht0def]; linarith
  have ht0pos : 0 < t0 := lt_trans ht1pos ht1t0
  have ht0one : t0 < 1 := lt_of_lt_of_le ht0tm htmone
  have ht1one : t1 < 1 := lt_trans ht1t0 ht0one
  have ht1tm : t1 < tm := lt_trans ht1t0 ht0tm
  have hupos : 0 < u := by
    rw [hudef]
    apply mul_pos _ hwpos
    linarith
  have huy : u < y := by
    rw [hudef]
    have : (tm - 2 * rho) * w < tm * w := by nlinarith
    linarith
  have hut1 : t1 * w < u := by rw [hudef, ht1def]; nlinarith
  have hut0 : u < t0 * w := by rw [hudef, ht0def]; nlinarith
  -- gap exponents
  have hgap : ∀ t : Real, t < tm → q4GapExponent d gamma t < 0 := by
    intro t httm
    unfold q4GapExponent
    rw [htmdef, hAdef, lt_div_iff₀ hAg] at httm
    nlinarith
  have hout : ∀ t : Real, 0 < t →
      q4LowerWeakOutputExponent p (2 / t) = p / (t * (p - 1)) := by
    intro t htpos
    unfold q4LowerWeakOutputExponent
    field_simp
  have hinvw : ∀ t : Real, 0 < t → 1 / (t * (p - 1)) = (1 - w) / (t * w) := by
    intro t htpos
    have hx : (1 : Real) - w = 1 / p := by rw [hwdef]; ring
    have hwv : w = (p - 1) / p := by rw [hwdef]; field_simp
    rw [hx, hwv]
    field_simp
  -- the below rate at output 1 / u
  set S : Real := u * (1 / (t1 * (p - 1)) - (d : Real) + eta) with hSdef
  clear_value S u t1 t0 rho eta eps slack3 P c tm A y w
  have hq0q : q4LowerWeakOutputExponent p (2 / t0) < 1 / u := by
    rw [hout t0 ht0pos, div_lt_div_iff₀ (mul_pos ht0pos hpm) hupos]
    have hwv : w = (p - 1) / p := by rw [hwdef]; field_simp
    rw [hwv, ← mul_div_assoc, lt_div_iff₀ hp0] at hut0
    linarith
  have hqq1 : (1 : Real) / u < q4LowerWeakOutputExponent p (2 / t1) := by
    rw [hout t1 ht1pos, div_lt_div_iff₀ hupos (mul_pos ht1pos hpm)]
    have hwv : w = (p - 1) / p := by rw [hwdef]; field_simp
    rw [hwv, ← mul_div_assoc, div_lt_iff₀ hp0] at hut1
    linarith
  have hSbound : ∀ t : Real, 0 < t → t1 ≤ t →
      (2 / t) * (q4FrequencyExponentWithSubpowerLoss d t eta / 2) +
        q4LowerWeakTailExponent p (2 / t) ≤ (1 / u) * S := by
    intro t htpos ht1t
    rw [q4_lower_net_exponent_eq hp1 htpos, hSdef]
    have hqS : (1 / u) * (u * (1 / (t1 * (p - 1)) - (d : Real) + eta)) =
        1 / (t1 * (p - 1)) - (d : Real) + eta := by
      field_simp
    rw [hqS]
    have hmono : 1 / (t * (p - 1)) ≤ 1 / (t1 * (p - 1)) := by
      apply one_div_le_one_div_of_le (mul_pos ht1pos hpm)
      nlinarith
    linarith
  obtain ⟨Ccover, hCcover, hcov⟩ :=
    exists_hasSubpowerAssouadCoverBound_of_quasiAssouadDimension_eq hE hquasi hetapos
  obtain ⟨C1, hC1, hrate1⟩ :=
    exists_q4_lower_sector_explicit_dyadic_rate hd hE hEne hgamma.le hetapos.le
      hCcover.le hcov phi hphiOne hphiZero hphiNorm hphiRadial hp1 hp2
      (one_div_pos.mpr hupos)
      ht0pos ht0one ht1pos ht1one (hgap t0 ht0tm) (hgap t1 ht1tm) hq0q hqq1
      (hSbound t0 ht0pos (le_of_lt ht1t0)) (hSbound t1 ht1pos le_rfl)
  -- the above rate: the physical Q3 estimate at the dual output exponent
  have hQ3strict : p / (p - 1) < ((d - 1 : Nat) : Real) + 2 - (beta + eps) := by
    have hcast : ((d - 1 : Nat) : Real) = (d : Real) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    rw [hcast]
    have hwv : w = (p - 1) / p := by rw [hwdef]; field_simp
    have hkey : 1 < ((d : Real) + 1 - beta - eps) * w := by
      rw [hs3def] at hslack3 hepsS
      nlinarith [hwone, hwpos, hepspos]
    rw [hwv, ← mul_div_assoc, lt_div_iff₀ hp0] at hkey
    rw [div_lt_iff₀ hpm]
    linarith
  obtain ⟨C0, rho0, hC0pos, hC0, hrho0, hrho0eq, hrate0⟩ :
      ∃ C rho : ENNReal, 0 < C ∧ C < ⊤ ∧ rho < 1 ∧
        rho = ENNReal.ofReal
          (q3PhysicalMinkowskiRatio (d - 1) (beta + eps) (p / (p - 1))) ∧
        ∀ j : Nat, 1 ≤ j →
          ∀ f : SchwartzMap (Auto.Spherical.SurfaceMeasureDecay.Euclidean d) Complex,
            MemLp (fractalDyadicBandpassMaximal d E
              (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
              (ENNReal.ofReal (p / (p - 1))) volume ∧
            eLpNorm (fractalDyadicBandpassMaximal d E
              (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
              (ENNReal.ofReal (p / (p - 1))) volume ≤
              C * rho ^ j *
                eLpNorm (f : Auto.Spherical.SurfaceMeasureDecay.Euclidean d → Complex)
                  (ENNReal.ofReal p) volume := by
    rcases hd with hd3 | ⟨hd2', hgh⟩
    · obtain ⟨n, rfl⟩ : ∃ n : Nat, d = n + 1 := ⟨d - 1, by omega⟩
      have hQ3s : p / (p - 1) < ((n : Nat) : Real) + 2 - (beta + eps) := by
        simpa only [Nat.add_sub_cancel] using hQ3strict
      exact q3_physical_strict_normalized_dyadic_rate_of_upperMinkowskiDimension_eq
        (n := n) (by omega) hE hEne hMinkowski hepspos hp1 hp2 rfl hQ3s
        phi psi hphiOne hphiZero hphiNorm hpsi
    · subst hd2'
      have hQ3s : p / (p - 1) < 3 - (beta + eps) := by
        have h := hQ3strict
        norm_num at h
        linarith
      exact circle_q3_physical_strict_normalized_dyadic_rate_of_upperMinkowskiDimension_eq
        hE hEne hMinkowski hepspos hp1 hp2 rfl hQ3s
        phi psi hphiOne hphiZero hphiNorm hpsi
  have hrate0' : ∀ j : Nat, 1 ≤ j →
      ∀ f : SchwartzMap (Auto.Spherical.SurfaceMeasureDecay.Euclidean d) Complex,
        eLpNorm (fractalDyadicBandpassMaximal d E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal (p / (p - 1))) volume ≤
          C0 * rho0 ^ j *
            eLpNorm (f : Auto.Spherical.SurfaceMeasureDecay.Euclidean d → Complex)
              (ENNReal.ofReal p) volume := by
    intro j hj f
    exact (hrate0 j hj f).2
  -- interpolation weight
  set lam : Real := (y - u) / (w - u) with hlamdef
  clear_value lam
  have hwu : 0 < w - u := by linarith
  have hlam0 : 0 < lam := by rw [hlamdef]; exact div_pos (by linarith) hwu
  have hlam1 : lam < 1 := by
    rw [hlamdef, div_lt_one hwu]
    linarith
  have hexp : 1 / q = lam / (p / (p - 1)) + (1 - lam) / (1 / u) := by
    have hdual : p / (p - 1) = 1 / w := by
      rw [hwdef]
      field_simp
    have hwne : w ≠ 0 := hwpos.ne'
    have hune : u ≠ 0 := hupos.ne'
    have hwune : w - u ≠ 0 := hwu.ne'
    have hkey : lam / (1 / w) + (1 - lam) / (1 / u) = y := by
      rw [hlamdef]
      field_simp
      ring
    rw [hdual, hkey, hydef]
  -- the two explicit frequency exponents
  set e3 : Real := q3PhysicalMinkowskiExponent (d - 1) (beta + eps) (p / (p - 1))
    with he3def
  clear_value e3
  have he3val : e3 = 1 - ((d : Real) + 1 - beta - eps) * w := by
    rw [he3def]
    unfold q3PhysicalMinkowskiExponent
    have hcast : ((d - 1 : Nat) : Real) = (d : Real) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    have hdual : ((d : Real) + 1 - beta - eps) * w =
        (((d : Real) - 1) + 2 - (beta + eps)) / (p / (p - 1)) := by
      have hw : w = (p - 1) / p := by rw [hwdef]; field_simp
      rw [hw]
      field_simp
      ring
    rw [hcast, hdual]
  have he3neg : e3 < 0 := by
    rw [he3val, hs3def] at *
    nlinarith [hslack3, hepsS, hwone, hwpos]
  have hrho0val : rho0 = ENNReal.ofReal ((2 : Real) ^ e3) := by
    rw [hrho0eq, he3def]
    unfold q3PhysicalMinkowskiRatio
    rfl
  -- the arithmetic core
  have hSform : S = (1 - w) * (tm - 2 * rho) / (tm - 3 * rho) -
      (d : Real) * ((tm - 2 * rho) * w) + eta * ((tm - 2 * rho) * w) := by
    rw [hSdef, hinvw t1 ht1pos, hudef, ht1def]
    have hw0 : w ≠ 0 := hwpos.ne'
    have ht0' : tm - 3 * rho ≠ 0 := by
      have : 0 < tm - 3 * rho := by rw [ht1def] at ht1pos; linarith
      exact this.ne'
    field_simp
  have htm3 : tm / 2 ≤ tm - 3 * rho := by linarith
  have hSle : S ≤ ((1 - w) - (d : Real) * tm * w) +
      (2 * rho / tm + 2 * (d : Real) * rho + eta) := by
    rw [hSform]
    have h1 : (tm - 2 * rho) / (tm - 3 * rho) ≤ 1 + 2 * rho / tm := by
      rw [div_le_iff₀ (by linarith)]
      have hexp2 : (1 + 2 * rho / tm) * (tm - 3 * rho) =
          tm - 3 * rho + 2 * rho - 6 * rho * rho / tm := by
        field_simp
        ring
      rw [hexp2]
      have : 0 ≤ 6 * rho * rho / tm :=
        div_nonneg (by nlinarith [hrhopos]) htmpos.le
      have h6 : 6 * rho * rho / tm ≤ rho := by
        rw [div_le_iff₀ htmpos]
        nlinarith
      linarith
    have h2 : (1 - w) * ((tm - 2 * rho) / (tm - 3 * rho)) ≤
        (1 - w) * (1 + 2 * rho / tm) := by
      apply mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : (1 - w) * (1 + 2 * rho / tm) ≤ (1 - w) + 2 * rho / tm := by
      have hr : 0 ≤ 2 * rho / tm := div_nonneg (by linarith) htmpos.le
      nlinarith
    have h4 : (1 - w) * (tm - 2 * rho) / (tm - 3 * rho) =
        (1 - w) * ((tm - 2 * rho) / (tm - 3 * rho)) := by
      rw [mul_div_assoc]
    have h5 : -((d : Real) * ((tm - 2 * rho) * w)) ≤
        -((d : Real) * tm * w) + 2 * (d : Real) * rho := by
      have hkey : 0 ≤ (d : Real) * rho * (1 - w) :=
        mul_nonneg (mul_nonneg hDpos.le hrhopos.le) (by linarith)
      have : (d : Real) * ((tm - 2 * rho) * w) ≥ (d : Real) * tm * w
          - 2 * (d : Real) * rho := by
        nlinarith [hkey]
      linarith
    have h6 : eta * ((tm - 2 * rho) * w) ≤ eta := by
      have hle : (tm - 2 * rho) * w ≤ 1 := by nlinarith
      nlinarith [hetapos]
    rw [h4]
    linarith
  have hyu : y - u = (y - tm * w) + 2 * rho * w := by
    rw [hudef]; ring
  have hyutm : 0 ≤ y - tm * w := by linarith
  have htmw : 0 ≤ tm * w := (mul_pos htmpos hwpos).le
  have hstep1 : (y - u) * e3 ≤ (y - tm * w) * e3 := by
    rw [hyu]
    have h1 : 0 < 2 * rho * w := mul_pos (by linarith only [hrhopos]) hwpos
    have hneg := mul_nonneg h1.le (neg_nonneg.mpr he3neg.le)
    linarith only [hneg]
  have hstep2 : (y - tm * w) * e3 ≤
      (y - tm * w) * (1 - ((d : Real) + 1 - beta) * w) + eps := by
    rw [he3val]
    have hA2 : y - tm * w ≤ 1 := by linarith only [hyone, htmw]
    have hA3 : (0 : Real) ≤ eps * w := (mul_pos hepspos hwpos).le
    have hA4 : eps * w ≤ eps := by
      have := mul_nonneg hepspos.le (by linarith only [hwone] : (0 : Real) ≤ 1 - w)
      linarith only [this]
    have hle : (y - tm * w) * (eps * w) ≤ eps := by
      calc (y - tm * w) * (eps * w) ≤ 1 * (eps * w) :=
            mul_le_mul_of_nonneg_right hA2 hA3
        _ = eps * w := one_mul _
        _ ≤ eps := hA4
    linarith only [hle]
  have hstep3 : (w - y) * S ≤
      (w - y) * ((1 - w) - (d : Real) * tm * w) +
        (2 * rho / tm + 2 * (d : Real) * rho + eta) := by
    have hwy0 : 0 < w - y := by linarith only [hwy]
    have hwy1 : w - y ≤ 1 := by linarith only [hwone, hypos]
    have hpert : 0 ≤ 2 * rho / tm + 2 * (d : Real) * rho + eta :=
      add_nonneg (add_nonneg (div_nonneg (by linarith only [hrhopos]) htmpos.le)
        ((mul_nonneg (by linarith only [hDpos]) hrhopos.le))) hetapos.le
    have hmain := mul_le_mul_of_nonneg_left hSle hwy0.le
    have hshrink :
        (w - y) * (2 * rho / tm + 2 * (d : Real) * rho + eta) ≤
          2 * rho / tm + 2 * (d : Real) * rho + eta := by
      have := mul_nonneg (by linarith only [hwy1] : (0 : Real) ≤ 1 - (w - y)) hpert
      linarith only [this]
    linarith only [hmain, hshrink]
  have hidentP : (y - tm * w) * (1 - ((d : Real) + 1 - beta) * w) +
      (w - y) * ((1 - w) - (d : Real) * tm * w) = -P := by
    have hident := q4_lower_loss_gain_identity (d := d) (beta := beta)
      (gamma := gamma) (w := w) (y := y) hgamma (by rw [← hAdef]; exact hAg)
    rw [← hAdef, ← htmdef] at hident
    rw [hident, hPdef, hcdef, neg_div]
  have hsmall : eps + (2 * rho / tm + 2 * (d : Real) * rho + eta) < P := by
    have hden : (0 : Real) < 24 * (1 + (d : Real)) := by positivity
    have hbase : rho * (24 * (1 + (d : Real))) ≤ P * tm := by
      have h := hrhoP
      rw [le_div_iff₀ hden] at h
      exact h
    have h1 : 2 * rho / tm ≤ P / 12 := by
      rw [div_le_div_iff₀ htmpos (by norm_num)]
      have hpos : (0 : Real) ≤ 24 * rho * (d : Real) :=
        mul_nonneg (by linarith only [hrhopos]) hDpos.le
      linarith only [hbase, hpos]
    have h2 : 2 * (d : Real) * rho ≤ P / 12 := by
      rw [le_div_iff₀ (by norm_num : (0 : Real) < 12)]
      have hPtm : P * tm ≤ P := mul_le_of_le_one_right hPpos.le htmone
      have hr : (0 : Real) ≤ 24 * rho := by linarith only [hrhopos]
      linarith only [hbase, hPtm, hr]
    have h3 : eta = P / 8 := hetadef
    linarith only [hepsP, h1, h2, h3, hPpos]
  have hfinal : (y - u) * e3 + (w - y) * S < 0 := by
    linarith only [hstep1, hstep2, hstep3, hidentP, hsmall]
  -- assemble the two rates
  obtain ⟨Cfin, hfin⟩ :
      ∃ Cfin : ENNReal, Cfin < ⊤ ∧ True := ⟨(C0 ^ lam * C1 ^ (1 - lam)), by
        exact ⟨ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg hlam0.le hC0.ne)
          (ENNReal.rpow_lt_top_of_nonneg (by linarith) hC1.ne), trivial⟩⟩
  have hratio : (rho0 ^ lam * (ENNReal.ofReal ((2 : Real) ^ S)) ^ (1 - lam)) < 1 := by
    rw [hrho0val, ofReal_two_rpow_rpow e3 lam, ofReal_two_rpow_rpow S (1 - lam),
      ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by norm_num)]
    refine ENNReal.ofReal_lt_one.mpr ?_
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    have hwu' : 0 < w - u := hwu
    have hwune : w - u ≠ 0 := hwu.ne'
    have hlamval : e3 * lam + S * (1 - lam) =
        ((y - u) * e3 + (w - y) * S) / (w - u) := by
      rw [hlamdef]
      field_simp
      ring
    rw [hlamval]
    exact div_neg_of_neg_of_pos hfinal hwu'
  have hinterp := memLp_and_eLpNorm_schwartz_of_weighted_output_dyadic_rates
    (d := d)
    (fun j g => fractalDyadicBandpassMaximal d E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) g)
    (fun j g => (measurable_fractalDyadicBandpassMaximal E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) g).aestronglyMeasurable)
    (p := p) (q0 := p / (p - 1)) (q := q) (q1 := 1 / u) (lam := lam)
    (by positivity) (by positivity) hq0 hlam0 hlam1 hexp
    hC0 hC1 (lt_of_lt_of_le hrho0 le_top) ENNReal.ofReal_lt_top
    hrate0' (fun j hj f => (hrate1 j hj f).2)
  exact ⟨_, _,
    ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hlam0.le hC0.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by linarith) hC1.ne),
    hratio, hinterp⟩

set_option maxHeartbeats 1000000 in
theorem q4_interior_band_rate_of_conjugate_output
    {d : Nat} {E : Set Real} {beta gamma p q : Real}
    (hd : 3 ≤ d ∨ d = 2 ∧ gamma ≤ 1 / 2)
    (hE : E ⊆ Icc (1 : Real) 2) (hEne : E.Nonempty)
    (hMinkowski : upperMinkowskiDimension E = beta)
    (hp1 : 1 < p) (hp2 : p < 2) (hpq : p < q)
    (hqeq : q = p / (p - 1))
    (hQ3 : q < (d : Real) + 1 - beta)
    (phi psi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean d, ‖phi xi‖ ≤ 1)
    (hphiRadial : IsNormRadial (phi : Euclidean d → Complex))
    (hpsi : ∀ eta : Euclidean d, psi eta =
      phi (((2 : Real) ^ (0 + 1))⁻¹ • eta) - phi (((2 : Real) ^ 0)⁻¹ • eta)) :
    HasAbsoluteBandRate E phi hphiOne hphiZero p q := by
  have hd2 : 2 ≤ d := by rcases hd with h | ⟨h, -⟩ <;> omega
  have hq1 : (1 : Real) ≤ q := by linarith
  set eps : Real := ((d : Real) + 1 - beta - q) / 2 with hepsdef
  have hepspos : 0 < eps := by rw [hepsdef]; linarith
  have hstrict : q < ((d - 1 : Nat) : Real) + 2 - (beta + eps) := by
    have hcast : ((d - 1 : Nat) : Real) = (d : Real) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    rw [hcast, hepsdef]
    linarith
  obtain ⟨C, rho, hCpos, hCtop, hrho, hrhoeq, hrate⟩ :
      ∃ C rho : ENNReal, 0 < C ∧ C < ⊤ ∧ rho < 1 ∧
        rho = ENNReal.ofReal
          (q3PhysicalMinkowskiRatio (d - 1) (beta + eps) q) ∧
        ∀ j : Nat, 1 ≤ j →
          ∀ f : SchwartzMap (Auto.Spherical.SurfaceMeasureDecay.Euclidean d) Complex,
            MemLp (fractalDyadicBandpassMaximal d E
              (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
              (ENNReal.ofReal q) volume ∧
            eLpNorm (fractalDyadicBandpassMaximal d E
              (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
              (ENNReal.ofReal q) volume ≤
              C * rho ^ j *
                eLpNorm (f : Auto.Spherical.SurfaceMeasureDecay.Euclidean d → Complex)
                  (ENNReal.ofReal p) volume := by
    rcases hd with hd3 | ⟨hd2', hgh⟩
    · obtain ⟨n, rfl⟩ : ∃ n : Nat, d = n + 1 := ⟨d - 1, by omega⟩
      have hs : q < ((n : Nat) : Real) + 2 - (beta + eps) := by
        simpa only [Nat.add_sub_cancel] using hstrict
      exact q3_physical_strict_normalized_dyadic_rate_of_upperMinkowskiDimension_eq
        (n := n) (by omega) hE hEne hMinkowski hepspos hp1 hp2 hqeq hs
        phi psi hphiOne hphiZero hphiNorm hpsi
    · subst hd2'
      have hs : q < 3 - (beta + eps) := by
        have h := hstrict
        norm_num at h
        linarith
      exact circle_q3_physical_strict_normalized_dyadic_rate_of_upperMinkowskiDimension_eq
        hE hEne hMinkowski hepspos hp1 hp2 hqeq hs
        phi psi hphiOne hphiZero hphiNorm hpsi
  exact ⟨C, rho, hCtop, hrho, hrate⟩

/-! ### The empty radius set -/

theorem hasAbsoluteBandRate_empty {d : Nat} (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0) (p q : Real) :
    HasAbsoluteBandRate (∅ : Set Real) phi hphiOne hphiZero p q := by
  refine ⟨1, 1 / 2, by norm_num, by norm_num, fun j hj f => ?_⟩
  have hzero : fractalDyadicBandpassMaximal d (∅ : Set Real)
      (absoluteDyadicBandpass phi hphiOne hphiZero j) f = fun _ => 0 := by
    funext x
    rw [fractalDyadicBandpassMaximal, fractalSphericalMaximalReal,
      fractalSphericalMaximal_empty]
    simp
  rw [hzero]
  refine ⟨?_, ?_⟩
  · exact ⟨aestronglyMeasurable_const, by simp⟩
  · simp

/-! ### The band-rate dispatcher for the repository skeleton -/

set_option maxHeartbeats 1000000 in
theorem band_rate_of_mem_interior_Q_of_skeleton
    {d : ℕ} {β γ p q : ℝ}
    (hd : 3 ≤ d ∨ d = 2 ∧ γ ≤ 1 / 2)
    (E : Set ℝ) (hE : E ⊆ Icc (1 : ℝ) 2)
    (hβγ : 0 ≤ β ∧ β ≤ γ ∧ γ ≤ 1)
    (hMinkowski : upperMinkowskiDimension E = β)
    (hquasiAssouad : quasiAssouadDimension E = γ)
    (hp : 0 < p) (hq : 1 ≤ q)
    (hregion : reciprocalExponentPoint p q ∈ interior (Q d β γ))
    (phi psi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean d, ‖phi xi‖ ≤ 1)
    (hphiRadial : IsNormRadial (phi : Euclidean d → Complex))
    (hpsi : ∀ eta : Euclidean d, psi eta =
      phi (((2 : Real) ^ (0 + 1))⁻¹ • eta) - phi (((2 : Real) ^ 0)⁻¹ • eta)) :
    HasAbsoluteBandRate E phi hphiOne hphiZero p q := by
  rcases Set.eq_empty_or_nonempty E with rfl | hEne
  · exact hasAbsoluteBandRate_empty phi hphiOne hphiZero p q
  obtain ⟨hbeta, hbeta_gamma, hgamma_one⟩ := hβγ
  have hgamma : (0 : Real) ≤ γ := hbeta.trans hbeta_gamma
  have hbeta_one : β ≤ 1 := hbeta_gamma.trans hgamma_one
  have hd2 : 2 ≤ d := by rcases hd with h | ⟨h, -⟩ <;> omega
  have hD : (2 : Real) ≤ (d : Real) := by exact_mod_cast hd2
  have hp1 : 1 < p :=
    one_lt_inputExponent_of_mem_interior_Q hd2 hbeta hbeta_one hbeta_gamma hp
      hregion
  have hpq : p < q :=
    inputExponent_lt_outputExponent_of_mem_interior_Q hd2 hbeta_one hgamma hp hq
      hregion
  have hq0 : (0 : Real) < q := by linarith
  have hpm : (0 : Real) < p - 1 := by linarith
  have hw : (0 : Real) < 1 - 1 / p := by
    rw [sub_pos, div_lt_one hp]
    linarith
  have hcrit : β < ((d : Real) - 1) * (p - 1) :=
    minkowski_critical_of_mem_interior_Q hd2 hbeta hbeta_one hbeta_gamma
      hgamma_one hp hregion
  have hcap : q < (d : Real) * p := by
    have h := strict_first_lt_natCast_mul_second_of_mem_interior_Q
      (x := reciprocalExponentPoint p q) hd2 hbeta hbeta_one hgamma hregion
    change p⁻¹ < (d : Real) * q⁻¹ at h
    have hpqpos : (0 : Real) < p * q := mul_pos hp hq0
    have h2 := mul_lt_mul_of_pos_right h hpqpos
    rw [show p⁻¹ * (p * q) = q by field_simp,
      show (d : Real) * q⁻¹ * (p * q) = (d : Real) * p by field_simp] at h2
    exact h2
  have hannulus :
      (d : Real) * (1 / p) < (1 - β) * (1 / q) + ((d : Real) - 1) := by
    have h := strict_annulus_of_mem_interior_Q
      (x := reciprocalExponentPoint p q) hd2 hbeta hbeta_gamma hbeta_one hregion
    change (d : Real) * p⁻¹ < (1 - β) * q⁻¹ + ((d : Real) - 1) at h
    simpa only [one_div] using h
  have hcluster : 0 < clusterEdgeFunctional d (β / γ) β (1 / p, 1 / q) := by
    have h := strict_clusterEdgeFunctional_of_mem_interior_Q
      (x := reciprocalExponentPoint p q) hd2 hbeta hbeta_one hbeta_gamma hregion
    simpa only [reciprocalExponentPoint, one_div] using h
  by_cases hp2 : 2 ≤ p
  · exact q4_interior_band_rate_of_two_le_input hd hE hEne hbeta hgamma
      hgamma_one hbeta_gamma hMinkowski hquasiAssouad hp2 hpq hcap hcrit phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi
  push_neg at hp2
  rcases lt_trichotomy q (p / (p - 1)) with hlt | heq | hgt
  · exact q4_interior_band_rate_of_sum_gt_one hd hE hEne hbeta hMinkowski
      hp1 hp2 hpq hlt hannulus hcrit phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi
  · have hxq : 1 / q = 1 - 1 / p := by
      rw [heq]
      field_simp
    have hxbound : (1 / p) * ((d : Real) + 1 - β) < (d : Real) - β := by
      rw [hxq] at hannulus
      nlinarith [hannulus]
    have hQ3 : q < (d : Real) + 1 - β := by
      have hval : q = 1 / (1 - 1 / p) := by
        have h1 : (1 : Real) - 1 / p = (p - 1) / p := by field_simp
        rw [h1, one_div_div, heq]
      rw [hval, div_lt_iff₀ hw]
      nlinarith [hxbound]
    exact q4_interior_band_rate_of_conjugate_output (gamma := γ) hd hE hEne
      hMinkowski hp1 hp2 hpq heq hQ3 phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi
  · by_cases hslope :
        p / (q * (p - 1)) <
          (((d : Real) - 1) / 2) / ((((d : Real) - 1) / 2) + γ)
    · exact q4_interior_band_rate_of_strict_lower_sector hd hE hEne hgamma
        hquasiAssouad hbeta hbeta_gamma hgamma_one hp1 hp2 hpq hcap hslope phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi
    · push_neg at hslope
      have hApos : (0 : Real) < ((d : Real) - 1) / 2 := by linarith
      have hAg : (0 : Real) < ((d : Real) - 1) / 2 + γ := by linarith
      have hratio : p / (q * (p - 1)) = (1 / q) / (1 - 1 / p) := by
        field_simp
      rw [hratio] at hslope
      have hbalance :
          (((d : Real) - 1) / 2) / ((((d : Real) - 1) / 2) + γ) *
            (1 - 1 / p) ≤ 1 / q := (le_div_iff₀ hw).mp hslope
      have hywlt : 1 / q < 1 - 1 / p := by
        have h1 : (1 : Real) - 1 / p = (p - 1) / p := by field_simp
        rw [h1, div_lt_div_iff₀ hq0 hp]
        have h2 : p < q * (p - 1) := (div_lt_iff₀ hpm).mp hgt
        linarith
      have htmone :
          (((d : Real) - 1) / 2) / ((((d : Real) - 1) / 2) + γ) < 1 := by
        have hlt :
            (((d : Real) - 1) / 2) / ((((d : Real) - 1) / 2) + γ) *
              (1 - 1 / p) < 1 * (1 - 1 / p) := by
          rw [one_mul]
          exact lt_of_le_of_lt hbalance hywlt
        exact lt_of_mul_lt_mul_right hlt hw.le
      have hgammapos : (0 : Real) < γ := by
        rw [div_lt_one hAg] at htmone
        linarith
      have hxbound : (1 / p) * ((d : Real) + 1 - β) < (d : Real) - β := by
        have hle : (1 - β) * (1 / q) ≤ (1 - β) * (1 - 1 / p) :=
          mul_le_mul_of_nonneg_left hywlt.le (by linarith)
        nlinarith [hannulus, hle]
      have hQ3 : p / (p - 1) < (d : Real) + 1 - β := by
        have hval : p / (p - 1) = 1 / (1 - 1 / p) := by
          have h1 : (1 : Real) - 1 / p = (p - 1) / p := by field_simp
          rw [h1, one_div_div]
        rw [hval, div_lt_iff₀ hw]
        nlinarith [hxbound]
      exact q4_interior_band_rate_of_loss_gain hd hE hEne hbeta hgammapos
        hgamma_one hMinkowski hquasiAssouad hp1 hp2 hpq hgt hQ3 hbalance hcluster phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi

/-! ### From the planar dyadic rate to the band rate -/

theorem hasAbsoluteBandRate_of_hasDyRate
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (phi : SchwartzMap Pl ℂ)
    (hphiOne : ∀ xi : Pl, ‖xi‖ ≤ 1 → (phi : Pl → ℂ) xi = 1)
    (hphiZero : ∀ xi : Pl, 2 ≤ ‖xi‖ → (phi : Pl → ℂ) xi = 0)
    (hphiNorm : ∀ xi : Pl, ‖(phi : Pl → ℂ) xi‖ ≤ 1)
    {a b : ℝ} (hbpos : 0 < b) (hba : b < a) (ha1 : a < 1) (hb1 : b ≤ 1)
    (hrate : HasDyRate (E := E) phi hphiOne hphiZero a b) :
    HasAbsoluteBandRate E phi hphiOne hphiZero (1 / a) (1 / b) := by
  obtain ⟨C, rho, hC, hrho, hrho1, hbound⟩ := hrate
  have hapos : 0 < a := lt_trans hbpos hba
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal rho, ENNReal.ofReal_lt_top, ?_, ?_⟩
  · rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hrho1
  intro j hj f
  have h := hbound j hj f
  have hconv : ENNReal.ofReal (C * rho ^ j)
      = ENNReal.ofReal C * ENNReal.ofReal rho ^ j := by
    rw [ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_pow hrho.le]
  rw [hconv] at h
  refine ⟨?_, h⟩
  refine ⟨(measurable_fractalDyadicBandpassMaximal E
    (absoluteDyadicBandpass phi hphiOne hphiZero j) f).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt h ?_
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))
    (f.memLp (ENNReal.ofReal (1 / a)) volume).2

/-! ### The planar band rate above the conjugate line -/

theorem bandRate_planar_sum_ge_one
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (hMink : upperMinkowskiDimension E = beta)
    {a b : ℝ} (hbpos : 0 < b) (hba : b < a) (ha1 : a < 1) (hsum : 1 ≤ a + b)
    (hann : 2 * a < (1 - beta) * b + 1)
    (phi psi : SchwartzMap Pl ℂ)
    (hphiOne : ∀ xi : Pl, ‖xi‖ ≤ 1 → (phi : Pl → ℂ) xi = 1)
    (hphiZero : ∀ xi : Pl, 2 ≤ ‖xi‖ → (phi : Pl → ℂ) xi = 0)
    (hphiNorm : ∀ xi : Pl, ‖(phi : Pl → ℂ) xi‖ ≤ 1)
    (hphiRadial : IsNormRadial (phi : Pl → ℂ))
    (hpsi : ∀ eta : Pl, psi eta =
      phi (((2 : ℝ) ^ (0 + 1))⁻¹ • eta) - phi (((2 : ℝ) ^ 0)⁻¹ • eta)) :
    HasAbsoluteBandRate E phi hphiOne hphiZero (1 / a) (1 / b) := by
  have hapos : 0 < a := lt_trans hbpos hba
  have hahalf : 1 / 2 < a := by linarith
  have hone_a : (0 : ℝ) < 1 - a := by linarith
  have hp1 : (1 : ℝ) < 1 / a := by
    rw [lt_div_iff₀ hapos]
    linarith
  have hp2 : (1 : ℝ) / a < 2 := by
    rw [div_lt_iff₀ hapos]
    linarith
  have hpq : (1 : ℝ) / a < 1 / b := one_div_lt_one_div_of_lt hbpos hba
  have hcrit : beta < 1 / a - 1 := by
    have h2 : (1 : ℝ) + beta < 1 / a := by
      rw [lt_div_iff₀ hapos]
      nlinarith
    linarith
  have hne : (1 : ℝ) / a - 1 ≠ 0 := by
    have h : (0:ℝ) < 1 / a - 1 := by linarith
    exact h.ne'
  have hconj : (1 : ℝ) / a / (1 / a - 1) = 1 / (1 - a) := by
    have hane : a ≠ 0 := hapos.ne'
    have h1 : (1 : ℝ) - a ≠ 0 := hone_a.ne'
    rw [div_eq_div_iff hne h1]
    field_simp
  rcases lt_or_eq_of_le hsum with hgt | heq
  · refine q4_interior_band_rate_of_sum_gt_one (d := 2) (gamma := 0)
      (Or.inr ⟨rfl, by norm_num⟩) hE hEne hbeta hMink hp1 hp2 hpq ?_ ?_ ?_ phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi
    · rw [hconj]
      exact one_div_lt_one_div_of_lt hone_a (by linarith)
    · push_cast
      rw [one_div_one_div, one_div_one_div]
      nlinarith [hann]
    · push_cast
      linarith [hcrit]
  · have hb : b = 1 - a := by linarith
    refine q4_interior_band_rate_of_conjugate_output (d := 2) (gamma := 0) (beta := beta)
      (Or.inr ⟨rfl, by norm_num⟩) hE hEne hMink hp1 hp2 hpq ?_ ?_ phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi
    · rw [hconj, hb]
    · have hbgt : 1 / (3 - beta) < b := by
        rw [div_lt_iff₀ (by linarith : (0:ℝ) < 3 - beta)]
        nlinarith [hann]
      have hqlt : (1 : ℝ) / b < 3 - beta := by
        rw [div_lt_iff₀ hbpos]
        rw [div_lt_iff₀ (by linarith : (0:ℝ) < 3 - beta)] at hbgt
        nlinarith [hbgt]
      push_cast
      linarith [hqlt]

/-! ### The planar band rate in the interior -/

set_option maxHeartbeats 1000000 in
theorem bandRate_planar_interior
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) {beta gam p q : ℝ}
    (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1) (hbg : beta ≤ gam) (hgam2 : gam ≤ 1)
    (hMink : upperMinkowskiDimension E = beta) (hquasi : quasiAssouadDimension E = gam)
    (hgam1 : 1 / 2 < gam) (hp : 0 < p) (hq : 1 ≤ q)
    (hdiagall : ∀ (φ : SchwartzMap Pl ℂ)
      (hφone : ∀ ξ : Pl, ‖ξ‖ ≤ 1 → (φ : Pl → ℂ) ξ = 1)
      (hφzero : ∀ ξ : Pl, 2 ≤ ‖ξ‖ → (φ : Pl → ℂ) ξ = 0),
      (∀ ξ : Pl, ‖(φ : Pl → ℂ) ξ‖ ≤ 1) → HasDiagGains (E := E) φ hφone hφzero beta)
    (hregion : reciprocalExponentPoint p q ∈ interior (Q 2 beta gam))
    (phi psi : SchwartzMap Pl ℂ)
    (hphiOne : ∀ xi : Pl, ‖xi‖ ≤ 1 → (phi : Pl → ℂ) xi = 1)
    (hphiZero : ∀ xi : Pl, 2 ≤ ‖xi‖ → (phi : Pl → ℂ) xi = 0)
    (hphiNorm : ∀ xi : Pl, ‖(phi : Pl → ℂ) xi‖ ≤ 1)
    (hphiRadial : IsNormRadial (phi : Pl → ℂ))
    (hpsi : ∀ eta : Pl, psi eta =
      phi (((2 : ℝ) ^ (0 + 1))⁻¹ • eta) - phi (((2 : ℝ) ^ 0)⁻¹ • eta)) :
    HasAbsoluteBandRate E phi hphiOne hphiZero p q := by
  rcases Set.eq_empty_or_nonempty E with rfl | hEne
  · exact hasAbsoluteBandRate_empty phi hphiOne hphiZero p q
  have hgamnn : (0 : ℝ) ≤ gam := by linarith
  have htrans := strict_second_lt_first_of_mem_interior_Q (d := 2) (by omega) hbeta1 hgamnn
    hregion
  have hcap := strict_first_lt_natCast_mul_second_of_mem_interior_Q (d := 2) (by omega) hbeta
    hbeta1 hgamnn hregion
  have hannraw := strict_annulus_of_mem_interior_Q (d := 2) (by omega) hbeta hbg hbeta1 hregion
  have hcluraw := strict_clusterEdgeFunctional_of_mem_interior_Q (d := 2) (by omega) hbeta
    hbeta1 hbg hregion
  have ha1raw := strict_first_lt_one_of_mem_interior_Q (d := 2) (by omega) hbeta hbeta1 hbg
    hregion
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set a : ℝ := p⁻¹ with hadef
  set b : ℝ := q⁻¹ with hbdef
  have hbpos : 0 < b := by rw [hbdef]; positivity
  have hb1 : b ≤ 1 := by
    rw [hbdef, inv_le_one_iff₀]
    right
    exact hq
  have hba : b < a := htrans
  have hab : a < 2 * b := by
    have h : a < ((2:ℕ):ℝ) * b := hcap
    push_cast at h
    exact h
  have hann : 2 * a < (1 - beta) * b + 1 := by
    have h : ((2:ℕ):ℝ) * a < (1 - beta) * b + (((2:ℕ):ℝ) - 1) := hannraw
    push_cast at h
    linarith
  have hclu : 0 < beta / gam / 2 + (2 - beta - beta / gam / 2) * b
      - (1 + beta / gam / 2) * a := by
    have h : 0 < Auto.Spherical.FractalDilations.Auxiliary.clusterEdgeFunctional
        2 (beta / gam) beta (a, b) := hcluraw
    rw [Auto.Spherical.FractalDilations.Auxiliary.clusterEdgeFunctional] at h
    push_cast at h
    have hform : beta / gam / 2 * ((2 : ℝ) - 1)
        + ((2 : ℝ) - beta - ((2 : ℝ) - 1) * (beta / gam) / 2) * b
        - (1 + beta / gam / 2 * ((2 : ℝ) - 1)) * a
        = beta / gam / 2 + (2 - beta - beta / gam / 2) * b
          - (1 + beta / gam / 2) * a := by ring
    linarith [h]
  have ha1 : a < 1 := ha1raw
  have hpa : (1 : ℝ) / a = p := by
    rw [hadef, one_div, inv_inv]
  have hqb : (1 : ℝ) / b = q := by
    rw [hbdef, one_div, inv_inv]
  rcases lt_or_ge (a + b) 1 with hsum | hsum
  · have hrate := exists_rate_interior hE hEne hbeta hbeta1 hbg hMink hquasi hgam1 hgam2
      phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi
      (hdiagall phi hphiOne hphiZero hphiNorm)
      hbpos hba hab hsum hann hclu
    have h := hasAbsoluteBandRate_of_hasDyRate hE phi hphiOne hphiZero hphiNorm hbpos hba
      ha1 hb1 hrate
    rw [hpa, hqb] at h
    exact h
  · have h := bandRate_planar_sum_ge_one hE hEne hbeta hMink hbpos hba ha1 hsum hann
      phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi
    rw [hpa, hqb] at h
    exact h

/-! ### The planar band rate, assembled -/

theorem bandRate_planar
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) {beta gam p q : ℝ}
    (hbeta : 0 ≤ beta) (hbg : beta ≤ gam) (hgam2 : gam ≤ 1)
    (hMink : upperMinkowskiDimension E = beta) (hquasi : quasiAssouadDimension E = gam)
    (hgam1 : 1 / 2 < gam) (hp : 0 < p) (hq : 1 ≤ q)
    (hregion : reciprocalExponentPoint p q ∈ interior (Q 2 beta gam))
    (phi psi : SchwartzMap Pl ℂ)
    (hphiOne : ∀ xi : Pl, ‖xi‖ ≤ 1 → (phi : Pl → ℂ) xi = 1)
    (hphiZero : ∀ xi : Pl, 2 ≤ ‖xi‖ → (phi : Pl → ℂ) xi = 0)
    (hphiNorm : ∀ xi : Pl, ‖(phi : Pl → ℂ) xi‖ ≤ 1)
    (hphiRadial : IsNormRadial (phi : Pl → ℂ))
    (hpsi : ∀ eta : Pl, psi eta =
      phi (((2 : ℝ) ^ (0 + 1))⁻¹ • eta) - phi (((2 : ℝ) ^ 0)⁻¹ • eta)) :
    HasAbsoluteBandRate E phi hphiOne hphiZero p q := by
  have hbeta1 : beta ≤ 1 := by
    have h := upperMinkowskiDimension_le_one_of_subset_Icc hE
    simpa only [hMink] using h
  refine bandRate_planar_interior hE hbeta hbeta1 hbg hgam2 hMink hquasi hgam1 hp hq
      ?_ hregion phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi
  intro φ hφone hφzero hφnorm
  rcases lt_or_eq_of_le hbeta1 with hlt | heq
  · rcases Set.eq_empty_or_nonempty E with rfl | hEne
    · intro s hs hsbeta
      refine ⟨1, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      intro j hj f
      have hzero : Mdy (E := (∅ : Set ℝ)) φ hφone hφzero j f = 0 := by
        funext x
        simp [Mdy, fractalDyadicBandpassMaximal, fractalSphericalMaximalReal,
          fractalSphericalMaximal]
      rw [hzero]
      simp
    · obtain ⟨psi, hpsi⟩ : ∃ psi : SchwartzMap Pl ℂ, ∀ ξ : Pl,
          psi ξ = φ (((2 : ℝ) ^ (0 + 1))⁻¹ • ξ) - φ (((2 : ℝ) ^ 0)⁻¹ • ξ) :=
        Auto.Spherical.Auxiliary.exists_schwartzMap_smooth_dyadic_bandpass φ 0
      exact hasDiagGains_of_beta_lt_one hE hEne hbeta hlt hMink φ psi hφone hφzero
        hφnorm hpsi
  · rw [heq]
    exact rs_hasDiagGains_one hE φ hφone hφzero

/-! ### The band rate at every interior point, in every dimension -/

theorem bandRate_of_mem_interior_Q
    {d : ℕ} {beta gam p q : ℝ} (hd : 2 ≤ d)
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2)
    (hbeta : 0 ≤ beta) (hbg : beta ≤ gam) (hgam : gam ≤ 1)
    (hMink : upperMinkowskiDimension E = beta) (hquasi : quasiAssouadDimension E = gam)
    (hp : 0 < p) (hq : 1 ≤ q)
    (phi psi : SchwartzMap (Euclidean d) ℂ)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean d, ‖phi xi‖ ≤ 1)
    (hphiRadial : IsNormRadial (phi : Euclidean d → ℂ))
    (hpsi : ∀ eta : Euclidean d, psi eta =
      phi (((2 : ℝ) ^ (0 + 1))⁻¹ • eta) - phi (((2 : ℝ) ^ 0)⁻¹ • eta))
    (hregion : reciprocalExponentPoint p q ∈ interior (Q d beta gam)) :
    HasAbsoluteBandRate E phi hphiOne hphiZero p q := by
  by_cases hd3 : 3 ≤ d
  · exact band_rate_of_mem_interior_Q_of_skeleton (Or.inl hd3) E hE ⟨hbeta, hbg, hgam⟩
      hMink hquasi hp hq hregion phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi
  · have hd2 : d = 2 := by omega
    subst hd2
    by_cases hg : gam ≤ 1 / 2
    · exact band_rate_of_mem_interior_Q_of_skeleton (Or.inr ⟨rfl, hg⟩) E hE
        ⟨hbeta, hbg, hgam⟩ hMink hquasi hp hq hregion phi psi hphiOne hphiZero hphiNorm
        hphiRadial hpsi
    · exact bandRate_planar hE hbeta hbg hgam hMink hquasi (not_le.mp hg) hp hq hregion
        phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi

/-! ### Comparison of the two dimensions -/

theorem quasiAssouadDimension_le_one (E : Set ℝ) :
    quasiAssouadDimension E ≤ 1 := by
  rw [quasiAssouadDimension]
  refine csSup_le ⟨upperAssouadSpectrum E 0, ⟨0, ⟨le_refl (0:ℝ), zero_lt_one⟩, rfl⟩⟩ ?_
  rintro x ⟨θ, hθ, rfl⟩
  exact upperAssouadSpectrum_le_one E (le_of_lt hθ.2)

/-- **Upper Minkowski dimension is at most quasi-Assouad dimension.**  Both are computed from
the same covering numbers, and the spectrum at parameter zero is the Minkowski dimension. -/
theorem upperMinkowskiDimension_le_quasiAssouadDimension {E : Set ℝ}
    (hE : E ⊆ Icc (1 : ℝ) 2) :
    upperMinkowskiDimension E ≤ quasiAssouadDimension E := by
  refine (upperMinkowskiDimension_le_upperAssouadSpectrum_zero hE).trans ?_
  rw [quasiAssouadDimension]
  refine le_csSup ⟨1, ?_⟩ ⟨0, ⟨le_refl (0:ℝ), zero_lt_one⟩, rfl⟩
  rintro x ⟨θ, hθ, rfl⟩
  exact upperAssouadSpectrum_le_one E (le_of_lt hθ.2)

/-! ### Theorem 1.2(i), the necessary conditions -/

/-- **The closure of a type set is a closed convex set squeezed between two regions.**  This is
the "only if" direction of Theorem 1.2(i): the pair `(β,γ)` is the pair of dimensions of `E`. -/
theorem isClosed_convex_sandwich_closure_fractalTypeSet {d : ℕ} (hd : 2 ≤ d)
    {E : Set ℝ} (hE : E ⊆ Icc (1 : ℝ) 2) (hEne : E.Nonempty) :
    IsClosed (closure (fractalTypeSet d E)) ∧ Convex ℝ (closure (fractalTypeSet d E)) ∧
      ∃ beta gam : ℝ, 0 ≤ beta ∧ beta ≤ gam ∧ gam ≤ 1 ∧
        Q d beta gam ⊆ closure (fractalTypeSet d E) ∧
        closure (fractalTypeSet d E) ⊆ Q d beta beta := by
  refine ⟨isClosed_closure, convex_closure_fractalTypeSet hd hE hEne, ?_⟩
  refine ⟨upperMinkowskiDimension E, quasiAssouadDimension E,
    upperMinkowskiDimension_nonneg_of_subset_Icc hE,
    upperMinkowskiDimension_le_quasiAssouadDimension hE,
    quasiAssouadDimension_le_one E, ?_, ?_⟩
  · exact Q_subset_closure_fractalTypeSet hd hE
      (upperMinkowskiDimension_nonneg_of_subset_Icc hE)
      (upperMinkowskiDimension_le_quasiAssouadDimension hE)
      (quasiAssouadDimension_le_one E) rfl rfl
  · refine closure_minimal ?_ (isClosed_Q d _ _)
    exact fractalTypeSet_subset_Q_self hd hE hEne
      (upperMinkowskiDimension_nonneg_of_subset_Icc hE)
      (upperMinkowskiDimension_le_one_of_subset_Icc hE) rfl

open MeasureTheory Set ENNReal Metric FourierTransform
open scoped FourierTransform
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds

/-! ### Radius sets inside a single band cell -/

/-- A set inside an interval of length at most `δ` is covered by the single interval of length
`δ` centred at the midpoint. -/
theorem oneCell_isIntervalCover {E : Set ℝ} {a b δ : ℝ}
    (hE : E ⊆ Icc a b) (hlen : b - a ≤ δ) :
    IsIntervalCover E δ {(a + b) / 2} := by
  intro x hx
  obtain ⟨hxa, hxb⟩ := hE hx
  refine Set.mem_iUnion₂.mpr ⟨(a + b) / 2, Finset.mem_singleton_self _, ?_, ?_⟩
  · linarith
  · linarith

/-- The `L¹` and `L²` endpoint estimates for one band cell: a radius set confined to an interval
of length `2^{-j}` behaves at frequency `2^j` like a single radius. -/
theorem exists_oneCell_dyadic_endpoints {n : ℕ} (hn : 2 ≤ n)
    (phi psi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphiOne : ∀ xi : Euclidean (n + 1), ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean (n + 1), 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean (n + 1), ‖phi xi‖ ≤ 1)
    (hpsi : ∀ xi : Euclidean (n + 1),
      psi xi = phi (((2 : ℝ) ^ (0 + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ 0)⁻¹ • xi)) :
    ∃ B1 B2 : ℝ, 0 ≤ B1 ∧ 0 ≤ B2 ∧
      ∀ (j : ℕ), 1 ≤ j → ∀ {E : Set ℝ}, E ⊆ Icc (1 : ℝ) 2 → E.Nonempty →
        ∀ {a b : ℝ}, E ⊆ Icc a b → b - a ≤ ((2 : ℝ) ^ j)⁻¹ →
        ∀ f : SchwartzMap (Euclidean (n + 1)) ℂ,
          (MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f) 1 volume ∧
            (∫ x : Euclidean (n + 1),
              ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
                (absoluteDyadicBandpass phi hphiOne hphiZero j) f x‖)
              ≤ B1 * ∫ x : Euclidean (n + 1), ‖f x‖) ∧
          (MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f) 2 volume ∧
            (∫ x : Euclidean (n + 1),
              ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
                (absoluteDyadicBandpass phi hphiOne hphiZero j) f x‖ ^ (2 : ℕ))
              ≤ (B2 * ((2 : ℝ) ^ j) ^ (-(n : ℝ)))
                * ∫ x : Euclidean (n + 1), ‖f x‖ ^ (2 : ℕ)) := by
  obtain ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩ := exists_sharp_surfaceFourier_succ_decay_and_deriv hn
  refine ⟨surfaceMass (n + 1) *
      ((∫ x : Euclidean (n + 1), ‖(𝓕⁻ psi : SchwartzMap (Euclidean (n + 1)) ℂ) x‖) +
        ∫ x : Euclidean (n + 1),
          ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean (n + 1)) ℂ) :
            Euclidean (n + 1) → ℂ) x‖),
    8 * C0 ^ 2 + 8 * C1 ^ 2, ?_, by positivity, ?_⟩
  · have hmass : 0 ≤ surfaceMass (n + 1) := le_of_lt (surfaceMass_pos (Nat.succ_pos n))
    have h1 : 0 ≤ ∫ x : Euclidean (n + 1), ‖(𝓕⁻ psi : SchwartzMap (Euclidean (n + 1)) ℂ) x‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ x : Euclidean (n + 1),
        ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean (n + 1)) ℂ) :
          Euclidean (n + 1) → ℂ) x‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  intro j hj E hE hEne a b hEab hlen f
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hRone : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hδpos : (0 : ℝ) < ((2 : ℝ) ^ j)⁻¹ := by positivity
  have hδone : ((2 : ℝ) ^ j)⁻¹ < 1 := by
    rw [inv_lt_one₀ hRpos]
    calc (1 : ℝ) < 2 := by norm_num
      _ = (2 : ℝ) ^ (1 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hcover : IsIntervalCover E (((2 : ℝ) ^ j)⁻¹) {(a + b) / 2} :=
    oneCell_isIntervalCover hEab hlen
  have hcard : (({(a + b) / 2} : Finset ℝ).card : ℝ) ≤ 1 * (((2 : ℝ) ^ j)⁻¹) ^ (-(0 : ℝ)) := by
    simp
  have hmain := absolute_dyadic_minkowski_endpoints_of_cover hn C0 C1 hC0 hC1 hdecay hderiv
    hE hEne hRpos hRone hδpos hδone (le_refl _) {(a + b) / 2} hcover hcard
    phi f psi (absoluteDyadicBandpass phi hphiOne hphiZero j) hphiOne hphiZero hphiNorm j
    (absoluteDyadicBandpass_spec phi hphiOne hphiZero j)
    (absoluteDyadicBandpass_compact phi hphiOne hphiZero j)
    rfl
    (by
      intro xi
      simpa only [Auto.Spherical.SurfaceMeasureDecay.dyadicScale] using
        smooth_dyadic_bandpass_eq_scaled_base phi psi
          (absoluteDyadicBandpass phi hphiOne hphiZero j) hpsi j
          (absoluteDyadicBandpass_spec phi hphiOne hphiZero j) xi)
  obtain ⟨hm1, hb1, hm2, hb2⟩ := hmain
  refine ⟨⟨hm1, ?_⟩, ⟨hm2, ?_⟩⟩
  · refine hb1.trans (le_of_eq ?_)
    norm_num
  · refine hb2.trans (le_of_eq ?_)
    norm_num

open MeasureTheory Set ENNReal Metric FourierTransform
open scoped FourierTransform
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary



/-- The `L¹` and `L²` endpoint estimates for one band cell in the plane. -/
theorem exists_oneCell_dyadic_endpoints_circle
    (phi psi : SchwartzMap (Euclidean 2) ℂ)
    (hphiOne : ∀ xi : Euclidean 2, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean 2, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean 2, ‖phi xi‖ ≤ 1)
    (hpsi : ∀ xi : Euclidean 2,
      psi xi = phi (((2 : ℝ) ^ (0 + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ 0)⁻¹ • xi)) :
    ∃ B1 B2 : ℝ, 0 ≤ B1 ∧ 0 ≤ B2 ∧
      ∀ (j : ℕ), 1 ≤ j → ∀ {E : Set ℝ}, E ⊆ Icc (1 : ℝ) 2 → E.Nonempty →
        ∀ {a b : ℝ}, E ⊆ Icc a b → b - a ≤ ((2 : ℝ) ^ j)⁻¹ →
        ∀ f : SchwartzMap (Euclidean 2) ℂ,
          (MemLp (unnormalizedFractalDyadicBandpassMaximal 2 E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f) 1 volume ∧
            (∫ x : Euclidean 2,
              ‖unnormalizedFractalDyadicBandpassMaximal 2 E
                (absoluteDyadicBandpass phi hphiOne hphiZero j) f x‖)
              ≤ B1 * ∫ x : Euclidean 2, ‖f x‖) ∧
          (MemLp (unnormalizedFractalDyadicBandpassMaximal 2 E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f) 2 volume ∧
            (∫ x : Euclidean 2,
              ‖unnormalizedFractalDyadicBandpassMaximal 2 E
                (absoluteDyadicBandpass phi hphiOne hphiZero j) f x‖ ^ (2 : ℕ))
              ≤ (B2 * ((2 : ℝ) ^ j) ^ (-(1 : ℝ)))
                * ∫ x : Euclidean 2, ‖f x‖ ^ (2 : ℕ)) := by
  obtain ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩ := exists_sharp_surfaceFourier_two_decay_and_deriv
  refine ⟨surfaceMass 2 *
      ((∫ x : Euclidean 2, ‖(𝓕⁻ psi : SchwartzMap (Euclidean 2) ℂ) x‖) +
        ∫ x : Euclidean 2,
          ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean 2) ℂ) : Euclidean 2 → ℂ) x‖),
    8 * C0 ^ 2 + 32 * C1 ^ 2, ?_, by positivity, ?_⟩
  · have hmass : 0 ≤ surfaceMass 2 := le_of_lt (surfaceMass_pos (by norm_num))
    have h1 : 0 ≤ ∫ x : Euclidean 2, ‖(𝓕⁻ psi : SchwartzMap (Euclidean 2) ℂ) x‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ x : Euclidean 2,
        ‖fderiv ℝ ((𝓕⁻ psi : SchwartzMap (Euclidean 2) ℂ) : Euclidean 2 → ℂ) x‖ :=
      integral_nonneg fun _ => norm_nonneg _
    positivity
  intro j hj E hE hEne a b hEab hlen f
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hRone : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hδpos : (0 : ℝ) < ((2 : ℝ) ^ j)⁻¹ := by positivity
  have hδone : ((2 : ℝ) ^ j)⁻¹ < 1 := by
    rw [inv_lt_one₀ hRpos]
    calc (1 : ℝ) < 2 := by norm_num
      _ = (2 : ℝ) ^ (1 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hcover : IsIntervalCover E (((2 : ℝ) ^ j)⁻¹) {(a + b) / 2} :=
    oneCell_isIntervalCover hEab hlen
  have hcard : (({(a + b) / 2} : Finset ℝ).card : ℝ) ≤ 1 * (((2 : ℝ) ^ j)⁻¹) ^ (-(0 : ℝ)) := by
    simp
  have hlocal := absolute_dyadic_minkowski_endpoints_of_cover_of_local_l2
    (n := 1) (by norm_num) hE hEne hRpos hRone hδpos hδone (le_refl _)
    {(a + b) / 2} hcover hcard psi f (absoluteDyadicBandpass phi hphiOne hphiZero j)
    (by
      intro xi
      simpa only [Auto.Spherical.SurfaceMeasureDecay.dyadicScale] using
        smooth_dyadic_bandpass_eq_scaled_base phi psi
          (absoluteDyadicBandpass phi hphiOne hphiZero j) hpsi j
          (absoluteDyadicBandpass_spec phi hphiOne hphiZero j) xi)
    (B2 := 8 * C0 ^ 2 + 32 * C1 ^ 2) (by positivity)
    (by
      intro u v huv huvinterval hlenuv
      rcases sphericalIntervalMaximalRaw_memLp_two_of_circle_sharp
          C0 C1 hC0 hC1 hdecay hderiv phi f
          (absoluteDyadicBandpass phi hphiOne hphiZero j)
          hphiOne hphiZero hphiNorm j
          (absoluteDyadicBandpass_spec phi hphiOne hphiZero j)
          (absoluteDyadicBandpass_compact phi hphiOne hphiZero j)
          huv huvinterval with ⟨hmem, hbound⟩
      refine ⟨hmem, hbound.trans ?_⟩
      apply mul_le_mul_of_nonneg_right
        (by
          simpa only [Nat.cast_one, Auto.Spherical.SurfaceMeasureDecay.dyadicScale] using
            circle_short_interval_l2_coefficient_le_frequency_decay
              C0 C1 hC0.le hC1.le hRpos hRone (sub_nonneg.mpr huv) hlenuv)
        (integral_nonneg fun _ => sq_nonneg _))
  obtain ⟨hm1, hb1, hm2, hb2⟩ := hlocal
  refine ⟨⟨hm1, ?_⟩, ⟨hm2, ?_⟩⟩
  · refine hb1.trans (le_of_eq ?_)
    norm_num
  · refine hb2.trans (le_of_eq ?_)
    norm_num

open MeasureTheory Set ENNReal Metric FourierTransform
open scoped FourierTransform
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-! ### Band rates that are uniform over the radius sets inside one band cell -/

/-- A geometric band rate valid, with one and the same constant, for every radius set confined
to an interval of length `2^{-j}`.  This is the estimate the union construction of §7 needs for
the tail of the family, which at frequency `2^j` is contained in a single cell. -/
def HasOneCellBandRate {d : ℕ} (phi : SchwartzMap (Euclidean d) ℂ)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0) (p q : ℝ) : Prop :=
  ∃ C rho : ℝ≥0∞, C < ⊤ ∧ rho < 1 ∧ ∀ (j : ℕ), 1 ≤ j → ∀ {E : Set ℝ}, E ⊆ Icc (1 : ℝ) 2 →
    E.Nonempty → ∀ {a b : ℝ}, E ⊆ Icc a b → b - a ≤ ((2 : ℝ) ^ j)⁻¹ →
    ∀ f : SchwartzMap (Euclidean d) ℂ,
      eLpNorm (fractalDyadicBandpassMaximal d E (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal q) volume
        ≤ (C * rho ^ j) * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume

/-- Monotonicity of the dyadic band maximal operator in the radius set. -/
theorem fractalDyadicBandpassMaximal_mono {d : ℕ} (hd : 0 < d) {E F : Set ℝ} (hEF : E ⊆ F)
    (hF : F ⊆ Ioi (0 : ℝ)) (psi f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    fractalDyadicBandpassMaximal d E psi f x ≤ fractalDyadicBandpassMaximal d F psi f x := by
  unfold fractalDyadicBandpassMaximal
  exact fractalSphericalMaximalReal_mono hd hEF hF _ x

/-- **The crossed one-cell band rate.**  On the conjugate line the physical `L¹ → L∞` endpoint
and the one-cell `L²` estimate interpolate to a geometric rate, uniformly over all radius sets
inside one band cell. -/
theorem oneCell_crossed_bandRate {n : ℕ}
    (phi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphiOne : ∀ xi : Euclidean (n + 1), ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean (n + 1), 2 ≤ ‖xi‖ → phi xi = 0)
    {B2 : ℝ} (hB2 : 0 ≤ B2)
    (hl2 : ∀ (j : ℕ), 1 ≤ j → ∀ {E : Set ℝ}, E ⊆ Icc (1 : ℝ) 2 → E.Nonempty →
      ∀ {a b : ℝ}, E ⊆ Icc a b → b - a ≤ ((2 : ℝ) ^ j)⁻¹ →
      ∀ f : SchwartzMap (Euclidean (n + 1)) ℂ,
        MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f) 2 volume ∧
        (∫ x : Euclidean (n + 1),
          ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f x‖ ^ (2 : ℕ))
          ≤ (B2 * ((2 : ℝ) ^ j) ^ (-(n : ℝ)))
            * ∫ x : Euclidean (n + 1), ‖f x‖ ^ (2 : ℕ))
    {p q : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hq : q = p / (p - 1))
    (hstrict : q < (n : ℝ) + 2) :
    HasOneCellBandRate phi hphiOne hphiZero p q := by
  have hdpos : 0 < n + 1 := Nat.succ_pos n
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hqpos : 0 < q := by
    rw [hq]
    exact div_pos hp0 (by linarith)
  have hqtwo : 2 < q := by
    rw [hq]
    have hpminus : 0 < p - 1 := by linarith
    apply (lt_div_iff₀ hpminus).mpr
    nlinarith
  -- the physical `L¹ → L∞` endpoint on the whole radius interval
  obtain ⟨D, hD, hphysical⟩ := exists_absoluteDyadicBandpass_lone_linf_endpoint
    (d := n + 1) hdpos (Icc (1 : ℝ) 2) (subset_refl _) phi hphiOne hphiZero
  set A0 : ℝ := surfaceMass (n + 1) * D with hA0def
  have hA0 : 0 < A0 := by
    rw [hA0def]
    exact mul_pos (surfaceMass_pos hdpos) hD
  set rho : ℝ≥0∞ :=
    ENNReal.ofReal ((2 : ℝ) ^ q3PhysicalMinkowskiExponent n 0 q) with hrhodef
  have hrho : rho < 1 := by
    rw [hrhodef]
    refine ENNReal.ofReal_lt_one.mpr ?_
    have h := q3PhysicalMinkowskiRatio_mem_Ioo (n := n) (a := 0) (q := q) hqpos (by simpa using hstrict)
    simpa only [q3PhysicalMinkowskiRatio] using h.2
  set CT : ℝ≥0∞ := ENNReal.ofReal ((surfaceMass (n + 1))⁻¹) *
    (q3PhysicalCrossedConstant A0 B2 q) ^ q⁻¹ with hCTdef
  have hcrossTop : q3PhysicalCrossedConstant A0 B2 q < ⊤ := by
    unfold q3PhysicalCrossedConstant
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) ?_
    refine ENNReal.mul_lt_top ?_ ?_
    · exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (by linarith : 0 < q - 2))
    · exact ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  have hCTtop : CT < ⊤ := by
    rw [hCTdef]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr hqpos.le) hcrossTop.ne)
  refine ⟨CT, rho, hCTtop, hrho, ?_⟩
  intro j hj E hE hEne a b hEab hlen f
  set R : ℝ := (2 : ℝ) ^ j with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  -- the endpoint on `E`, by monotonicity in the radius set
  have hendpoint : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ, ∀ x : Euclidean (n + 1),
      fractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g x
        ≤ D * R * ∫ y : Euclidean (n + 1), ‖(g : Euclidean (n + 1) → ℂ) y‖ := by
    intro g x
    refine le_trans (fractalDyadicBandpassMaximal_mono hdpos hE
      (fun t ht => lt_of_lt_of_le zero_lt_one ht.1) _ g x) ?_
    rw [hRdef]
    exact hphysical j g x
  have hBscale : 0 ≤ B2 * R ^ (0 - (n : ℝ)) :=
    mul_nonneg hB2 (Real.rpow_nonneg hR.le _)
  have hl2' : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g) 2 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) g x‖ ^ (2 : ℕ))
        ≤ (B2 * R ^ (0 - (n : ℝ))) * ∫ x : Euclidean (n + 1), ‖g x‖ ^ (2 : ℕ) := by
    intro g
    obtain ⟨hmem, hbd⟩ := hl2 j hj hE hEne hEab hlen g
    refine ⟨hmem, hbd.trans (le_of_eq ?_)⟩
    congr 2
    rw [hRdef, zero_sub]
  have hpiece := q3_rational_schwartz_crossed_eLpNorm_of_physical_lone_ltwo_homogeneous
    (n := n) (E := E) (R := R) (D := D) (B := B2 * R ^ (0 - (n : ℝ)))
    hE hR hD hBscale phi hphiOne hphiZero hendpoint hl2' hp1 hp2 hq f
  have hscale := q3PhysicalCrossedConstant_rpow_scale
    (n := n) (A := A0) (B := B2) (R := R) (a := 0) (q := q) hA0 hB2 hR hqtwo
  have hRrate : (ENNReal.ofReal R) ^ q3PhysicalMinkowskiExponent n 0 q = rho ^ j := by
    rw [hrhodef, hRdef]
    calc (ENNReal.ofReal ((2 : ℝ) ^ j)) ^ q3PhysicalMinkowskiExponent n 0 q
        = ENNReal.ofReal (((2 : ℝ) ^ j) ^ q3PhysicalMinkowskiExponent n 0 q) :=
          ENNReal.ofReal_rpow_of_pos (pow_pos (by norm_num : (0:ℝ) < 2) j)
      _ = ENNReal.ofReal (((2 : ℝ) ^ q3PhysicalMinkowskiExponent n 0 q) ^ j) := by
          congr 1
          calc ((2 : ℝ) ^ j) ^ q3PhysicalMinkowskiExponent n 0 q
              = (2 : ℝ) ^ ((j : ℝ) * q3PhysicalMinkowskiExponent n 0 q) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
            _ = (2 : ℝ) ^ (q3PhysicalMinkowskiExponent n 0 q * (j : ℝ)) := by
                congr 1
                ring
            _ = ((2 : ℝ) ^ q3PhysicalMinkowskiExponent n 0 q) ^ j :=
                Real.rpow_mul_natCast (by norm_num) _ _
      _ = (ENNReal.ofReal ((2 : ℝ) ^ q3PhysicalMinkowskiExponent n 0 q)) ^ j := by
          rw [ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _)]
  -- assemble
  have hstep : eLpNorm (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume
      ≤ (q3PhysicalCrossedConstant (A0 * R) (B2 * R ^ (0 - (n : ℝ))) q) ^ q⁻¹ *
        eLpNorm ((f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p) volume := by
    simpa only [hA0def, mul_assoc] using hpiece
  rw [hscale, hRrate] at hstep
  have hunnorm : eLpNorm (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume
      ≤ ((q3PhysicalCrossedConstant A0 B2 q) ^ q⁻¹) * rho ^ j *
        eLpNorm ((f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p) volume := hstep
  have hnorm := fractalDyadicBandpass_eLpNorm_le_of_unnormalized_rate (d := n + 1) hdpos hunnorm
  refine hnorm.trans (le_of_eq ?_)
  rw [hCTdef]

open MeasureTheory Set ENNReal Metric FourierTransform
open scoped FourierTransform
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-- A real-constant form of the one-cell band rate. -/
def HasOneCellBandRateReal {d : ℕ} (phi : SchwartzMap (Euclidean d) ℂ)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0) (p q : ℝ) : Prop :=
  ∃ C rho : ℝ, 0 < C ∧ 0 < rho ∧ rho < 1 ∧ ∀ (j : ℕ), 1 ≤ j → ∀ {E : Set ℝ},
    E ⊆ Icc (1 : ℝ) 2 → E.Nonempty → ∀ {a b : ℝ}, E ⊆ Icc a b → b - a ≤ ((2 : ℝ) ^ j)⁻¹ →
    ∀ f : SchwartzMap (Euclidean d) ℂ,
      eLpNorm (fractalDyadicBandpassMaximal d E (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal q) volume
        ≤ ENNReal.ofReal (C * rho ^ j) * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume

theorem hasOneCellBandRateReal_of_hasOneCellBandRate {d : ℕ}
    {phi : SchwartzMap (Euclidean d) ℂ}
    {hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1}
    {hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0} {p q : ℝ}
    (h : HasOneCellBandRate phi hphiOne hphiZero p q) :
    HasOneCellBandRateReal phi hphiOne hphiZero p q := by
  obtain ⟨C, rho, hCtop, hrho, hbound⟩ := h
  obtain ⟨C', rho', hC', hrho', hrho1', hconv⟩ := exists_real_rate_of_ennreal hCtop hrho
  refine ⟨C', rho', hC', hrho', hrho1', ?_⟩
  intro j hj E hE hEne a b hEab hlen f
  exact (hbound j hj hE hEne hEab hlen f).trans
    (mul_le_mul' (hconv j) (le_refl _))

/-! ### The diagonal one-cell rate below `L²` -/

/-- **The diagonal one-cell band rate for `1 < p < 2`.**  The one-cell `L¹` and `L²` endpoints
interpolate to a geometric `L^p → L^p` rate, uniformly over all radius sets inside a cell. -/
theorem oneCell_diagonal_bandRate {n : ℕ} (hn : 0 < n)
    (phi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphiOne : ∀ xi : Euclidean (n + 1), ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean (n + 1), 2 ≤ ‖xi‖ → phi xi = 0)
    {B1 B2 : ℝ} (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hend : ∀ (j : ℕ), 1 ≤ j → ∀ {E : Set ℝ}, E ⊆ Icc (1 : ℝ) 2 → E.Nonempty →
      ∀ {a b : ℝ}, E ⊆ Icc a b → b - a ≤ ((2 : ℝ) ^ j)⁻¹ →
      ∀ f : SchwartzMap (Euclidean (n + 1)) ℂ,
        (MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f) 1 volume ∧
          (∫ x : Euclidean (n + 1),
            ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
              (absoluteDyadicBandpass phi hphiOne hphiZero j) f x‖)
            ≤ B1 * ∫ x : Euclidean (n + 1), ‖f x‖) ∧
        (MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f) 2 volume ∧
          (∫ x : Euclidean (n + 1),
            ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
              (absoluteDyadicBandpass phi hphiOne hphiZero j) f x‖ ^ (2 : ℕ))
            ≤ (B2 * ((2 : ℝ) ^ j) ^ (-(n : ℝ)))
              * ∫ x : Euclidean (n + 1), ‖f x‖ ^ (2 : ℕ)))
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    HasOneCellBandRateReal phi hphiOne hphiZero p p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hmass : 0 < surfaceMass (n + 1) := surfaceMass_pos (Nat.succ_pos n)
  set a1 : ℝ := (p - 1)⁻¹ + (3 - p)⁻¹ with ha1def
  set a2 : ℝ := ((1 : ℝ) / 4) * p⁻¹ + (2 - p)⁻¹ with ha2def
  set A : ℝ := ((surfaceMass (n + 1))⁻¹) ^ p * (p * (4 * (1 * B2) * a2 + 2 * (1 * B1) * a1))
    with hAdef
  have ha1 : 0 < a1 := by
    rw [ha1def]
    have h1 : 0 < (p - 1)⁻¹ := by positivity
    have h2 : 0 < (3 - p)⁻¹ := by
      apply inv_pos.mpr
      linarith
    linarith
  have ha2 : 0 < a2 := by
    rw [ha2def]
    have h1 : 0 < ((1 : ℝ) / 4) * p⁻¹ := by positivity
    have h2 : 0 < (2 - p)⁻¹ := by
      apply inv_pos.mpr
      linarith
    linarith
  have hA : 0 ≤ A := by
    rw [hAdef]
    have h1 : 0 ≤ ((surfaceMass (n + 1))⁻¹) ^ p :=
      Real.rpow_nonneg (inv_nonneg.mpr hmass.le) _
    have h2 : 0 ≤ p * (4 * (1 * B2) * a2 + 2 * (1 * B1) * a1) := by
      have : 0 ≤ 4 * (1 * B2) * a2 + 2 * (1 * B1) * a1 := by
        have hx : 0 ≤ 4 * (1 * B2) * a2 := by positivity
        have hy : 0 ≤ 2 * (1 * B1) * a1 := by positivity
        linarith
      positivity
    positivity
  set eps : ℝ := (n : ℝ) * (p - 1) with hepsdef
  have heps : 0 < eps := by
    rw [hepsdef]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have : 0 < p - 1 := by linarith
    positivity
  refine ⟨(A + 1) ^ p⁻¹, (2 : ℝ) ^ (-eps / p), by positivity, by positivity, ?_, ?_⟩
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by
        apply div_neg_of_neg_of_pos _ hp0
        linarith)
  intro j hj E hE hEne a b hEab hlen f
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hEpos : E ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le zero_lt_one (hE ht).1
  -- the endpoints in the shape required by the interpolation lemma
  have hendpoints : ∀ g : SchwartzMap (Euclidean (n + 1)) ℂ,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g) 1 volume ∧
        (∫ x : Euclidean (n + 1),
          ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) g x‖)
          ≤ (1 * (((2 : ℝ) ^ j)⁻¹) ^ (-(0 : ℝ))) * B1
            * ∫ x : Euclidean (n + 1), ‖g x‖ ∧
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g) 2 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) g x‖ ^ (2 : ℕ))
        ≤ (1 * (((2 : ℝ) ^ j)⁻¹) ^ (-(0 : ℝ))) * (B2 * ((2 : ℝ) ^ j) ^ (-(n : ℝ)))
          * ∫ x : Euclidean (n + 1), ‖g x‖ ^ (2 : ℕ) := by
    intro g
    obtain ⟨⟨hm1, hb1⟩, ⟨hm2, hb2⟩⟩ := hend j hj hE hEne hEab hlen g
    refine ⟨hm1, ?_, hm2, ?_⟩
    · refine hb1.trans (le_of_eq ?_)
      norm_num
    · refine hb2.trans (le_of_eq ?_)
      norm_num
  have hmoment := normalized_absolute_minkowski_moment_of_cover_endpoints_of_pos
    (n := n) (E := E) (R := (2 : ℝ) ^ j) (δ := (((2 : ℝ) ^ j)⁻¹)) (α := 0) (C := 1) (D := 1)
    (B₁ := B1) (B₂ := B2) (p := p) hn hRpos (le_refl _) (by norm_num) hB1 hB2 hp1 hp2
    (by norm_num) (absoluteDyadicBandpass phi hphiOne hphiZero j) hEpos hendpoints f
  obtain ⟨hmemp, hmomentbd⟩ := hmoment
  -- rewrite the frequency power as a geometric factor
  have hpow : ((2 : ℝ) ^ j) ^ ((0 : ℝ) + (n : ℝ) - (n : ℝ) * p) = (2 : ℝ) ^ (-eps * (j : ℝ)) := by
    rw [hepsdef, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have hI : 0 ≤ ∫ x : Euclidean (n + 1), ‖f x‖ ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hmoment' : (∫ x : Euclidean (n + 1),
      (fractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f x) ^ p)
      ≤ A * (2 : ℝ) ^ (-eps * (j : ℝ)) * ∫ x : Euclidean (n + 1), ‖f x‖ ^ p := by
    refine hmomentbd.trans (le_of_eq ?_)
    rw [hAdef, hpow]
  have hnormbd := absolute_eLpNorm_le_of_bandpass_real_moment_bound
    (d := n + 1) (p := p) (A := A) (ε := eps) (I := ∫ x : Euclidean (n + 1), ‖f x‖ ^ p)
    hp0 (fractalDyadicBandpassMaximal (n + 1) E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) f) hmemp
    (fun x => fractalDyadicBandpassMaximal_nonneg E _ f x) hA hI j hmoment'
  -- identify the input norm
  have hinput : ENNReal.ofReal ((∫ x : Euclidean (n + 1), ‖f x‖ ^ p) ^ p⁻¹)
      = eLpNorm ((f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p) volume := by
    have h := eLpNorm_schwartz_eq_sameOutputInputScale (d := n + 1) (p := p)
      (I := ∫ x : Euclidean (n + 1), ‖f x‖ ^ p) hp0 f rfl
    rw [h, sameOutputInputScale]
  have hApow : A ^ p⁻¹ ≤ (A + 1) ^ p⁻¹ :=
    Real.rpow_le_rpow hA (by linarith) (by positivity)
  refine hnormbd.trans ?_
  calc (ENNReal.ofReal (A ^ p⁻¹) *
        ENNReal.ofReal ((∫ x : Euclidean (n + 1), ‖f x‖ ^ p) ^ p⁻¹)) *
        ENNReal.ofReal ((2 : ℝ) ^ (-eps / p)) ^ j
      = ENNReal.ofReal (A ^ p⁻¹ * ((2 : ℝ) ^ (-eps / p)) ^ j) *
          ENNReal.ofReal ((∫ x : Euclidean (n + 1), ‖f x‖ ^ p) ^ p⁻¹) := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ A ^ p⁻¹),
          ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (2 : ℝ) ^ (-eps / p))]
        ring
    _ ≤ ENNReal.ofReal ((A + 1) ^ p⁻¹ * ((2 : ℝ) ^ (-eps / p)) ^ j) *
          eLpNorm ((f : Euclidean (n + 1) → ℂ)) (ENNReal.ofReal p) volume := by
        rw [hinput]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hApow (by positivity))) (le_refl _)

open MeasureTheory Set ENNReal Metric FourierTransform
open scoped FourierTransform
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-! ### Upgrading a one-cell diagonal rate through the `L∞` endpoint -/

/-- **The diagonal one-cell band rate above a given exponent.**  The uniform `L∞` bound of the
band operator upgrades a diagonal one-cell rate at `r` to every exponent `s > r`. -/
theorem oneCell_diagonal_bandRate_above {d : ℕ} (hd : 0 < d)
    (phi : SchwartzMap (Euclidean d) ℂ)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hrate : HasOneCellBandRateReal phi hphiOne hphiZero r r) :
    HasOneCellBandRateReal phi hphiOne hphiZero s s := by
  obtain ⟨c, rho, hc, hrho, hrho1, hbound⟩ := hrate
  set L : ℝ := absoluteDyadicBandpassLInfinityConstant phi hphiOne hphiZero + 1 with hLdef
  have hK : 0 ≤ absoluteDyadicBandpassLInfinityConstant phi hphiOne hphiZero :=
    absoluteDyadicBandpassLInfinityConstant_nonneg phi hphiOne hphiZero
  have hL : 0 < L := by rw [hLdef]; linarith
  refine ⟨q2TopDyadicRateConstant r s c L, q2TopDyadicRateRatio r s rho,
    q2TopDyadicRateConstant_pos hr hrs hc hL,
    (q2TopDyadicRateRatio_mem_Ioo hr hrs hrho hrho1).1,
    (q2TopDyadicRateRatio_mem_Ioo hr hrs hrho hrho1).2, ?_⟩
  intro j hj E hE hEne a b hEab hlen f
  have hEpos : E ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le zero_lt_one (hE ht).1
  set T : SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
    fun g => fractalDyadicBandpassMaximal d E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) g with hTdef
  have hTmeas : ∀ g : SchwartzMap (Euclidean d) ℂ, AEStronglyMeasurable (T g) volume := by
    intro g
    rw [hTdef]
    exact (measurable_fractalDyadicBandpassMaximal E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) g).aestronglyMeasurable
  have hTnonneg : ∀ (g : SchwartzMap (Euclidean d) ℂ) x, 0 ≤ T g x := by
    intro g x
    rw [hTdef]
    exact fractalDyadicBandpassMaximal_nonneg E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) g x
  have hTsub : ∀ (g h : SchwartzMap (Euclidean d) ℂ) x, T (g + h) x ≤ T g x + T h x := by
    intro g h x
    rw [hTdef]
    exact fractalDyadicBandpassMaximal_add_le hd E hEpos
      (absoluteDyadicBandpass phi hphiOne hphiZero j) g h x
  have hcj : 0 < c * rho ^ j := mul_pos hc (pow_pos hrho j)
  have hstrong : ∀ g : SchwartzMap (Euclidean d) ℂ,
      MemLp (T g) (ENNReal.ofReal r) volume ∧
      eLpNorm (T g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal (c * rho ^ j) *
          eLpNorm ((g : Euclidean d → ℂ)) (ENNReal.ofReal r) volume := by
    intro g
    have hbd := hbound j hj hE hEne hEab hlen g
    refine ⟨⟨hTmeas g, ?_⟩, hbd⟩
    refine lt_of_le_of_lt hbd ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr (eLpNorm_schwartz_ne_top hr g))
  have htop : ∀ (g : SchwartzMap (Euclidean d) ℂ) (u : ℝ), 0 ≤ u →
      (∀ x, ‖g x‖ ≤ u) → ∀ x, T g x ≤ L * u := by
    intro g u hu hgu x
    have hbase := fractalDyadicBandpassMaximal_absoluteDyadicBandpass_le_of_uniform_norm
      hd E hE phi hphiOne hphiZero j g hgu x
    calc T g x ≤ absoluteDyadicBandpassLInfinityConstant phi hphiOne hphiZero * u := hbase
      _ ≤ L * u := by
        refine mul_le_mul_of_nonneg_right ?_ hu
        rw [hLdef]
        linarith
  have hhigh := schwartz_operator_strong_above_of_diagonal_top_with_constant
    T hr hrs hcj hL hTmeas hTnonneg hTsub hstrong htop f
  have hcoefficient := q2TopDyadicRateCoefficient_eq hr hrs hc hrho hL j
  refine hhigh.2.trans (le_of_eq ?_)
  rw [hcoefficient]

open MeasureTheory Set ENNReal Metric FourierTransform
open scoped FourierTransform
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-- The one-cell `L¹` and `L²` endpoints in every dimension `n + 1 ≥ 2`. -/
theorem exists_oneCell_dyadic_endpoints_all {n : ℕ} (hn : 1 ≤ n)
    (phi psi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphiOne : ∀ xi : Euclidean (n + 1), ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean (n + 1), 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean (n + 1), ‖phi xi‖ ≤ 1)
    (hpsi : ∀ xi : Euclidean (n + 1),
      psi xi = phi (((2 : ℝ) ^ (0 + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ 0)⁻¹ • xi)) :
    ∃ B1 B2 : ℝ, 0 ≤ B1 ∧ 0 ≤ B2 ∧
      ∀ (j : ℕ), 1 ≤ j → ∀ {E : Set ℝ}, E ⊆ Icc (1 : ℝ) 2 → E.Nonempty →
        ∀ {a b : ℝ}, E ⊆ Icc a b → b - a ≤ ((2 : ℝ) ^ j)⁻¹ →
        ∀ f : SchwartzMap (Euclidean (n + 1)) ℂ,
          (MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f) 1 volume ∧
            (∫ x : Euclidean (n + 1),
              ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
                (absoluteDyadicBandpass phi hphiOne hphiZero j) f x‖)
              ≤ B1 * ∫ x : Euclidean (n + 1), ‖f x‖) ∧
          (MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f) 2 volume ∧
            (∫ x : Euclidean (n + 1),
              ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
                (absoluteDyadicBandpass phi hphiOne hphiZero j) f x‖ ^ (2 : ℕ))
              ≤ (B2 * ((2 : ℝ) ^ j) ^ (-(n : ℝ)))
                * ∫ x : Euclidean (n + 1), ‖f x‖ ^ (2 : ℕ)) := by
  rcases eq_or_lt_of_le hn with hn1 | hn2
  · -- the plane
    have hn1' : n = 1 := hn1.symm
    subst hn1'
    have h := exists_oneCell_dyadic_endpoints_circle phi psi hphiOne hphiZero hphiNorm hpsi
    obtain ⟨B1, B2, hB1, hB2, hmain⟩ := h
    refine ⟨B1, B2, hB1, hB2, ?_⟩
    intro j hj E hE hEne a b hEab hlen f
    simpa only [Nat.cast_one] using hmain j hj hE hEne hEab hlen f
  · -- the higher-dimensional case
    exact exists_oneCell_dyadic_endpoints (by omega) phi psi hphiOne hphiZero hphiNorm hpsi

open MeasureTheory Set ENNReal Metric FourierTransform
open scoped FourierTransform
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-! ### The amplitude-scale data of a collinear triple of exponent pairs -/

/-- From the reciprocal collinearity of three exponent pairs with increasing input and output
exponents one reads off the strict orderings and the amplitude-scale exponent `m` of the
two-pair interpolation. -/
theorem exists_twoPair_data_of_reciprocal {p0 q0 p1 q1 p q lam : ℝ}
    (hp0 : 0 < p0) (hp1 : 0 < p1) (hq0 : 0 < q0) (hq1 : 0 < q1)
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hpa : p⁻¹ = (1 - lam) * p0⁻¹ + lam * p1⁻¹)
    (hqb : q⁻¹ = (1 - lam) * q0⁻¹ + lam * q1⁻¹)
    (hp01 : p0 < p1) (hq01 : q0 < q1) :
    0 < p ∧ 0 < q ∧ p0 < p ∧ p < p1 ∧ q0 < q ∧ q < q1 ∧
      ∃ m : ℝ, 0 < m ∧ q - q0 = m * (p - p0) * (q0 / p0) ∧
        q - q1 = m * (p - p1) * (q1 / p1) ∧
        (q0 / p0) * ((q1 - q) / (q1 - q0)) + (q1 / p1) * ((q - q0) / (q1 - q0)) = q / p := by
  have hlam1' : 0 < 1 - lam := by linarith
  have hpinv : 0 < p⁻¹ := by
    rw [hpa]
    exact add_pos (mul_pos hlam1' (inv_pos.mpr hp0)) (mul_pos hlam0 (inv_pos.mpr hp1))
  have hp : 0 < p := inv_pos.mp hpinv
  have hqinv : 0 < q⁻¹ := by
    rw [hqb]
    exact add_pos (mul_pos hlam1' (inv_pos.mpr hq0)) (mul_pos hlam0 (inv_pos.mpr hq1))
  have hq : 0 < q := inv_pos.mp hqinv
  have hpne : p ≠ 0 := ne_of_gt hp
  have hqne : q ≠ 0 := ne_of_gt hq
  have hp0ne : p0 ≠ 0 := ne_of_gt hp0
  have hp1ne : p1 ≠ 0 := ne_of_gt hp1
  have hq0ne : q0 ≠ 0 := ne_of_gt hq0
  have hq1ne : q1 ≠ 0 := ne_of_gt hq1
  set Da : ℝ := p0⁻¹ - p1⁻¹ with hDadef
  set Db : ℝ := q0⁻¹ - q1⁻¹ with hDbdef
  have hDapos : 0 < Da := by
    rw [hDadef]
    have hinv : p1⁻¹ < p0⁻¹ := (inv_lt_inv₀ hp1 hp0).mpr hp01
    linarith
  have hDbpos : 0 < Db := by
    rw [hDbdef]
    have hinv : q1⁻¹ < q0⁻¹ := (inv_lt_inv₀ hq1 hq0).mpr hq01
    linarith
  have hDane : Da ≠ 0 := ne_of_gt hDapos
  have hDbne : Db ≠ 0 := ne_of_gt hDbpos
  have hdp0 : p - p0 = p * p0 * (lam * Da) := by
    have hstep : p0⁻¹ - p⁻¹ = lam * Da := by rw [hpa, hDadef]; ring
    have hbase : p - p0 = p * p0 * (p0⁻¹ - p⁻¹) := by field_simp
    rw [hbase, hstep]
  have hdp1 : p - p1 = -(p * p1 * ((1 - lam) * Da)) := by
    have hstep : p1⁻¹ - p⁻¹ = -((1 - lam) * Da) := by rw [hpa, hDadef]; ring
    have hbase : p - p1 = p * p1 * (p1⁻¹ - p⁻¹) := by field_simp
    rw [hbase, hstep]
    ring
  have hdq0 : q - q0 = q * q0 * (lam * Db) := by
    have hstep : q0⁻¹ - q⁻¹ = lam * Db := by rw [hqb, hDbdef]; ring
    have hbase : q - q0 = q * q0 * (q0⁻¹ - q⁻¹) := by field_simp
    rw [hbase, hstep]
  have hdq1 : q - q1 = -(q * q1 * ((1 - lam) * Db)) := by
    have hstep : q1⁻¹ - q⁻¹ = -((1 - lam) * Db) := by rw [hqb, hDbdef]; ring
    have hbase : q - q1 = q * q1 * (q1⁻¹ - q⁻¹) := by field_simp
    rw [hbase, hstep]
    ring
  have hp0p : p0 < p := by
    have hpos : 0 < p * p0 * (lam * Da) :=
      mul_pos (mul_pos hp hp0) (mul_pos hlam0 hDapos)
    linarith [hdp0]
  have hpp1 : p < p1 := by
    have hpos : 0 < p * p1 * ((1 - lam) * Da) :=
      mul_pos (mul_pos hp hp1) (mul_pos hlam1' hDapos)
    linarith [hdp1]
  have hq0q : q0 < q := by
    have hpos : 0 < q * q0 * (lam * Db) :=
      mul_pos (mul_pos hq hq0) (mul_pos hlam0 hDbpos)
    linarith [hdq0]
  have hqq1 : q < q1 := by
    have hpos : 0 < q * q1 * ((1 - lam) * Db) :=
      mul_pos (mul_pos hq hq1) (mul_pos hlam1' hDbpos)
    linarith [hdq1]
  refine ⟨hp, hq, hp0p, hpp1, hq0q, hqq1, (q / p) * (Db / Da),
    mul_pos (div_pos hq hp) (div_pos hDbpos hDapos), ?_, ?_, ?_⟩
  · rw [hdq0, hdp0]
    field_simp
  · rw [hdq1, hdp1]
    field_simp
  · have hq10 : q1 - q0 = q0 * q1 * Db := by
      rw [hDbdef]
      field_simp
    have hq1q : q1 - q = q * q1 * ((1 - lam) * Db) := by linarith [hdq1]
    rw [hq1q, hdq0, hq10, div_eq_mul_inv q p, hpa]
    field_simp

/-! ### Interpolating two one-cell band rates -/

/-- **Two-pair interpolation of one-cell band rates.**  Along a segment of positive slope the
uniform one-cell rates interpolate, and the interpolated ratio is the weighted geometric mean. -/
theorem oneCell_bandRate_interp {d : ℕ} (hd : 0 < d)
    (phi : SchwartzMap (Euclidean d) ℂ)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0)
    {p0 q0 p1 q1 p q lam : ℝ}
    (hp0 : 0 < p0) (hp1 : 0 < p1) (hq0 : 0 < q0) (hq1 : 0 < q1)
    (hr0 : 1 ≤ q0 / p0) (hr1 : 1 ≤ q1 / p1)
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hpa : p⁻¹ = (1 - lam) * p0⁻¹ + lam * p1⁻¹)
    (hqb : q⁻¹ = (1 - lam) * q0⁻¹ + lam * q1⁻¹)
    (hp01 : p0 < p1) (hq01 : q0 < q1)
    (h0 : HasOneCellBandRateReal phi hphiOne hphiZero p0 q0)
    (h1 : HasOneCellBandRateReal phi hphiOne hphiZero p1 q1) :
    HasOneCellBandRateReal phi hphiOne hphiZero p q := by
  obtain ⟨hp, hq, hp0p, hpp1, hq0q, hqq1, m, hm, hm0, hm1, hcol⟩ :=
    exists_twoPair_data_of_reciprocal hp0 hp1 hq0 hq1 hlam0 hlam1 hpa hqb hp01 hq01
  obtain ⟨C0, rho0, hC0, hrho0, hrho01, hbound0⟩ := h0
  obtain ⟨C1, rho1, hC1, hrho1, hrho11, hbound1⟩ := h1
  obtain ⟨C, hCpos, hC⟩ := exists_twoPair_interpolation_const (d := d)
    hp0 hp0p hpp1 hq0 hq0q hqq1 hr0 hr1 hm hm0 hm1 hcol
  set e0 : ℝ := q0 * ((q1 - q) / (q1 - q0)) / q with he0def
  set e1 : ℝ := q1 * ((q - q0) / (q1 - q0)) / q with he1def
  have hqden : 0 < q1 - q0 := by linarith
  have he0pos : 0 < e0 := by
    rw [he0def]
    exact div_pos (mul_pos hq0 (div_pos (by linarith) hqden)) hq
  have he1pos : 0 < e1 := by
    rw [he1def]
    exact div_pos (mul_pos hq1 (div_pos (by linarith) hqden)) hq
  have hsum : e0 + e1 = 1 := by
    rw [he0def, he1def]
    field_simp
    ring
  refine ⟨C * C0 ^ e0 * C1 ^ e1, rho0 ^ e0 * rho1 ^ e1, by positivity, by positivity, ?_, ?_⟩
  · -- the interpolated ratio is below one
    have h0' : rho0 ^ e0 < 1 ^ e0 := Real.rpow_lt_rpow hrho0.le hrho01 he0pos
    have h1' : rho1 ^ e1 < 1 ^ e1 := Real.rpow_lt_rpow hrho1.le hrho11 he1pos
    rw [Real.one_rpow] at h0' h1'
    have hpos0 : 0 < rho0 ^ e0 := Real.rpow_pos_of_pos hrho0 _
    have hpos1 : 0 < rho1 ^ e1 := Real.rpow_pos_of_pos hrho1 _
    calc rho0 ^ e0 * rho1 ^ e1 < 1 * 1 := by
          exact mul_lt_mul'' h0' h1' hpos0.le hpos1.le
      _ = 1 := by norm_num
  intro j hj E hE hEne a b hEab hlen f
  set T : SchwartzMap (Euclidean d) ℂ → Euclidean d → ℝ :=
    fun g => fractalDyadicBandpassMaximal d E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) g with hTdef
  have hEpos : E ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le zero_lt_one (hE ht).1
  have hmain := hC T
    (fun g x => fractalDyadicBandpassMaximal_nonneg E _ g x)
    (fun g h x => fractalDyadicBandpassMaximal_add_le hd E hEpos _ g h x)
    (fun g => (measurable_fractalDyadicBandpassMaximal E _ g).aestronglyMeasurable)
    (fun x => by
      have hprojection : dyadicBandpassProjection
          (absoluteDyadicBandpass phi hphiOne hphiZero j)
          (0 : SchwartzMap (Euclidean d) ℂ) = 0 := by
        simp [dyadicBandpassProjection]
      rw [hTdef]
      simp only
      rw [fractalDyadicBandpassMaximal, hprojection]
      exact Auto.Spherical.FractalDilations.AHRSLowerBounds.fractalSphericalMaximalReal_zero E x)
    (C0 * rho0 ^ j) (C1 * rho1 ^ j) (by positivity) (by positivity)
    (fun g => hbound0 j hj hE hEne hEab hlen g)
    (fun g => hbound1 j hj hE hEne hEab hlen g) f
  refine hmain.trans (le_of_eq ?_)
  congr 1
  have hexp0 : (C0 * rho0 ^ j) ^ e0 = C0 ^ e0 * (rho0 ^ e0) ^ j := by
    rw [Real.mul_rpow hC0.le (by positivity), rpow_npow_swap hrho0.le]
  have hexp1 : (C1 * rho1 ^ j) ^ e1 = C1 ^ e1 * (rho1 ^ e1) ^ j := by
    rw [Real.mul_rpow hC1.le (by positivity), rpow_npow_swap hrho1.le]
  rw [hexp0, hexp1, mul_pow]
  ring

open MeasureTheory Set ENNReal Metric FourierTransform
open scoped FourierTransform
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-! ### The two families of one-cell rates -/

/-- The diagonal one-cell rate at every exponent above one. -/
theorem oneCell_diagonal_bandRate_all {n : ℕ} (hn : 1 ≤ n)
    (phi psi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphiOne : ∀ xi : Euclidean (n + 1), ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean (n + 1), 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean (n + 1), ‖phi xi‖ ≤ 1)
    (hpsi : ∀ xi : Euclidean (n + 1),
      psi xi = phi (((2 : ℝ) ^ (0 + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ 0)⁻¹ • xi))
    {u : ℝ} (hu : 1 < u) :
    HasOneCellBandRateReal phi hphiOne hphiZero u u := by
  obtain ⟨B1, B2, hB1, hB2, hend⟩ :=
    exists_oneCell_dyadic_endpoints_all hn phi psi hphiOne hphiZero hphiNorm hpsi
  have hnpos : 0 < n := hn
  rcases lt_or_ge u 2 with hu2 | hu2
  · exact oneCell_diagonal_bandRate hnpos phi hphiOne hphiZero hB1 hB2 hend hu hu2
  · have hbase : HasOneCellBandRateReal phi hphiOne hphiZero (3 / 2) (3 / 2) :=
      oneCell_diagonal_bandRate hnpos phi hphiOne hphiZero hB1 hB2 hend
        (by norm_num) (by norm_num)
    exact oneCell_diagonal_bandRate_above (Nat.succ_pos n) phi hphiOne hphiZero
      (by norm_num) (by linarith) hbase

/-- The crossed one-cell rate on the conjugate line, parameterized by the reciprocal input
exponent `ξ`. -/
theorem oneCell_crossed_bandRate_of_xi {n : ℕ} (hn : 1 ≤ n)
    (phi psi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphiOne : ∀ xi : Euclidean (n + 1), ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean (n + 1), 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean (n + 1), ‖phi xi‖ ≤ 1)
    (hpsi : ∀ xi : Euclidean (n + 1),
      psi xi = phi (((2 : ℝ) ^ (0 + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ 0)⁻¹ • xi))
    {xi : ℝ} (hxi1 : 1 / 2 < xi) (hxi2 : xi < ((n : ℝ) + 1) / ((n : ℝ) + 2)) :
    HasOneCellBandRateReal phi hphiOne hphiZero (1 / xi) (1 / (1 - xi)) := by
  obtain ⟨B1, B2, hB1, hB2, hend⟩ :=
    exists_oneCell_dyadic_endpoints_all hn phi psi hphiOne hphiZero hphiNorm hpsi
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxipos : 0 < xi := by linarith
  have hxione : xi < 1 := by
    have : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith
  have honeminus : 0 < 1 - xi := by linarith
  have hp1 : 1 < 1 / xi := by
    rw [lt_div_iff₀ hxipos]
    linarith
  have hp2 : 1 / xi < 2 := by
    rw [div_lt_iff₀ hxipos]
    linarith
  have hq : 1 / (1 - xi) = (1 / xi) / ((1 / xi) - 1) := by
    field_simp
  have hstrict : 1 / (1 - xi) < (n : ℝ) + 2 := by
    rw [div_lt_iff₀ honeminus]
    have hxi2' : xi * ((n : ℝ) + 2) < (n : ℝ) + 1 :=
      (lt_div_iff₀ (show (0:ℝ) < (n : ℝ) + 2 by linarith)).mp hxi2
    linarith
  have hrate := oneCell_crossed_bandRate phi hphiOne hphiZero hB2
    (fun j hj E hE hEne a b hEab hlen f => (hend j hj hE hEne hEab hlen f).2)
    hp1 hp2 hq hstrict
  exact hasOneCellBandRateReal_of_hasOneCellBandRate hrate

open MeasureTheory Set ENNReal Metric FourierTransform
open scoped FourierTransform
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-! ### The segment through a reciprocal point joining the conjugate line to the diagonal -/

/-- Given a reciprocal point `(x,y)` with `y < x` and a conjugate-line parameter `xi` satisfying
three explicit lower bounds, the segment joining `(xi, 1 - xi)` to the diagonal passes through
`(x,y)`, with weight `nu ∈ (0,1)` and diagonal parameter `t ∈ (0,1)`. -/
theorem exists_oneCell_segment_data {x y xi : ℝ} (hy : 0 < y) (hyx : y < x)
    (hxihalf : 1 / 2 < xi) (hxinu : (1 + x - y) / 2 < xi)
    (hxit0 : x / (x + y) < xi) (hxit1 : (1 - y) / (2 - x - y) < xi) (hx1 : x < 1) :
    ∃ nu t : ℝ, 0 < nu ∧ nu < 1 ∧ 0 < t ∧ t < 1 ∧
      x = (1 - nu) * xi + nu * t ∧ y = (1 - nu) * (1 - xi) + nu * t := by
  have hxpos : 0 < x := lt_trans hy hyx
  have hsumpos : 0 < x + y := by linarith
  have hD1 : 0 < 2 * xi - 1 := by linarith
  have hD2 : 0 < (2 * xi - 1) - (x - y) := by linarith
  have hD1' : (2 * xi - 1) ≠ 0 := ne_of_gt hD1
  have hD2' : ((2 * xi - 1) - (x - y)) ≠ 0 := ne_of_gt hD2
  have hden : 0 < 2 - x - y := by linarith
  have hnum0 : 0 < x * (2 * xi - 1) - (x - y) * xi := by
    have h := (div_lt_iff₀ hsumpos).mp hxit0
    nlinarith
  have hnum1 : x * (2 * xi - 1) - (x - y) * xi < (2 * xi - 1) - (x - y) := by
    have h := (div_lt_iff₀ hden).mp hxit1
    nlinarith
  refine ⟨((2 * xi - 1) - (x - y)) / (2 * xi - 1),
    (x * (2 * xi - 1) - (x - y) * xi) / ((2 * xi - 1) - (x - y)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos hD2 hD1
  · rw [div_lt_one hD1]
    linarith
  · exact div_pos hnum0 hD2
  · rw [div_lt_one hD2]
    exact hnum1
  · have h1 : (1 : ℝ) - ((2 * xi - 1) - (x - y)) / (2 * xi - 1) = (x - y) / (2 * xi - 1) := by
      field_simp
      ring
    rw [h1]
    field_simp
    ring
  · have h1 : (1 : ℝ) - ((2 * xi - 1) - (x - y)) / (2 * xi - 1) = (x - y) / (2 * xi - 1) := by
      field_simp
      ring
    rw [h1]
    field_simp
    ring

open MeasureTheory Set ENNReal Metric FourierTransform
open scoped FourierTransform
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds



set_option maxHeartbeats 1000000 in
/-- **The one-cell band rate at every interior point of `Q(0,0)`.**  The three strict
inequalities are the interior conditions of the region `Q(d,0,0)` for `d = n + 1`; the rate is
uniform over all radius sets confined to a single band cell. -/
theorem oneCell_bandRate_of_strict {n : ℕ} (hn : 1 ≤ n)
    (phi psi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphiOne : ∀ xi : Euclidean (n + 1), ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean (n + 1), 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean (n + 1), ‖phi xi‖ ≤ 1)
    (hpsi : ∀ xi : Euclidean (n + 1),
      psi xi = phi (((2 : ℝ) ^ (0 + 1))⁻¹ • xi) - phi (((2 : ℝ) ^ 0)⁻¹ • xi))
    {x y : ℝ} (hy : 0 < y) (hyx : y < x)
    (hcap : x < ((n : ℝ) + 1) * y) (hann : ((n : ℝ) + 1) * x < y + (n : ℝ)) :
    HasOneCellBandRateReal phi hphiOne hphiZero (1 / x) (1 / y) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxpos : 0 < x := lt_trans hy hyx
  have hsumpos : 0 < x + y := by linarith
  have hx1 : x < 1 := by nlinarith
  have hy1 : y < 1 := by linarith
  have hgap : x - y < (n : ℝ) / ((n : ℝ) + 2) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < (n : ℝ) + 2)]
    nlinarith
  have hhalfmax : (1 : ℝ) / 2 < ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
    linarith
  rcases lt_trichotomy (x + y) 1 with hcase | hcase | hcase
  · -- below the conjugate line
    have hylt : y < 1 / 2 := by linarith
    have hxupper : x < ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      rw [lt_div_iff₀ (by linarith : (0:ℝ) < (n : ℝ) + 2)]
      nlinarith
    set m : ℝ := min (1 - y) (((n : ℝ) + 1) / ((n : ℝ) + 2)) with hmdef
    set M : ℝ := max (max (1 / 2) x)
      (max (x / (x + y)) (max ((1 + x - y) / 2) ((1 - y) / (2 - x - y)))) with hMdef
    have hden : (0 : ℝ) < 2 - x - y := by linarith
    have hMm : M < m := by
      rw [hMdef, hmdef]
      refine max_lt (max_lt ?_ ?_) (max_lt ?_ (max_lt ?_ ?_)) <;> refine lt_min ?_ ?_
      · linarith
      · exact hhalfmax
      · linarith
      · exact hxupper
      · rw [div_lt_iff₀ hsumpos]
        nlinarith
      · rw [div_lt_div_iff₀ hsumpos (by linarith : (0:ℝ) < (n : ℝ) + 2)]
        nlinarith
      · linarith
      · rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) (by linarith : (0:ℝ) < (n : ℝ) + 2)]
        nlinarith
      · rw [div_lt_iff₀ hden]
        nlinarith
      · rw [div_lt_div_iff₀ hden (by linarith : (0:ℝ) < (n : ℝ) + 2)]
        nlinarith
    set xi : ℝ := (M + m) / 2 with hxidef
    have hxiM : M < xi := by rw [hxidef]; linarith
    have hxim : xi < m := by rw [hxidef]; linarith
    have hxihalf : (1 : ℝ) / 2 < xi := lt_of_le_of_lt (le_trans (le_max_left _ _)
      (le_max_left _ _)) hxiM
    have hxix : x < xi := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hxiM
    have hxit0 : x / (x + y) < xi := lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right _ _)) hxiM
    have hxinu : (1 + x - y) / 2 < xi := lt_of_le_of_lt
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hxiM
    have hxit1 : (1 - y) / (2 - x - y) < xi := lt_of_le_of_lt
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hxiM
    have hxiy : xi < 1 - y := lt_of_lt_of_le hxim (min_le_left _ _)
    have hxin : xi < ((n : ℝ) + 1) / ((n : ℝ) + 2) := lt_of_lt_of_le hxim (min_le_right _ _)
    have hxione : xi < 1 := by linarith
    have hxipos : 0 < xi := by linarith
    obtain ⟨nu, t, hnu0, hnu1, ht0, ht1, hxid, hyid⟩ :=
      exists_oneCell_segment_data hy hyx hxihalf hxinu hxit0 hxit1 hx1
    -- the diagonal parameter is below both `x` and `1 - xi`
    have htx : t < x := by nlinarith
    have hty : t < y := by nlinarith
    have htxi : t < 1 - xi := by linarith
    -- the two rates
    have h0 : HasOneCellBandRateReal phi hphiOne hphiZero (1 / xi) (1 / (1 - xi)) :=
      oneCell_crossed_bandRate_of_xi hn phi psi hphiOne hphiZero hphiNorm hpsi hxihalf hxin
    have h1 : HasOneCellBandRateReal phi hphiOne hphiZero (1 / t) (1 / t) :=
      oneCell_diagonal_bandRate_all hn phi psi hphiOne hphiZero hphiNorm hpsi
        (by rw [lt_div_iff₀ ht0]; linarith)
    refine oneCell_bandRate_interp (Nat.succ_pos n) phi hphiOne hphiZero
      (by positivity) (by positivity) (by positivity) (by positivity) ?_
      (by rw [div_self (by positivity : (1:ℝ) / t ≠ 0)])
      hnu0 hnu1 ?_ ?_ ?_ ?_ h0 h1
    · have hratio : (1 : ℝ) / (1 - xi) / (1 / xi) = xi / (1 - xi) := by
        field_simp
      rw [hratio, le_div_iff₀ (by linarith : (0:ℝ) < 1 - xi)]
      linarith
    · simp only [one_div, inv_inv]
      exact hxid
    · simp only [one_div, inv_inv]
      exact hyid
    · exact one_div_lt_one_div_of_lt ht0 (by linarith)
    · exact one_div_lt_one_div_of_lt ht0 (by linarith)
  · -- on the conjugate line
    have hxhalf : (1 : ℝ) / 2 < x := by linarith
    have hxupper : x < ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      rw [lt_div_iff₀ (by linarith : (0:ℝ) < (n : ℝ) + 2)]
      nlinarith
    have hyx' : y = 1 - x := by linarith
    have h := oneCell_crossed_bandRate_of_xi hn phi psi hphiOne hphiZero hphiNorm hpsi
      hxhalf hxupper
    rw [← hyx'] at h
    exact h
  · -- above the conjugate line
    have hxhalf : (1 : ℝ) / 2 < x := by linarith
    have hylower : 1 / ((n : ℝ) + 2) < y := by
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < (n : ℝ) + 2)]
      nlinarith
    set m : ℝ := min x (((n : ℝ) + 1) / ((n : ℝ) + 2)) with hmdef
    set M : ℝ := max (max (1 / 2) (1 - y))
      (max (x / (x + y)) (max ((1 + x - y) / 2) ((1 - y) / (2 - x - y)))) with hMdef
    have hden : (0 : ℝ) < 2 - x - y := by linarith
    have hMm : M < m := by
      rw [hMdef, hmdef]
      refine max_lt (max_lt ?_ ?_) (max_lt ?_ (max_lt ?_ ?_)) <;> refine lt_min ?_ ?_
      · linarith
      · exact hhalfmax
      · linarith
      · have hy' : 1 < y * ((n : ℝ) + 2) :=
          (div_lt_iff₀ (by linarith : (0:ℝ) < (n : ℝ) + 2)).mp hylower
        rw [lt_div_iff₀ (by linarith : (0:ℝ) < (n : ℝ) + 2)]
        nlinarith
      · rw [div_lt_iff₀ hsumpos]
        nlinarith
      · rw [div_lt_div_iff₀ hsumpos (by linarith : (0:ℝ) < (n : ℝ) + 2)]
        nlinarith
      · linarith
      · rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) (by linarith : (0:ℝ) < (n : ℝ) + 2)]
        nlinarith
      · rw [div_lt_iff₀ hden]
        nlinarith
      · rw [div_lt_div_iff₀ hden (by linarith : (0:ℝ) < (n : ℝ) + 2)]
        nlinarith
    set xi : ℝ := (M + m) / 2 with hxidef
    have hxiM : M < xi := by rw [hxidef]; linarith
    have hxim : xi < m := by rw [hxidef]; linarith
    have hxihalf : (1 : ℝ) / 2 < xi := lt_of_le_of_lt (le_trans (le_max_left _ _)
      (le_max_left _ _)) hxiM
    have hxiy : 1 - y < xi := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hxiM
    have hxit0 : x / (x + y) < xi := lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right _ _)) hxiM
    have hxinu : (1 + x - y) / 2 < xi := lt_of_le_of_lt
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hxiM
    have hxit1 : (1 - y) / (2 - x - y) < xi := lt_of_le_of_lt
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hxiM
    have hxix : xi < x := lt_of_lt_of_le hxim (min_le_left _ _)
    have hxin : xi < ((n : ℝ) + 1) / ((n : ℝ) + 2) := lt_of_lt_of_le hxim (min_le_right _ _)
    have hxione : xi < 1 := by linarith
    have hxipos : 0 < xi := by linarith
    obtain ⟨nu, t, hnu0, hnu1, ht0, ht1, hxid, hyid⟩ :=
      exists_oneCell_segment_data hy hyx hxihalf hxinu hxit0 hxit1 hx1
    -- the diagonal parameter is above both `x` and `1 - xi`
    have htx : x < t := by nlinarith
    have htxi : 1 - xi < t := by nlinarith
    have h1 : HasOneCellBandRateReal phi hphiOne hphiZero (1 / xi) (1 / (1 - xi)) :=
      oneCell_crossed_bandRate_of_xi hn phi psi hphiOne hphiZero hphiNorm hpsi hxihalf hxin
    have h0 : HasOneCellBandRateReal phi hphiOne hphiZero (1 / t) (1 / t) :=
      oneCell_diagonal_bandRate_all hn phi psi hphiOne hphiZero hphiNorm hpsi
        (by rw [lt_div_iff₀ ht0]; linarith)
    refine oneCell_bandRate_interp (Nat.succ_pos n) phi hphiOne hphiZero
      (by positivity) (by positivity) (by positivity) (by positivity)
      (by rw [div_self (by positivity : (1:ℝ) / t ≠ 0)]) ?_
      (by linarith : (0:ℝ) < 1 - nu) (by linarith : 1 - nu < 1) ?_ ?_ ?_ ?_ h0 h1
    · have hratio : (1 : ℝ) / (1 - xi) / (1 / xi) = xi / (1 - xi) := by
        field_simp
      rw [hratio, le_div_iff₀ (by linarith : (0:ℝ) < 1 - xi)]
      linarith
    · simp only [one_div, inv_inv]
      rw [show (1 : ℝ) - (1 - nu) = nu by ring]
      linarith [hxid]
    · simp only [one_div, inv_inv]
      rw [show (1 : ℝ) - (1 - nu) = nu by ring]
      linarith [hyid]
    · exact one_div_lt_one_div_of_lt hxipos (by linarith)
    · exact one_div_lt_one_div_of_lt (by linarith : (0:ℝ) < 1 - xi) (by linarith)

open MeasureTheory Set ENNReal
open Auto.FractalDimensions
open Auto.FractalDimensions
/-! ### Affine images of radius sets -/

/-- An affine image of an interval cover is an interval cover of the affine image. -/
theorem isIntervalCover_image_affine {E : Set ℝ} {c s δ : ℝ} (hs : 0 < s) {ι : Finset ℝ}
    (h : IsIntervalCover E δ ι) :
    IsIntervalCover ((fun r => c + s * r) '' E) (s * δ) (ι.image (fun a => c + s * a)) := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨a, ha, hra⟩ := Set.mem_iUnion₂.mp (h hr)
  refine Set.mem_iUnion₂.mpr ⟨c + s * a, Finset.mem_image_of_mem _ ha, ?_, ?_⟩
  · have := hra.1
    nlinarith
  · have := hra.2
    nlinarith

/-- A one-element cover of a set of small diameter. -/
theorem isIntervalCover_singleton_of_subset {E : Set ℝ} {u v δ : ℝ}
    (hE : E ⊆ Icc u v) (hlen : v - u ≤ δ) :
    IsIntervalCover E δ {(u + v) / 2} :=
  oneCell_isIntervalCover hE hlen

/-- **Affine invariance of the upper Minkowski covering exponents.** -/
theorem hasUpperMinkowskiExponent_image_affine {E : Set ℝ} {c s β : ℝ} (hs : 0 < s)
    (hβ : 0 ≤ β) (hE : E ⊆ Icc (1 : ℝ) 2)
    (h : HasUpperMinkowskiExponent E β) :
    HasUpperMinkowskiExponent ((fun r => c + s * r) '' E) β := by
  intro ε hε
  obtain ⟨C, hC, hcov⟩ := h ε hε
  refine ⟨max (C * s ^ (β + ε)) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro δ hδ hδone
  have hpow : (1 : ℝ) ≤ δ ^ (-(β + ε)) := by
    rw [show (-(β + ε) : ℝ) = -(β + ε) from rfl]
    refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδone.le (by linarith)
  rcases le_or_gt s δ with hsδ | hsδ
  · -- the whole affine image fits into a single interval of length `δ`
    refine ⟨{(c + s * 1 + (c + s * 2)) / 2}, ?_, ?_⟩
    · refine isIntervalCover_singleton_of_subset (u := c + s * 1) (v := c + s * 2) ?_ ?_
      · intro x hx
        obtain ⟨r, hr, rfl⟩ := hx
        obtain ⟨hr1, hr2⟩ := hE hr
        exact ⟨by nlinarith, by nlinarith⟩
      · nlinarith
    · have h1 : ((({(c + s * 1 + (c + s * 2)) / 2} : Finset ℝ).card : ℝ)) = 1 := by simp
      rw [h1]
      calc (1 : ℝ) ≤ δ ^ (-(β + ε)) := hpow
        _ = 1 * δ ^ (-(β + ε)) := by ring
        _ ≤ max (C * s ^ (β + ε)) 1 * δ ^ (-(β + ε)) := by
            refine mul_le_mul_of_nonneg_right (le_max_right _ _) ?_
            exact Real.rpow_nonneg hδ.le _
  · -- pull the scale back through the affine map
    have hδ' : 0 < δ / s := div_pos hδ hs
    have hδ'one : δ / s < 1 := by
      rw [div_lt_one hs]
      exact hsδ
    obtain ⟨ι, hcover, hcard⟩ := hcov (δ / s) hδ' hδ'one
    refine ⟨ι.image (fun a => c + s * a), ?_, ?_⟩
    · have h := isIntervalCover_image_affine (c := c) hs hcover
      rw [show s * (δ / s) = δ by field_simp] at h
      exact h
    · have hcardle : ((ι.image (fun a => c + s * a)).card : ℝ) ≤ (ι.card : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (Finset.card_image_le)
      refine hcardle.trans (hcard.trans ?_)
      have hrw : (δ / s) ^ (-(β + ε)) = s ^ (β + ε) * δ ^ (-(β + ε)) := by
        rw [Real.div_rpow hδ.le hs.le, Real.rpow_neg hδ.le, Real.rpow_neg hs.le]
        field_simp
      rw [hrw]
      calc C * (s ^ (β + ε) * δ ^ (-(β + ε)))
          = (C * s ^ (β + ε)) * δ ^ (-(β + ε)) := by ring
        _ ≤ max (C * s ^ (β + ε)) 1 * δ ^ (-(β + ε)) := by
            refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
            exact Real.rpow_nonneg hδ.le _

open MeasureTheory Set ENNReal
open Auto.FractalDimensions
open Auto.FractalDimensions
set_option maxHeartbeats 1000000 in
/-- **Affine invariance of the upper Assouad spectrum exponents.** -/
theorem hasUpperAssouadSpectrumExponent_image_affine {E : Set ℝ} {c s θ γ : ℝ}
    (hs : 0 < s) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hγ : 0 ≤ γ)
    (hE : E ⊆ Icc (1 : ℝ) 2)
    (h : HasUpperAssouadSpectrumExponent E θ γ) :
    HasUpperAssouadSpectrumExponent ((fun r => c + s * r) '' E) θ γ := by
  obtain ⟨C, hC, hcov⟩ := h
  refine ⟨max (C * (max 1 s) ^ γ) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro δ a b hδ hδone ha hab hb hscale
  have hCmax : C * (max 1 s) ^ γ ≤ max (C * (max 1 s) ^ γ) 1 := le_max_left _ _
  have honemax : (1 : ℝ) ≤ max (C * (max 1 s) ^ γ) 1 := le_max_right _ _
  have hratio : (1 : ℝ) ≤ (b - a) / δ := by
    rw [le_div_iff₀ hδ]
    have hδθ : δ ≤ δ ^ θ := by
      calc δ = δ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ δ ^ θ := Real.rpow_le_rpow_of_exponent_ge hδ hδone.le hθ1
    linarith
  have hratiopow : (1 : ℝ) ≤ ((b - a) / δ) ^ γ :=
    Real.one_le_rpow hratio hγ
  rcases le_or_gt s δ with hsδ | hsδ
  · -- one interval covers the whole affine image
    refine ⟨{(c + s * 1 + (c + s * 2)) / 2}, ?_, ?_⟩
    · refine isIntervalCover_singleton_of_subset (u := c + s * 1) (v := c + s * 2) ?_ (by nlinarith)
      intro x hx
      obtain ⟨hx1, -⟩ := hx
      obtain ⟨r, hr, rfl⟩ := hx1
      obtain ⟨hr1, hr2⟩ := hE hr
      exact ⟨by nlinarith, by nlinarith⟩
    · have h1 : ((({(c + s * 1 + (c + s * 2)) / 2} : Finset ℝ).card : ℝ)) = 1 := by simp
      rw [h1]
      calc (1 : ℝ) ≤ ((b - a) / δ) ^ γ := hratiopow
        _ = 1 * ((b - a) / δ) ^ γ := by ring
        _ ≤ max (C * (max 1 s) ^ γ) 1 * ((b - a) / δ) ^ γ := by
            exact mul_le_mul_of_nonneg_right honemax (Real.rpow_nonneg (by positivity) _)
  -- from now on the band scale is finer than the affine scale
  have hδ' : 0 < δ / s := div_pos hδ hs
  have hδ'one : δ / s < 1 := by
    rw [div_lt_one hs]
    exact hsδ
  set alpha : ℝ := max 1 ((a - c) / s) with halphadef
  set beta : ℝ := min 2 ((b - c) / s) with hbetadef
  have halpha1 : (1 : ℝ) ≤ alpha := le_max_left _ _
  have hbeta2 : beta ≤ 2 := min_le_left _ _
  have hsubset : ((fun r => c + s * r) '' E) ∩ Icc a b
      ⊆ (fun r => c + s * r) '' (E ∩ Icc alpha beta) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨r, hr, rfl⟩ := hx1
    obtain ⟨hr1, hr2⟩ := hE hr
    refine ⟨r, ⟨hr, ?_, ?_⟩, rfl⟩
    · refine max_le hr1 ?_
      rw [div_le_iff₀ hs]
      have := hx2.1
      nlinarith
    · refine le_min hr2 ?_
      rw [le_div_iff₀ hs]
      have := hx2.2
      nlinarith
  have hlenle : beta - alpha ≤ (b - a) / s := by
    have h1 : (a - c) / s ≤ alpha := le_max_right _ _
    have h2 : beta ≤ (b - c) / s := min_le_right _ _
    have h3 : (b - c) / s - (a - c) / s = (b - a) / s := by
      field_simp
      ring
    linarith
  rcases le_or_gt alpha beta with hab' | hab'
  · rcases le_or_gt ((δ / s) ^ θ) (beta - alpha) with hcase | hcase
    · -- the pulled back interval is long enough for the spectrum estimate
      obtain ⟨ι, hcover, hcard⟩ := hcov (δ / s) alpha beta hδ' hδ'one halpha1 hab' hbeta2 hcase
      refine ⟨ι.image (fun u => c + s * u), ?_, ?_⟩
      · have himg := isIntervalCover_image_affine (c := c) hs hcover
        rw [show s * (δ / s) = δ by field_simp] at himg
        exact fun x hx => himg (hsubset hx)
      · have hcardle : ((ι.image (fun u => c + s * u)).card : ℝ) ≤ (ι.card : ℝ) := by
          exact_mod_cast Nat.cast_le.mpr Finset.card_image_le
        refine hcardle.trans (hcard.trans ?_)
        have hkey : (beta - alpha) / (δ / s) ≤ (b - a) / δ := by
          rw [div_le_div_iff₀ hδ' hδ]
          have h1 : (beta - alpha) * δ ≤ ((b - a) / s) * δ :=
            mul_le_mul_of_nonneg_right hlenle hδ.le
          have h2 : ((b - a) / s) * δ = (b - a) * (δ / s) := by field_simp
          linarith
        calc C * ((beta - alpha) / (δ / s)) ^ γ
            ≤ C * ((b - a) / δ) ^ γ := by
              refine mul_le_mul_of_nonneg_left ?_ hC.le
              exact Real.rpow_le_rpow (by positivity) hkey hγ
          _ ≤ max (C * (max 1 s) ^ γ) 1 * ((b - a) / δ) ^ γ := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
              have hone : (1 : ℝ) ≤ (max 1 s) ^ γ :=
                Real.one_le_rpow (le_max_left _ _) hγ
              calc C = C * 1 := by ring
                _ ≤ C * (max 1 s) ^ γ := mul_le_mul_of_nonneg_left hone hC.le
                _ ≤ max (C * (max 1 s) ^ γ) 1 := hCmax
    · -- the pulled back interval is short: enlarge it to the critical length
      set ell : ℝ := (δ / s) ^ θ with helldef
      have hellpos : 0 < ell := Real.rpow_pos_of_pos hδ' _
      have hellone : ell ≤ 1 := by
        rw [helldef]
        exact Real.rpow_le_one hδ'.le hδ'one.le hθ0
      set alpha0 : ℝ := min alpha (2 - ell) with halpha0def
      have halpha01 : (1 : ℝ) ≤ alpha0 := by
        rw [halpha0def]
        exact le_min halpha1 (by linarith)
      have halpha0le : alpha0 ≤ alpha := min_le_left _ _
      have hbeta0 : alpha0 + ell ≤ 2 := by
        rcases min_cases alpha (2 - ell) with ⟨heq, hle⟩ | ⟨heq, hle⟩
        · rw [halpha0def, heq]
          linarith
        · rw [halpha0def, heq]
          linarith
      have hbetale : beta ≤ alpha0 + ell := by
        rcases min_cases alpha (2 - ell) with ⟨heq, hle⟩ | ⟨heq, hle⟩
        · rw [halpha0def, heq]
          linarith
        · rw [halpha0def, heq]
          linarith
      obtain ⟨ι, hcover, hcard⟩ := hcov (δ / s) alpha0 (alpha0 + ell) hδ' hδ'one halpha01
        (by linarith) hbeta0 (by rw [← helldef]; linarith)
      refine ⟨ι.image (fun u => c + s * u), ?_, ?_⟩
      · have himg := isIntervalCover_image_affine (c := c) hs hcover
        rw [show s * (δ / s) = δ by field_simp] at himg
        refine fun x hx => himg ?_
        obtain ⟨r, ⟨hrE, hr1, hr2⟩, rfl⟩ := hsubset hx
        refine ⟨r, ⟨hrE, ?_, ?_⟩, rfl⟩
        · linarith
        · linarith
      · have hcardle : ((ι.image (fun u => c + s * u)).card : ℝ) ≤ (ι.card : ℝ) := by
          exact_mod_cast Nat.cast_le.mpr Finset.card_image_le
        refine hcardle.trans (hcard.trans ?_)
        have hlenratio : (alpha0 + ell - alpha0) / (δ / s) = (δ / s) ^ (θ - 1) := by
          rw [show alpha0 + ell - alpha0 = ell by ring, helldef,
            show (θ - 1 : ℝ) = θ + (-1) by ring, Real.rpow_add hδ', Real.rpow_neg_one]
          rw [div_eq_mul_inv]
        rw [hlenratio]
        have hspow : (δ / s) ^ (θ - 1) ≤ (max 1 s) * ((b - a) / δ) := by
          have h1 : (δ / s) ^ (θ - 1) = δ ^ (θ - 1) * s ^ (1 - θ) := by
            rw [Real.div_rpow hδ.le hs.le, show (1 - θ : ℝ) = -(θ - 1) by ring,
              Real.rpow_neg hs.le]
            field_simp
          have h2 : s ^ (1 - θ) ≤ max 1 s := by
            rcases le_or_gt s 1 with hs1 | hs1
            · calc s ^ (1 - θ) ≤ 1 ^ (1 - θ) := Real.rpow_le_rpow hs.le hs1 (by linarith)
                _ = 1 := Real.one_rpow _
                _ ≤ max 1 s := le_max_left _ _
            · calc s ^ (1 - θ) ≤ s ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le hs1.le (by linarith)
                _ = s := Real.rpow_one s
                _ ≤ max 1 s := le_max_right _ _
          have h3 : δ ^ (θ - 1) ≤ (b - a) / δ := by
            rw [le_div_iff₀ hδ]
            have h4 : δ ^ (θ - 1) * δ = δ ^ θ := by
              rw [show (θ : ℝ) = (θ - 1) + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
              congr 2
              ring
            rw [h4]
            exact hscale
          rw [h1]
          have hδpow : 0 ≤ δ ^ (θ - 1) := Real.rpow_nonneg hδ.le _
          have hspos : 0 ≤ s ^ (1 - θ) := Real.rpow_nonneg hs.le _
          calc δ ^ (θ - 1) * s ^ (1 - θ) ≤ δ ^ (θ - 1) * max 1 s :=
                mul_le_mul_of_nonneg_left h2 hδpow
            _ ≤ ((b - a) / δ) * max 1 s := by
                refine mul_le_mul_of_nonneg_right h3 ?_
                exact le_trans zero_le_one (le_max_left _ _)
            _ = max 1 s * ((b - a) / δ) := by ring
        calc C * ((δ / s) ^ (θ - 1)) ^ γ
            ≤ C * ((max 1 s) * ((b - a) / δ)) ^ γ := by
              refine mul_le_mul_of_nonneg_left ?_ hC.le
              exact Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hspow hγ
          _ = (C * (max 1 s) ^ γ) * ((b - a) / δ) ^ γ := by
              rw [Real.mul_rpow (le_trans zero_le_one (le_max_left _ _)) (by positivity)]
              ring
          _ ≤ max (C * (max 1 s) ^ γ) 1 * ((b - a) / δ) ^ γ :=
              mul_le_mul_of_nonneg_right hCmax (Real.rpow_nonneg (by positivity) _)
  · -- the pulled back interval is empty
    refine ⟨∅, ?_, ?_⟩
    · intro x hx
      obtain ⟨r, ⟨-, hr1, hr2⟩, rfl⟩ := hsubset hx
      exact absurd (le_trans hr1 hr2) (by linarith)
    · simp only [Finset.card_empty, Nat.cast_zero]
      have hpos : (0 : ℝ) ≤ ((b - a) / δ) ^ γ := Real.rpow_nonneg (by positivity) _
      have hCpos : (0 : ℝ) ≤ max (C * (max 1 s) ^ γ) 1 := le_trans zero_le_one honemax
      exact mul_nonneg hCpos hpos

open MeasureTheory Set ENNReal
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.FractalDimensions



/-! ### The inverse of an affine map -/

theorem image_affine_inverse {E : Set ℝ} {c s : ℝ} (hs : 0 < s) :
    (fun x => (-(c / s)) + s⁻¹ * x) '' ((fun r => c + s * r) '' E) = E := by
  rw [Set.image_image]
  have hid : ∀ r : ℝ, (-(c / s)) + s⁻¹ * (c + s * r) = r := by
    intro r
    field_simp
    ring
  simp only [hid]
  exact Set.image_id E

/-! ### Affine invariance of the two dimensions -/

theorem upperMinkowskiDimension_image_affine {E : Set ℝ} {c s : ℝ} (hs : 0 < s)
    (hE : E ⊆ Icc (1 : ℝ) 2) (hA : ((fun r => c + s * r) '' E) ⊆ Icc (1 : ℝ) 2) :
    upperMinkowskiDimension ((fun r => c + s * r) '' E) = upperMinkowskiDimension E := by
  have hsets : {t : ℝ | 0 ≤ t ∧ HasUpperMinkowskiExponent ((fun r => c + s * r) '' E) t}
      = {t : ℝ | 0 ≤ t ∧ HasUpperMinkowskiExponent E t} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨ht, hexp⟩
      refine ⟨ht, ?_⟩
      have hback := hasUpperMinkowskiExponent_image_affine (c := -(c / s)) (s := s⁻¹)
        (inv_pos.mpr hs) ht hA hexp
      rwa [image_affine_inverse hs] at hback
    · rintro ⟨ht, hexp⟩
      exact ⟨ht, hasUpperMinkowskiExponent_image_affine hs ht hE hexp⟩
  unfold upperMinkowskiDimension
  rw [hsets]

theorem upperAssouadSpectrum_image_affine {E : Set ℝ} {c s θ : ℝ} (hs : 0 < s)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hE : E ⊆ Icc (1 : ℝ) 2) (hA : ((fun r => c + s * r) '' E) ⊆ Icc (1 : ℝ) 2) :
    upperAssouadSpectrum ((fun r => c + s * r) '' E) θ = upperAssouadSpectrum E θ := by
  have hsets : {t : ℝ | 0 ≤ t ∧ HasUpperAssouadSpectrumExponent ((fun r => c + s * r) '' E) θ t}
      = {t : ℝ | 0 ≤ t ∧ HasUpperAssouadSpectrumExponent E θ t} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨ht, hexp⟩
      refine ⟨ht, ?_⟩
      have hback := hasUpperAssouadSpectrumExponent_image_affine (c := -(c / s)) (s := s⁻¹)
        (inv_pos.mpr hs) hθ0 hθ1 ht hA hexp
      rwa [image_affine_inverse hs] at hback
    · rintro ⟨ht, hexp⟩
      exact ⟨ht, hasUpperAssouadSpectrumExponent_image_affine hs hθ0 hθ1 ht hE hexp⟩
  unfold upperAssouadSpectrum
  rw [hsets]

theorem quasiAssouadDimension_image_affine {E : Set ℝ} {c s : ℝ} (hs : 0 < s)
    (hE : E ⊆ Icc (1 : ℝ) 2) (hA : ((fun r => c + s * r) '' E) ⊆ Icc (1 : ℝ) 2) :
    quasiAssouadDimension ((fun r => c + s * r) '' E) = quasiAssouadDimension E := by
  unfold quasiAssouadDimension
  congr 1
  refine Set.image_congr ?_
  intro θ hθ
  exact upperAssouadSpectrum_image_affine hs hθ.1 (le_of_lt hθ.2) hE hA

/-- **Affine invariance of quasi-Assouad regularity.** -/
theorem isQuasiAssouadRegular_image_affine {E : Set ℝ} {c s beta gam : ℝ} (hs : 0 < s)
    (hE : E ⊆ Icc (1 : ℝ) 2) (hA : ((fun r => c + s * r) '' E) ⊆ Icc (1 : ℝ) 2)
    (h : IsQuasiAssouadRegular E beta gam) :
    IsQuasiAssouadRegular ((fun r => c + s * r) '' E) beta gam := by
  obtain ⟨hM, hQ, hspec⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [upperMinkowskiDimension_image_affine hs hE hA]
    exact hM
  · rw [quasiAssouadDimension_image_affine hs hE hA]
    exact hQ
  · rcases hspec with hzero | hall
    · exact Or.inl hzero
    · refine Or.inr ?_
      intro θ hθ0 hθ1 hθcrit
      rw [upperAssouadSpectrum_image_affine hs hθ0 hθ1.le hE hA]
      exact hall θ hθ0 hθ1 hθcrit

open MeasureTheory Set ENNReal
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-! ### Reassembly from a summable sequence of band bounds -/

/-- The `L^q` norm of a finite sum is bounded by the corresponding sum of bounds. -/
theorem finite_output_sum_of_bounds {d : ℕ} {q : ENNReal} (hq : (1 : ENNReal) ≤ q)
    (T : ℕ → Euclidean d → ℝ) (hTmem : ∀ j, MemLp (T j) q volume)
    (a : ℕ → ENNReal) (hTnorm : ∀ j, eLpNorm (T j) q volume ≤ a j) (N : ℕ) :
    MemLp (fun x => ∑ j ∈ Finset.range N, T j x) q volume ∧
      eLpNorm (fun x => ∑ j ∈ Finset.range N, T j x) q volume
        ≤ ∑ j ∈ Finset.range N, a j := by
  induction N with
  | zero =>
      refine ⟨?_, ?_⟩
      · simpa using (memLp_zero_iff_aestronglyMeasurable (μ := (volume : Measure (Euclidean d)))
          (p := q) (f := fun _ : Euclidean d => (0 : ℝ))) |>.mpr aestronglyMeasurable_const
      · simp
  | succ N ih =>
      obtain ⟨hmem, hnorm⟩ := ih
      have hsplit : ∀ x : Euclidean d, ∑ j ∈ Finset.range (N + 1), T j x
          = (∑ j ∈ Finset.range N, T j x) + T N x := by
        intro x
        rw [Finset.sum_range_succ]
      have hrw0 : (fun x : Euclidean d => ∑ j ∈ Finset.range (N + 1), T j x)
          = (fun x => ∑ j ∈ Finset.range N, T j x) + T N := by
        funext x
        rw [hsplit x]
        rfl
      have hmem' : MemLp (fun x => ∑ j ∈ Finset.range (N + 1), T j x) q volume := by
        rw [hrw0]
        exact hmem.add (hTmem N)
      refine ⟨hmem', ?_⟩
      have hrw : (fun x : Euclidean d => ∑ j ∈ Finset.range (N + 1), T j x)
          = (fun x => ∑ j ∈ Finset.range N, T j x) + T N := by
        funext x
        rw [hsplit x]
        rfl
      rw [hrw, Finset.sum_range_succ]
      refine le_trans (eLpNorm_add_le hmem.1 (hTmem N).1 hq) ?_
      exact add_le_add hnorm (hTnorm N)

set_option maxHeartbeats 1000000 in
/-- **Reassembly of a summable family of band bounds.**  The geometric hypothesis of
`absolute_off_diagonal_reassembly_from_eLpNorm` is replaced by the summability of the band
coefficients; this is what the union construction of §7 produces. -/
theorem absolute_off_diagonal_reassembly_of_summable
    {d : ℕ} {p q : ℝ} (hd0 : 0 < d) (hp : 0 < p) (hq : 1 ≤ q)
    (E : Set ℝ) (hEpos : E ⊆ Ioi (0 : ℝ))
    (φ : SchwartzMap (Euclidean d) ℂ)
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (CR A : ENNReal) (hCRtop : CR < ⊤) (hAtop : A < ⊤) (a : ℕ → ENNReal)
    (hsum : ∀ N : ℕ, ∑ j ∈ Finset.range N, a j ≤ A)
    (hregular : ∀ f : SchwartzMap (Euclidean d) ℂ,
      MemLp (fractalSphericalMaximalReal d E
        (absoluteCutoffProjection φ 0 f)) (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalSphericalMaximalReal d E
        (absoluteCutoffProjection φ 0 f)) (ENNReal.ofReal q) volume ≤
        CR * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume)
    (hdyadic : ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      MemLp (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass φ hφone hφzero j) f) (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass φ hφone hφzero j) f) (ENNReal.ofReal q) volume ≤
        a j * eLpNorm (f : Euclidean d → ℂ) (ENNReal.ofReal p) volume) :
    HasFractalSphericalStrongType d E p q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqENN : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  set D : ENNReal := CR + A with hDdef
  have hDtop : D < ⊤ := by
    rw [hDdef]
    exact ENNReal.add_lt_top.mpr ⟨hCRtop, hAtop⟩
  set C : ℝ := D.toReal ^ q + 1 with hCdef
  have hC : 0 < C := by
    rw [hCdef]
    positivity
  refine absolute_reassembly_limit_off_diagonal hd0 hp hq0 E hEpos φ hφone C hC ?_
  intro N f
  set I : ℝ := ∫ x : Euclidean d, ‖f x‖ ^ p with hIdef
  have hI : 0 ≤ I := by
    rw [hIdef]
    exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
  set hroot : ENNReal := eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume with hrootdef
  -- the finite bound at level `N`
  set T : ℕ → Euclidean d → ℝ := fun j =>
    fractalDyadicBandpassMaximal d E (absoluteDyadicBandpass φ hφone hφzero j) f with hTdef
  have hTmem : ∀ j, MemLp (T j) (ENNReal.ofReal q) volume := fun j => (hdyadic j f).1
  have hTnorm : ∀ j, eLpNorm (T j) (ENNReal.ofReal q) volume ≤ a j * hroot :=
    fun j => (hdyadic j f).2
  obtain ⟨hSmem, hSnorm⟩ := finite_output_sum_of_bounds hqENN T hTmem
    (fun j => a j * hroot) hTnorm N
  have hSbound : eLpNorm (fun x => ∑ j ∈ Finset.range N, T j x) (ENNReal.ofReal q) volume
      ≤ A * hroot := by
    refine hSnorm.trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul' (hsum N) (le_refl _)
  obtain ⟨hRmem, hRnorm⟩ := hregular f
  set R : Euclidean d → ℝ := fractalSphericalMaximalReal d E
    (absoluteCutoffProjection φ 0 f) with hRdef
  set S : Euclidean d → ℝ := fun x => ∑ j ∈ Finset.range N, T j x with hSdef
  set P : Euclidean d → ℝ := fractalAbsoluteCutoffMaximal d E φ N f with hPdef
  have hR0 : ∀ x, 0 ≤ R x := fun x => ENNReal.toReal_nonneg
  have hT0 : ∀ j x, 0 ≤ T j x := fun j x => ENNReal.toReal_nonneg
  have hS0 : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg fun j _ => hT0 j x
  have hP0 : ∀ x, 0 ≤ P x := fun x => fractalAbsoluteCutoffMaximal_nonneg E φ N f x
  have hRS0 : ∀ x, 0 ≤ R x + S x := fun x => add_nonneg (hR0 x) (hS0 x)
  have hpoint : ∀ x, P x ≤ R x + S x := by
    intro x
    rw [hPdef, hRdef, hSdef, hTdef]
    exact fractalAbsoluteCutoffMaximal_le_low_add_band_sum hd0 E hEpos φ hφone hφzero N f x
  have hPmeas : AEStronglyMeasurable P volume :=
    (measurable_fractalAbsoluteCutoffMaximal E φ N f).aestronglyMeasurable
  have hRS_mem : MemLp (R + S) (ENNReal.ofReal q) volume := hRmem.add hSmem
  have hPmem : MemLp P (ENNReal.ofReal q) volume := by
    refine hRS_mem.mono hPmeas ?_
    filter_upwards with x
    change ‖P x‖ ≤ ‖R x + S x‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x), Real.norm_eq_abs, abs_of_nonneg (hRS0 x)]
    exact hpoint x
  have hPnorm : eLpNorm P (ENNReal.ofReal q) volume ≤ D * hroot := by
    calc eLpNorm P (ENNReal.ofReal q) volume
        ≤ eLpNorm (R + S) (ENNReal.ofReal q) volume := by
          refine eLpNorm_mono ?_
          intro x
          change ‖P x‖ ≤ ‖R x + S x‖
          rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x), Real.norm_eq_abs,
            abs_of_nonneg (hRS0 x)]
          exact hpoint x
      _ ≤ eLpNorm R (ENNReal.ofReal q) volume + eLpNorm S (ENNReal.ofReal q) volume :=
          eLpNorm_add_le hRmem.1 hSmem.1 hqENN
      _ ≤ CR * hroot + A * hroot := add_le_add hRnorm hSbound
      _ = D * hroot := by rw [hDdef]; ring
  refine ⟨hPmem, ?_⟩
  calc (∫ x : Euclidean d, (fractalAbsoluteCutoffMaximal d E φ N f x) ^ q)
      ≤ D.toReal ^ q * I ^ (q / p) := by
        rw [hIdef]
        exact off_diagonal_moment_bound_of_eLpNorm hp hq0 P hPmem hP0 f D hDtop.ne hPnorm
    _ ≤ C * I ^ (q / p) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hI _)
        rw [hCdef]
        linarith

open MeasureTheory Set ENNReal
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-! ### Finite unions of radius sets at the band level -/

/-- The band maximal operator over a finite union is dominated by the sum over the pieces. -/
theorem fractalDyadicBandpassMaximal_biUnion_le {d : ℕ} (hd : 0 < d) (S : Finset ℕ)
    (A : ℕ → Set ℝ) (hA : ∀ n, A n ⊆ Ioi (0 : ℝ))
    (psi f : SchwartzMap (Euclidean d) ℂ) (x : Euclidean d) :
    fractalDyadicBandpassMaximal d (⋃ n ∈ S, A n) psi f x
      ≤ ∑ n ∈ S, fractalDyadicBandpassMaximal d (A n) psi f x := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty,
        Finset.sum_empty]
      have hzero : fractalDyadicBandpassMaximal d (∅ : Set ℝ) psi f x = 0 := by
        rw [fractalDyadicBandpassMaximal, fractalSphericalMaximalReal,
          fractalSphericalMaximal_empty]
        simp
      rw [hzero]
  | insert n S hn ih =>
      have hsplit : (⋃ m ∈ insert n S, A m) = A n ∪ (⋃ m ∈ S, A m) := by
        rw [Finset.set_biUnion_insert]
      rw [hsplit, Finset.sum_insert hn]
      have hsub1 : A n ⊆ Ioi (0 : ℝ) := hA n
      have hsub2 : (⋃ m ∈ S, A m) ⊆ Ioi (0 : ℝ) := by
        intro t ht
        obtain ⟨m, hm, htm⟩ := Set.mem_iUnion₂.mp ht
        exact hA m htm
      have hstep := fractalSphericalMaximalReal_union_le hd hsub1 hsub2
        (dyadicBandpassProjection psi f) x
      calc fractalDyadicBandpassMaximal d (A n ∪ (⋃ m ∈ S, A m)) psi f x
          ≤ fractalDyadicBandpassMaximal d (A n) psi f x
            + fractalDyadicBandpassMaximal d (⋃ m ∈ S, A m) psi f x := hstep
        _ ≤ fractalDyadicBandpassMaximal d (A n) psi f x
            + ∑ m ∈ S, fractalDyadicBandpassMaximal d (A m) psi f x :=
            add_le_add_right ih (fractalDyadicBandpassMaximal d (A n) psi f x)

/-- The `L^q` norm of the band maximal operator over a countable union of pieces, each confined
to `[1, 1 + 2^{-L n}]`, splits into the resolved pieces and one cell. -/
theorem eLpNorm_bandMaximal_iUnion_le {d : ℕ} (hd : 0 < d) {q : ℝ} (hq : 1 ≤ q)
    {Es : ℕ → Set ℝ} (hEs : ∀ n, Es n ⊆ Icc (1 : ℝ) 2) {L : ℕ → ℕ} (hL : ∀ n, n ≤ L n)
    (hloc : ∀ n, Es n ⊆ Icc (1 : ℝ) (1 + ((2 : ℝ) ^ L n)⁻¹))
    (psi f : SchwartzMap (Euclidean d) ℂ) (j : ℕ) :
    eLpNorm (fractalDyadicBandpassMaximal d (⋃ n, Es n) psi f) (ENNReal.ofReal q) volume
      ≤ (∑ n ∈ (Finset.range j).filter (fun n => L n < j),
          eLpNorm (fractalDyadicBandpassMaximal d (Es n) psi f) (ENNReal.ofReal q) volume)
        + eLpNorm (fractalDyadicBandpassMaximal d
            ((⋃ n, Es n) ∩ Icc (1 : ℝ) (1 + ((2 : ℝ) ^ j)⁻¹)) psi f)
            (ENNReal.ofReal q) volume := by
  classical
  have hqENN : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  set S : Finset ℕ := (Finset.range j).filter (fun n => L n < j) with hSdef
  set U : Set ℝ := ⋃ n, Es n with hUdef
  set V : Set ℝ := U ∩ Icc (1 : ℝ) (1 + ((2 : ℝ) ^ j)⁻¹) with hVdef
  have hEpos : ∀ n, Es n ⊆ Ioi (0 : ℝ) := fun n t ht =>
    lt_of_lt_of_le zero_lt_one (hEs n ht).1
  have hUpos : U ⊆ Ioi (0 : ℝ) := by
    intro t ht
    obtain ⟨n, htn⟩ := Set.mem_iUnion.mp ht
    exact hEpos n htn
  have hVpos : V ⊆ Ioi (0 : ℝ) := fun t ht => hUpos ht.1
  -- the covering of the radius set
  have hcover : U ⊆ (⋃ n ∈ S, Es n) ∪ V := by
    intro t ht
    obtain ⟨n, htn⟩ := Set.mem_iUnion.mp ht
    by_cases hcase : n ∈ S
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨n, hcase, htn⟩)
    · refine Or.inr ⟨ht, ?_⟩
      have hjL : j ≤ L n := by
        rw [hSdef, Finset.mem_filter, Finset.mem_range] at hcase
        by_contra hlt
        push_neg at hlt
        exact hcase ⟨lt_of_le_of_lt (hL n) (lt_of_not_ge (fun h => absurd hlt (not_lt.mpr h))),
          hlt⟩
      obtain ⟨h1, h2⟩ := hloc n htn
      refine ⟨h1, le_trans h2 ?_⟩
      have hmono : ((2 : ℝ) ^ L n)⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ := by
        refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
        exact pow_le_pow_right₀ (by norm_num) hjL
      linarith
  set G : Euclidean d → ℝ := ∑ n ∈ S, fractalDyadicBandpassMaximal d (Es n) psi f with hGdef
  have hGapply : ∀ x, G x = ∑ n ∈ S, fractalDyadicBandpassMaximal d (Es n) psi f x := by
    intro x
    rw [hGdef]
    exact Finset.sum_apply x S _
  -- the pointwise bound
  have hpoint : ∀ x, fractalDyadicBandpassMaximal d U psi f x
      ≤ G x + fractalDyadicBandpassMaximal d V psi f x := by
    intro x
    have hmono := fractalDyadicBandpassMaximal_mono hd hcover
      (Set.union_subset (fun t ht => by
        obtain ⟨n, hn, htn⟩ := Set.mem_iUnion₂.mp ht
        exact hEpos n htn) hVpos) psi f x
    refine hmono.trans ?_
    have hstep : fractalDyadicBandpassMaximal d ((⋃ n ∈ S, Es n) ∪ V) psi f x
        ≤ fractalDyadicBandpassMaximal d (⋃ n ∈ S, Es n) psi f x
          + fractalDyadicBandpassMaximal d V psi f x :=
      fractalSphericalMaximalReal_union_le hd
        (show (⋃ n ∈ S, Es n) ⊆ Ioi (0:ℝ) from fun t ht => by
          obtain ⟨n, hn, htn⟩ := Set.mem_iUnion₂.mp ht
          exact hEpos n htn) hVpos (dyadicBandpassProjection psi f) x
    refine hstep.trans ?_
    rw [hGapply x]
    exact add_le_add_left
      (fractalDyadicBandpassMaximal_biUnion_le hd S Es hEpos psi f x) _
  -- pass to the norms
  have hmeasV : AEStronglyMeasurable (fractalDyadicBandpassMaximal d V psi f) volume :=
    (measurable_fractalDyadicBandpassMaximal V psi f).aestronglyMeasurable
  have hmeasS : AEStronglyMeasurable G volume := by
    rw [hGdef]
    refine Finset.aestronglyMeasurable_sum S ?_
    intro n hn
    exact (measurable_fractalDyadicBandpassMaximal (Es n) psi f).aestronglyMeasurable
  calc eLpNorm (fractalDyadicBandpassMaximal d U psi f) (ENNReal.ofReal q) volume
      ≤ eLpNorm (G + fractalDyadicBandpassMaximal d V psi f) (ENNReal.ofReal q) volume := by
        refine eLpNorm_mono ?_
        intro x
        have h0 : 0 ≤ fractalDyadicBandpassMaximal d U psi f x :=
          fractalDyadicBandpassMaximal_nonneg U psi f x
        have hG0 : 0 ≤ G x := by
          rw [hGapply x]
          exact Finset.sum_nonneg fun n _ => fractalDyadicBandpassMaximal_nonneg (Es n) psi f x
        have h1 : 0 ≤ (G + fractalDyadicBandpassMaximal d V psi f) x := by
          change 0 ≤ G x + fractalDyadicBandpassMaximal d V psi f x
          exact add_nonneg hG0 (fractalDyadicBandpassMaximal_nonneg V psi f x)
        rw [Real.norm_eq_abs, abs_of_nonneg h0, Real.norm_eq_abs, abs_of_nonneg h1]
        exact hpoint x
    _ ≤ eLpNorm G (ENNReal.ofReal q) volume
        + eLpNorm (fractalDyadicBandpassMaximal d V psi f) (ENNReal.ofReal q) volume :=
        eLpNorm_add_le hmeasS hmeasV hqENN
    _ ≤ (∑ n ∈ S, eLpNorm (fractalDyadicBandpassMaximal d (Es n) psi f)
          (ENNReal.ofReal q) volume)
        + eLpNorm (fractalDyadicBandpassMaximal d V psi f) (ENNReal.ofReal q) volume := by
        refine add_le_add_left ?_ _
        rw [hGdef]
        exact eLpNorm_sum_le (fun n _ =>
          (measurable_fractalDyadicBandpassMaximal (Es n) psi f).aestronglyMeasurable) hqENN

open MeasureTheory Set ENNReal



/-! ### A double geometric sum -/

/-- The partial sums of a geometric tail. -/
theorem sum_geometric_tail_eq {rho : ℝ} (hrho1 : rho < 1) (m : ℕ) :
    ∀ N : ℕ, m + 1 ≤ N →
      ∑ j ∈ (Finset.range N).filter (fun j => m < j), rho ^ j
        = (rho ^ (m + 1) - rho ^ N) / (1 - rho) := by
  have hone : (0 : ℝ) < 1 - rho := by linarith
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
      have hempty : (Finset.range (m + 1)).filter (fun j => m < j) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
        intro h
        omega
      rw [hempty, Finset.sum_empty]
      field_simp
      ring
  | succ N hN ih =>
      have hfilter : (Finset.range (N + 1)).filter (fun j => m < j)
          = insert N ((Finset.range N).filter (fun j => m < j)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
        constructor
        · rintro ⟨hj, hmj⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
          · exact Or.inr ⟨h, hmj⟩
          · exact Or.inl h
        · rintro (rfl | ⟨hj, hmj⟩)
          · exact ⟨Nat.lt_succ_self _, by omega⟩
          · exact ⟨Nat.lt_succ_of_lt hj, hmj⟩
      have hnotmem : N ∉ (Finset.range N).filter (fun j => m < j) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        intro h
        exact absurd h.1 (lt_irrefl N)
      rw [hfilter, Finset.sum_insert hnotmem, ih]
      field_simp
      ring

/-- The geometric tail bound. -/
theorem sum_geometric_tail_le {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (m N : ℕ) :
    ∑ j ∈ (Finset.range N).filter (fun j => m < j), C * rho ^ j
      ≤ C * rho ^ (m + 1) / (1 - rho) := by
  have hone : (0 : ℝ) < 1 - rho := by linarith
  rw [← Finset.mul_sum]
  rcases le_or_gt (m + 1) N with hN | hN
  · rw [sum_geometric_tail_eq hrho1 m N hN]
    rw [mul_div_assoc'] at *
    rw [div_le_div_iff_of_pos_right hone]
    have hpow : 0 ≤ rho ^ N := pow_nonneg hrho N
    nlinarith [mul_nonneg hC hpow]
  · have hempty : (Finset.range N).filter (fun j => m < j) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      intro h
      omega
    rw [hempty, Finset.sum_empty, mul_zero]
    positivity

/-- **Exchanging the order of summation in the double sum of §7.** -/
theorem sum_double_geometric_le {Cs rhos : ℕ → ℝ} {L : ℕ → ℕ} (hCs : ∀ n, 0 ≤ Cs n)
    (hrhos : ∀ n, 0 ≤ rhos n) (hrhos1 : ∀ n, rhos n < 1) {A0 : ℝ}
    (hA0 : ∀ N, ∑ n ∈ Finset.range N, Cs n * rhos n ^ (L n + 1) / (1 - rhos n) ≤ A0)
    (N : ℕ) :
    ∑ j ∈ Finset.range N, ∑ n ∈ (Finset.range j).filter (fun n => L n < j),
        Cs n * rhos n ^ j ≤ A0 := by
  classical
  have hle : ∀ j ∈ Finset.range N,
      ∑ n ∈ (Finset.range j).filter (fun n => L n < j), Cs n * rhos n ^ j
        ≤ ∑ n ∈ Finset.range N, (if L n < j then Cs n * rhos n ^ j else 0) := by
    intro j hj
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨lt_trans hn.1 (Finset.mem_range.mp hj), hn.2⟩
    · intro n _ _
      have := hCs n
      have := hrhos n
      positivity
  calc ∑ j ∈ Finset.range N, ∑ n ∈ (Finset.range j).filter (fun n => L n < j),
        Cs n * rhos n ^ j
      ≤ ∑ j ∈ Finset.range N, ∑ n ∈ Finset.range N,
          (if L n < j then Cs n * rhos n ^ j else 0) := Finset.sum_le_sum hle
    _ = ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (if L n < j then Cs n * rhos n ^ j else 0) := Finset.sum_comm
    _ = ∑ n ∈ Finset.range N, ∑ j ∈ (Finset.range N).filter (fun j => L n < j),
          Cs n * rhos n ^ j := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_filter]
    _ ≤ ∑ n ∈ Finset.range N, Cs n * rhos n ^ (L n + 1) / (1 - rhos n) := by
        refine Finset.sum_le_sum fun n _ => ?_
        exact sum_geometric_tail_le (hCs n) (hrhos n) (hrhos1 n) (L n) N
    _ ≤ A0 := hA0 N

open MeasureTheory Set ENNReal
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds



set_option maxHeartbeats 1000000 in
/-- **The union estimate of §7.**  A countable family of radius sets, the `n`-th one confined to
`[1, 1 + 2^{-L n}]` and obeying a band rate at `(p,q)`, together with the one-cell rate at
`(p,q)`, gives the strong type for the union as soon as the diagonal series converges. -/
theorem hasFractalSphericalStrongType_iUnion_of_bandRates {d : ℕ} (hd : 2 ≤ d)
    {Es : ℕ → Set ℝ} (hEs : ∀ n, Es n ⊆ Icc (1 : ℝ) 2)
    {L : ℕ → ℕ} (hL : ∀ n, n ≤ L n)
    (hloc : ∀ n, Es n ⊆ Icc (1 : ℝ) (1 + ((2 : ℝ) ^ L n)⁻¹))
    (phi : SchwartzMap (Euclidean d) ℂ)
    (hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi : Euclidean d, ‖phi xi‖ ≤ 1)
    {p q : ℝ} (hp : 1 < p) (hpq : p < q)
    {Cs rhos : ℕ → ℝ} (hCs : ∀ n, 0 ≤ Cs n) (hrhos : ∀ n, 0 ≤ rhos n)
    (hrhos1 : ∀ n, rhos n < 1)
    (hrates : ∀ (n j : ℕ), 1 ≤ j → ∀ f : SchwartzMap (Euclidean d) ℂ,
      eLpNorm (fractalDyadicBandpassMaximal d (Es n)
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume
        ≤ ENNReal.ofReal (Cs n * rhos n ^ j)
          * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume)
    (hcell : HasOneCellBandRateReal phi hphiOne hphiZero p q)
    {A0 : ℝ}
    (hA0 : ∀ N : ℕ, ∑ n ∈ Finset.range N, Cs n * rhos n ^ (L n + 1) / (1 - rhos n) ≤ A0) :
    HasFractalSphericalStrongType d (⋃ n, Es n) p q := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq1 : 1 ≤ q := le_of_lt (lt_trans hp hpq)
  set E : Set ℝ := ⋃ n, Es n with hEdef
  have hE : E ⊆ Icc (1 : ℝ) 2 := by
    intro t ht
    obtain ⟨n, htn⟩ := Set.mem_iUnion.mp ht
    exact hEs n htn
  have hEpos : E ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le zero_lt_one (hE ht).1
  obtain ⟨Ccell, rhocell, hCcell, hrhocell, hrhocell1, hcellbound⟩ := hcell
  -- the low-frequency and the zeroth band
  obtain ⟨CR, hCRtop, hregular⟩ :=
    absolute_lowpass_improving_eLpNorm hd0 E hE phi hphiZero hphiNorm hp hpq
  have hdisj : 3 ≤ d ∨ d = 2 ∧ (0 : ℝ) ≤ 1 / 2 := by
    rcases Nat.lt_or_ge d 3 with hd3 | hd3
    · exact Or.inr ⟨by omega, by norm_num⟩
    · exact Or.inl hd3
  obtain ⟨Czero, hCzerotop, hzero⟩ := absoluteDyadicBandpass_zero_improving_eLpNorm
    (gamma := 0) hdisj E hE phi hphiOne hphiZero hphiNorm hp hpq
  -- the band coefficients
  set b : ℕ → ℝ := fun j =>
    (∑ n ∈ (Finset.range j).filter (fun n => L n < j), Cs n * rhos n ^ j)
      + Ccell * rhocell ^ j with hbdef
  have hb0 : ∀ j, 0 ≤ b j := by
    intro j
    rw [hbdef]
    have h1 : 0 ≤ ∑ n ∈ (Finset.range j).filter (fun n => L n < j), Cs n * rhos n ^ j := by
      refine Finset.sum_nonneg fun n _ => ?_
      have := hCs n
      have := hrhos n
      positivity
    have h2 : 0 ≤ Ccell * rhocell ^ j := by positivity
    linarith
  set a : ℕ → ENNReal := fun j => if j = 0 then Czero else ENNReal.ofReal (b j) with hadef
  -- the band bounds
  have hdyadic : ∀ (j : ℕ) (f : SchwartzMap (Euclidean d) ℂ),
      MemLp (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume
        ≤ a j * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume := by
    intro j f
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      obtain ⟨hmem, hbd⟩ := hzero f
      refine ⟨hmem, ?_⟩
      rw [hadef]
      simpa using hbd
    · -- the split
      have hsplit := eLpNorm_bandMaximal_iUnion_le hd0 hq1 hEs hL hloc
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f j
      rw [← hEdef] at hsplit
      -- the resolved pieces
      have hpieces : (∑ n ∈ (Finset.range j).filter (fun n => L n < j),
          eLpNorm (fractalDyadicBandpassMaximal d (Es n)
            (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume)
          ≤ ENNReal.ofReal (∑ n ∈ (Finset.range j).filter (fun n => L n < j),
              Cs n * rhos n ^ j)
            * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by
          have := hCs n
          have := hrhos n
          positivity), Finset.sum_mul]
        exact Finset.sum_le_sum fun n _ => hrates n j hj1 f
      -- the tail cell
      have hcelltail : eLpNorm (fractalDyadicBandpassMaximal d
          (E ∩ Icc (1 : ℝ) (1 + ((2 : ℝ) ^ j)⁻¹))
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume
          ≤ ENNReal.ofReal (Ccell * rhocell ^ j)
            * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume := by
        rcases Set.eq_empty_or_nonempty (E ∩ Icc (1 : ℝ) (1 + ((2 : ℝ) ^ j)⁻¹)) with hempty | hne
        · rw [hempty]
          have hzeroband : fractalDyadicBandpassMaximal d (∅ : Set ℝ)
              (absoluteDyadicBandpass phi hphiOne hphiZero j) f = fun _ => 0 := by
            funext x
            rw [fractalDyadicBandpassMaximal, fractalSphericalMaximalReal,
              fractalSphericalMaximal_empty]
            simp
          rw [hzeroband]
          simp
        · refine hcellbound j hj1 (fun t ht => hE ht.1) hne
            (fun t ht => ht.2) ?_ f
          have : (1 : ℝ) + ((2 : ℝ) ^ j)⁻¹ - 1 = ((2 : ℝ) ^ j)⁻¹ := by ring
          rw [this]
      have hjne : ¬ (j = 0) := by omega
      have hfinal : eLpNorm (fractalDyadicBandpassMaximal d E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume
          ≤ a j * eLpNorm ((f : Euclidean d → ℂ)) (ENNReal.ofReal p) volume := by
        refine hsplit.trans ((add_le_add hpieces hcelltail).trans ?_)
        rw [hadef]
        simp only [hjne, if_false]
        rw [← add_mul, ← ENNReal.ofReal_add (by
          refine Finset.sum_nonneg fun n _ => ?_
          have := hCs n
          have := hrhos n
          positivity) (by positivity)]
      refine ⟨⟨(measurable_fractalDyadicBandpassMaximal E _ f).aestronglyMeasurable, ?_⟩, hfinal⟩
      refine lt_of_le_of_lt hfinal ?_
      refine ENNReal.mul_lt_top ?_
        (lt_top_iff_ne_top.mpr (eLpNorm_schwartz_ne_top hp0 f))
      rw [hadef]
      simp only [hjne, if_false]
      exact ENNReal.ofReal_lt_top
  -- the summability of the coefficients
  have hgeomcell : ∀ N : ℕ, ∑ j ∈ Finset.range N, Ccell * rhocell ^ j
      ≤ Ccell / (1 - rhocell) := by
    intro N
    have hone : (0 : ℝ) < 1 - rhocell := by linarith
    rw [← Finset.mul_sum]
    have hgeom : ∑ j ∈ Finset.range N, rhocell ^ j ≤ 1 / (1 - rhocell) := by
      rw [geom_sum_eq (by linarith) N]
      have hrewrite : (rhocell ^ N - 1) / (rhocell - 1) = (1 - rhocell ^ N) / (1 - rhocell) := by
        rw [div_eq_div_iff (by linarith : rhocell - 1 ≠ 0) (ne_of_gt hone)]
        ring
      rw [hrewrite, div_le_div_iff_of_pos_right hone]
      nlinarith [pow_nonneg hrhocell.le N]
    calc Ccell * ∑ j ∈ Finset.range N, rhocell ^ j
        ≤ Ccell * (1 / (1 - rhocell)) := mul_le_mul_of_nonneg_left hgeom hCcell.le
      _ = Ccell / (1 - rhocell) := by ring
  have hbsum : ∀ N : ℕ, ∑ j ∈ Finset.range N, b j ≤ A0 + Ccell / (1 - rhocell) := by
    intro N
    have hsplit : ∑ j ∈ Finset.range N, b j
        = (∑ j ∈ Finset.range N, ∑ n ∈ (Finset.range j).filter (fun n => L n < j),
            Cs n * rhos n ^ j) + ∑ j ∈ Finset.range N, Ccell * rhocell ^ j := by
      rw [hbdef, ← Finset.sum_add_distrib]
    rw [hsplit]
    exact add_le_add (sum_double_geometric_le hCs hrhos hrhos1 hA0 N) (hgeomcell N)
  have hsum : ∀ N : ℕ, ∑ j ∈ Finset.range N, a j
      ≤ Czero + ENNReal.ofReal (A0 + Ccell / (1 - rhocell)) := by
    intro N
    have hstep : ∀ j ∈ Finset.range N,
        a j ≤ (if j = 0 then Czero else 0) + ENNReal.ofReal (b j) := by
      intro j _
      rw [hadef]
      by_cases hj : j = 0
      · simp only [hj, if_true]
        exact le_add_of_nonneg_right bot_le
      · simp only [hj, if_false]
        exact le_add_of_nonneg_left bot_le
    calc ∑ j ∈ Finset.range N, a j
        ≤ ∑ j ∈ Finset.range N, ((if j = 0 then Czero else 0) + ENNReal.ofReal (b j)) :=
          Finset.sum_le_sum hstep
      _ = (∑ j ∈ Finset.range N, (if j = 0 then Czero else 0))
          + ∑ j ∈ Finset.range N, ENNReal.ofReal (b j) := Finset.sum_add_distrib
      _ ≤ Czero + ENNReal.ofReal (A0 + Ccell / (1 - rhocell)) := by
          refine add_le_add ?_ ?_
          · rcases Nat.eq_zero_or_pos N with rfl | hN
            · simp
            · rw [Finset.sum_ite_eq' (Finset.range N) 0 (fun _ => Czero)]
              split_ifs <;> simp
          · rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hb0 j)]
            exact ENNReal.ofReal_le_ofReal (hbsum N)
  exact absolute_off_diagonal_reassembly_of_summable hd0 hp0 hq1 E hEpos phi hphiOne hphiZero
    CR (Czero + ENNReal.ofReal (A0 + Ccell / (1 - rhocell))) hCRtop
    (ENNReal.add_lt_top.mpr ⟨hCzerotop, ENNReal.ofReal_lt_top⟩) a hsum hregular hdyadic

open MeasureTheory Set ENNReal
open Auto.FractalDimensions
open Auto.FractalDimensions
/-! ### Self-similarity of the Cantor construction -/

/-- Every generation of the Cantor construction is affine equivariant. -/
theorem cantorGen_image_affine (mu : ℝ) (m : ℕ) {c s : ℝ} (hs : 0 < s) :
    ∀ v L : ℝ, (fun x => c + s * x) '' cantorGen mu m v L
      = cantorGen mu m (c + s * v) (s * L) := by
  induction m with
  | zero =>
      intro v L
      rw [cantorGen_zero, cantorGen_zero]
      ext x
      simp only [Set.mem_image, Set.mem_Icc]
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        exact ⟨by nlinarith, by nlinarith⟩
      · rintro ⟨h1, h2⟩
        refine ⟨(x - c) / s, ⟨?_, ?_⟩, by field_simp; ring⟩
        · rw [le_div_iff₀ hs]
          linarith
        · rw [div_le_iff₀ hs]
          linarith
  | succ m ih =>
      intro v L
      rw [cantorGen_succ, cantorGen_succ, Set.image_union, ih, ih]
      congr 2 <;> ring

/-- The Cantor set is affine equivariant. -/
theorem cantorSet_image_affine (mu : ℝ) {c s : ℝ} (hs : 0 < s) (v L : ℝ) :
    (fun x => c + s * x) '' cantorSet mu v L = cantorSet mu (c + s * v) (s * L) := by
  have hinj : Function.Injective (fun x : ℝ => c + s * x) := by
    intro x y hxy
    simp only at hxy
    have : s * x = s * y := by linarith
    exact mul_left_cancel₀ (ne_of_gt hs) this
  rw [cantorSet, cantorSet]
  ext x
  simp only [Set.mem_image, Set.mem_iInter]
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro m
    have := hy m
    rw [← cantorGen_image_affine mu m hs v L]
    exact ⟨y, this, rfl⟩
  · intro hx
    -- the preimage point
    refine ⟨(x - c) / s, ?_, by field_simp; ring⟩
    intro m
    have hxm := hx m
    rw [← cantorGen_image_affine mu m hs v L] at hxm
    obtain ⟨y, hy, hxy⟩ := hxm
    have hyx : y = (x - c) / s := by
      simp only at hxy
      field_simp
      linarith
    rw [← hyx]
    exact hy

open MeasureTheory Set ENNReal
open Auto.FractalDimensions
open Auto.FractalDimensions
/-! ### Adding finitely many radii changes no covering exponent -/

theorem isIntervalCover_union_finset {F : Set ℝ} {δ : ℝ} (hδ : 0 < δ) {ι S : Finset ℝ}
    (h : IsIntervalCover F δ ι) :
    IsIntervalCover (F ∪ (↑S : Set ℝ)) δ (ι ∪ S) := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨a, ha, hax⟩ := Set.mem_iUnion₂.mp (h hx)
    exact Set.mem_iUnion₂.mpr ⟨a, Finset.mem_union_left _ ha, hax⟩
  · refine Set.mem_iUnion₂.mpr ⟨x, Finset.mem_union_right _ hx, ?_, ?_⟩ <;> linarith

theorem hasUpperMinkowskiExponent_union_finset {F : Set ℝ} {S : Finset ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (h : HasUpperMinkowskiExponent F β) :
    HasUpperMinkowskiExponent (F ∪ (↑S : Set ℝ)) β := by
  intro ε hε
  obtain ⟨C, hC, hcov⟩ := h ε hε
  refine ⟨C + (S.card : ℝ), by positivity, ?_⟩
  intro δ hδ hδone
  obtain ⟨ι, hcover, hcard⟩ := hcov δ hδ hδone
  refine ⟨ι ∪ S, isIntervalCover_union_finset hδ hcover, ?_⟩
  have hpow : (1 : ℝ) ≤ δ ^ (-(β + ε)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδone.le (by linarith)
  have hcardle : (((ι ∪ S).card : ℝ)) ≤ (ι.card : ℝ) + (S.card : ℝ) := by
    have := Finset.card_union_le ι S
    exact_mod_cast this
  calc (((ι ∪ S).card : ℝ)) ≤ (ι.card : ℝ) + (S.card : ℝ) := hcardle
    _ ≤ C * δ ^ (-(β + ε)) + (S.card : ℝ) * δ ^ (-(β + ε)) := by
        refine add_le_add hcard ?_
        calc (S.card : ℝ) = (S.card : ℝ) * 1 := by ring
          _ ≤ (S.card : ℝ) * δ ^ (-(β + ε)) := by
              refine mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
    _ = (C + (S.card : ℝ)) * δ ^ (-(β + ε)) := by ring

theorem hasUpperAssouadSpectrumExponent_union_finset {F : Set ℝ} {S : Finset ℝ} {θ γ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hγ : 0 ≤ γ)
    (h : HasUpperAssouadSpectrumExponent F θ γ) :
    HasUpperAssouadSpectrumExponent (F ∪ (↑S : Set ℝ)) θ γ := by
  obtain ⟨C, hC, hcov⟩ := h
  refine ⟨C + (S.card : ℝ), by positivity, ?_⟩
  intro δ a b hδ hδone ha hab hb hscale
  obtain ⟨ι, hcover, hcard⟩ := hcov δ a b hδ hδone ha hab hb hscale
  refine ⟨ι ∪ S, ?_, ?_⟩
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rcases hx1 with hx1 | hx1
    · obtain ⟨c, hc, hcx⟩ := Set.mem_iUnion₂.mp (hcover ⟨hx1, hx2⟩)
      exact Set.mem_iUnion₂.mpr ⟨c, Finset.mem_union_left _ hc, hcx⟩
    · refine Set.mem_iUnion₂.mpr ⟨x, Finset.mem_union_right _ hx1, ?_, ?_⟩ <;> linarith
  · have hratio : (1 : ℝ) ≤ (b - a) / δ := by
      rw [le_div_iff₀ hδ]
      have hδθ : δ ≤ δ ^ θ := by
        calc δ = δ ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ ≤ δ ^ θ := Real.rpow_le_rpow_of_exponent_ge hδ hδone.le hθ1
      linarith
    have hpow : (1 : ℝ) ≤ ((b - a) / δ) ^ γ := Real.one_le_rpow hratio hγ
    have hcardle : (((ι ∪ S).card : ℝ)) ≤ (ι.card : ℝ) + (S.card : ℝ) := by
      have := Finset.card_union_le ι S
      exact_mod_cast this
    calc (((ι ∪ S).card : ℝ)) ≤ (ι.card : ℝ) + (S.card : ℝ) := hcardle
      _ ≤ C * ((b - a) / δ) ^ γ + (S.card : ℝ) * ((b - a) / δ) ^ γ := by
          refine add_le_add hcard ?_
          calc (S.card : ℝ) = (S.card : ℝ) * 1 := by ring
            _ ≤ (S.card : ℝ) * ((b - a) / δ) ^ γ :=
                mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
      _ = (C + (S.card : ℝ)) * ((b - a) / δ) ^ γ := by ring

/-! ### The tail of the off-diagonal example -/

/-- The tail of the off-diagonal example, consisting of the pieces of index at least `J`. -/
def offDiagTail (beta gam : ℝ) (k0 J : ℕ) : Set ℝ :=
  ⋃ j : ℕ, (↑(offDiagPiece beta gam k0 (J + j)) : Set ℝ)

theorem offDiagTail_subset (beta gam : ℝ) (k0 J : ℕ) :
    offDiagTail beta gam k0 J ⊆ offDiagSet beta gam k0 := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨J + j, hj⟩

theorem offDiagSet_eq_tail_union (beta gam : ℝ) (k0 J : ℕ) :
    offDiagSet beta gam k0
      = offDiagTail beta gam k0 J
        ∪ (↑((Finset.range J).biUnion (fun j => offDiagPiece beta gam k0 j)) : Set ℝ) := by
  ext x
  simp only [offDiagSet, offDiagTail, Set.mem_iUnion, Set.mem_union, Finset.coe_biUnion,
    Finset.mem_range, Finset.mem_coe]
  constructor
  · rintro ⟨j, hj⟩
    rcases lt_or_ge j J with hlt | hge
    · exact Or.inr ⟨j, hlt, hj⟩
    · exact Or.inl ⟨j - J, by rwa [show J + (j - J) = j by omega]⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj, hxj⟩)
    · exact ⟨J + i, hi⟩
    · exact ⟨j, hxj⟩

theorem offDiagTail_subset_Icc {beta gam : ℝ} (hgam : 0 < gam) (hgam1 : gam ≤ 1)
    {k0 : ℕ} (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) (J : ℕ) :
    offDiagTail beta gam k0 J ⊆ Icc (1 : ℝ) (1 + 3 * offDiagLen beta gam k0 J) := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨h1, h2⟩ := offDiagPiece_subset_Icc hgam hgam1 k0 (J + j) x hj
  have hlen := offDiagLen_pos (beta := beta) (gam := gam) k0 (J + j)
  have hmono := offDiagLen_antitone hk0 J (J + j) (by omega)
  exact ⟨by linarith, by linarith⟩

open MeasureTheory Set ENNReal
open Auto.FractalDimensions
open Auto.FractalDimensions
/-! ### The tail of the off-diagonal example is regular -/

theorem hasUpperMinkowskiExponent_offDiagTail {beta gam : ℝ} (hbeta : 0 < beta)
    (hbg : beta < gam) (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) (J : ℕ) :
    HasUpperMinkowskiExponent (offDiagTail beta gam k0 J) beta :=
  HasUpperMinkowskiExponent.mono (offDiagTail_subset beta gam k0 J)
    (hasUpperMinkowskiExponent_offDiagSet hbeta hbg hgam1 hk0pos hk0)

theorem not_hasUpperMinkowskiExponent_offDiagTail {beta gam beta' : ℝ} (hbeta : 0 < beta)
    (hbg : beta < gam) (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hbeta'0 : 0 ≤ beta') (hlt : beta' < beta) (J : ℕ) :
    ¬ HasUpperMinkowskiExponent (offDiagTail beta gam k0 J) beta' := by
  intro h
  have hfull : HasUpperMinkowskiExponent (offDiagSet beta gam k0) beta' := by
    rw [offDiagSet_eq_tail_union beta gam k0 J]
    exact hasUpperMinkowskiExponent_union_finset hbeta'0 h
  exact not_hasUpperMinkowskiExponent_offDiagSet hbeta hbg hgam1 hk0pos hbeta'0 hlt hfull

theorem upperMinkowskiDimension_offDiagTail {beta gam : ℝ} (hbeta : 0 < beta)
    (hbg : beta < gam) (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) (J : ℕ) :
    upperMinkowskiDimension (offDiagTail beta gam k0 J) = beta := by
  refine upperMinkowskiDimension_eq_of_bounds hbeta.le
    (hasUpperMinkowskiExponent_offDiagTail hbeta hbg hgam1 hk0pos hk0 J) ?_
  intro beta' hbeta'0 hlt
  exact not_hasUpperMinkowskiExponent_offDiagTail hbeta hbg hgam1 hk0pos hbeta'0 hlt J

theorem hasUpperAssouadSpectrumExponent_offDiagTail {beta gam : ℝ} (hbeta : 0 < beta)
    (hbg : beta < gam) (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) {θ : ℝ} (hθ1 : θ ≤ 1) (J : ℕ) :
    HasUpperAssouadSpectrumExponent (offDiagTail beta gam k0 J) θ gam :=
  HasUpperAssouadSpectrumExponent.mono (offDiagTail_subset beta gam k0 J)
    (hasUpperAssouadSpectrumExponent_offDiagSet hbeta hbg hgam1 hk0pos hk0 hθ1)

theorem not_hasUpperAssouadSpectrumExponent_offDiagTail {beta gam gam' θ : ℝ}
    (hbeta : 0 < beta) (hbg : beta < gam) (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθ : 1 - beta / gam < θ) (hgam'0 : 0 ≤ gam')
    (hlt : gam' < gam) (J : ℕ) :
    ¬ HasUpperAssouadSpectrumExponent (offDiagTail beta gam k0 J) θ gam' := by
  intro h
  have hfull : HasUpperAssouadSpectrumExponent (offDiagSet beta gam k0) θ gam' := by
    rw [offDiagSet_eq_tail_union beta gam k0 J]
    exact hasUpperAssouadSpectrumExponent_union_finset hθ0 hθ1 hgam'0 h
  exact not_hasUpperAssouadSpectrumExponent_offDiagSet hbeta hbg hgam1 hk0pos hθ hgam'0 hlt hfull

theorem upperAssouadSpectrum_offDiagTail {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : 1 - beta / gam < θ) (hθ1 : θ ≤ 1) (J : ℕ) :
    upperAssouadSpectrum (offDiagTail beta gam k0 J) θ = gam := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  refine upperAssouadSpectrum_eq_of_bounds hgam.le
    (hasUpperAssouadSpectrumExponent_offDiagTail hbeta hbg hgam1 hk0pos hk0 hθ1 J) ?_
  intro gam' hgam'0 hlt
  exact not_hasUpperAssouadSpectrumExponent_offDiagTail hbeta hbg hgam1 hk0pos hθ0 hθ1 hθ
    hgam'0 hlt J

theorem upperAssouadSpectrum_offDiagTail_le {beta gam : ℝ} (hbeta : 0 < beta)
    (hbg : beta < gam) (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) {θ : ℝ} (hθ1 : θ ≤ 1) (J : ℕ) :
    upperAssouadSpectrum (offDiagTail beta gam k0 J) θ ≤ gam := by
  have hgam : 0 < gam := lt_trans hbeta hbg
  refine csInf_le ⟨0, fun g hg => hg.1⟩ ⟨hgam.le, ?_⟩
  exact hasUpperAssouadSpectrumExponent_offDiagTail hbeta hbg hgam1 hk0pos hk0 hθ1 J

theorem quasiAssouadDimension_offDiagTail {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) (J : ℕ) :
    quasiAssouadDimension (offDiagTail beta gam k0 J) = gam := by
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
    exact upperAssouadSpectrum_offDiagTail_le hbeta hbg hgam1 hk0pos hk0 hθ1.le J
  · intro ε hε
    refine ⟨(1 - beta / gam + 1) / 2, by linarith, by linarith, ?_⟩
    rw [upperAssouadSpectrum_offDiagTail hbeta hbg hgam1 hk0pos hk0 (by linarith)
      (by linarith) (by linarith) J]
    linarith

/-- **The tail of the off-diagonal example is `(β,γ)`-quasi-Assouad regular.** -/
theorem isQuasiAssouadRegular_offDiagTail {beta gam : ℝ} (hbeta : 0 < beta) (hbg : beta < gam)
    (hgam1 : gam ≤ 1) {k0 : ℕ} (hk0pos : 1 ≤ k0)
    (hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3) (J : ℕ) :
    IsQuasiAssouadRegular (offDiagTail beta gam k0 J) beta gam := by
  refine ⟨upperMinkowskiDimension_offDiagTail hbeta hbg hgam1 hk0pos hk0 J,
    quasiAssouadDimension_offDiagTail hbeta hbg hgam1 hk0pos hk0 J, Or.inr ?_⟩
  intro θ hθ0 hθ1 hθcrit
  exact upperAssouadSpectrum_offDiagTail hbeta hbg hgam1 hk0pos hk0 hθ0 hθcrit hθ1.le J

open MeasureTheory Set ENNReal
open Auto.FractalDimensions
open Auto.FractalDimensions
/-! ### The left branch of the Cantor construction -/

theorem cantorSet_left_subset {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2) (u : ℝ) {L : ℝ}
    (hL : 0 ≤ L) : cantorSet mu u (mu * L) ⊆ cantorSet mu u L := by
  intro x hx
  rw [cantorSet, Set.mem_iInter] at hx ⊢
  intro m
  have hstep : x ∈ cantorGen mu (m + 1) u L := by
    rw [cantorGen_succ]
    exact Or.inl (hx m)
  exact cantorGen_succ_subset hmu hmu2 m hL hstep

theorem cantorSet_pow_subset {mu : ℝ} (hmu : 0 < mu) (hmu2 : mu ≤ 1 / 2) (u : ℝ) :
    ∀ k : ℕ, cantorSet mu u (mu ^ k) ⊆ cantorSet mu u 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : cantorSet mu u (mu ^ (k + 1)) ⊆ cantorSet mu u (mu ^ k) := by
        have hpow : mu ^ (k + 1) = mu * mu ^ k := by ring
        rw [hpow]
        exact cantorSet_left_subset hmu hmu2 u (pow_nonneg hmu.le k)
      exact hstep.trans ih

/-! ### A regular set with a shrinking family of regular subsets -/

set_option maxHeartbeats 1000000 in
/-- For every admissible pair of dimensions there is a regular set `F ⊆ [1,2]` together with,
for every `m`, a `(β,γ)`-regular subset of `F` contained in `[1, 1 + 2^{-m}]`.  Monotonicity of
the maximal operator then transfers every band rate of `F` to all of these subsets. -/
theorem exists_regular_subset_in_small_interval {beta gam : ℝ} (hbeta : 0 ≤ beta)
    (hbg : beta ≤ gam) (hgam1 : gam ≤ 1) (hzero : beta = 0 → gam = 0) :
    ∃ F : Set ℝ, F ⊆ Icc (1 : ℝ) 2 ∧ F.Nonempty ∧ IsQuasiAssouadRegular F beta gam ∧
      ∀ m : ℕ, ∃ G : Set ℝ, G ⊆ F ∧ G.Nonempty ∧ IsQuasiAssouadRegular G beta gam ∧
        G ⊆ Icc (1 : ℝ) (1 + ((2 : ℝ) ^ m)⁻¹) := by
  rcases eq_or_lt_of_le hbeta with hb0 | hbpos
  · -- the degenerate pair `(0,0)`
    have hg0 : gam = 0 := hzero hb0.symm
    refine ⟨{1}, ?_, ⟨1, rfl⟩, ?_, ?_⟩
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨le_refl _, by norm_num⟩
    · rw [← hb0, hg0]
      exact isQuasiAssouadRegular_singleton 1
    · intro m
      refine ⟨{1}, subset_refl _, ⟨1, rfl⟩, ?_, ?_⟩
      · rw [← hb0, hg0]
        exact isQuasiAssouadRegular_singleton 1
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨le_refl _, ?_⟩
        have : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := by positivity
        linarith
  rcases eq_or_lt_of_le hbg with hbeq | hblt
  · -- the diagonal case: a Cantor set and its left branches
    subst hbeq
    set mu : ℝ := cantorRatio beta with hmudef
    have hmu : 0 < mu := cantorRatio_pos beta
    have hmu2 : mu ≤ 1 / 2 := cantorRatio_le_half hbpos hgam1
    have hmulone : mu < 1 := lt_of_le_of_lt hmu2 (by norm_num)
    refine ⟨cantorSet mu 1 1, cantorSet_subset_Icc_one_two 1 (le_refl _) (by norm_num),
      cantorSet_nonempty hbpos hgam1 1,
      isQuasiAssouadRegular_cantorSet hbpos hgam1 1 (le_refl _) (by norm_num), ?_⟩
    intro m
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < ((2 : ℝ) ^ m)⁻¹ by positivity) hmulone
    refine ⟨cantorSet mu 1 (mu ^ k), cantorSet_pow_subset hmu hmu2 1 k, ?_, ?_, ?_⟩
    · have := cantorSet_nonempty (gam := beta) hbpos hgam1 1
      -- the scaled copy is nonempty because it is an affine image
      have himg : cantorSet mu 1 (mu ^ k)
          = (fun x => (1 - mu ^ k) + mu ^ k * x) '' cantorSet mu 1 1 := by
        have h := cantorSet_image_affine mu (c := 1 - mu ^ k) (s := mu ^ k)
          (by positivity) 1 1
        rw [show (1 : ℝ) - mu ^ k + mu ^ k * 1 = 1 by ring,
          show mu ^ k * (1 : ℝ) = mu ^ k by ring] at h
        exact h.symm
      rw [himg]
      exact this.image _
    · -- regularity of the affine copy
      have himg : cantorSet mu 1 (mu ^ k)
          = (fun x => (1 - mu ^ k) + mu ^ k * x) '' cantorSet mu 1 1 := by
        have h := cantorSet_image_affine mu (c := 1 - mu ^ k) (s := mu ^ k)
          (by positivity) 1 1
        rw [show (1 : ℝ) - mu ^ k + mu ^ k * 1 = 1 by ring,
          show mu ^ k * (1 : ℝ) = mu ^ k by ring] at h
        exact h.symm
      rw [himg]
      refine isQuasiAssouadRegular_image_affine (by positivity)
        (cantorSet_subset_Icc_one_two 1 (le_refl _) (by norm_num)) ?_
        (isQuasiAssouadRegular_cantorSet hbpos hgam1 1 (le_refl _) (by norm_num))
      · -- the image stays in `[1,2]`
        intro x hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨hy1, hy2⟩ := cantorSet_subset_Icc mu 1 1 hy
        have hpow : 0 < mu ^ k := by positivity
        have hpow1 : mu ^ k ≤ 1 := pow_le_one₀ hmu.le hmulone.le
        exact ⟨by nlinarith, by nlinarith⟩
    · -- the left branch sits in a small interval
      intro x hx
      obtain ⟨h1, h2⟩ := cantorSet_subset_Icc mu 1 (mu ^ k) hx
      exact ⟨h1, by linarith [hk.le]⟩
  · -- the off-diagonal case
    have hgam : 0 < gam := lt_trans hbpos hblt
    have hr0 : 0 < offDiagRatio beta gam := offDiagRatio_pos beta gam
    have hr1 : offDiagRatio beta gam < 1 := offDiagRatio_lt_one hbpos hblt
    obtain ⟨k0, hk0lt⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ) < 1 / 3) hr1
    have hk0pos : 1 ≤ k0 := by
      rcases Nat.eq_zero_or_pos k0 with h0 | h
      · rw [h0] at hk0lt
        simp only [pow_zero] at hk0lt
        linarith
      · exact h
    have hk0 : (offDiagRatio beta gam) ^ k0 ≤ 1 / 3 := hk0lt.le
    refine ⟨offDiagSet beta gam k0,
      offDiagSet_subset_Icc hbpos hblt hgam hgam1 k0, offDiagSet_nonempty k0,
      isQuasiAssouadRegular_offDiagSet hbpos hblt hgam1 hk0pos hk0, ?_⟩
    intro m
    -- choose the starting index so that the tail is short
    obtain ⟨J, hJ⟩ := exists_pow_le_of_lt_one
      (show (0:ℝ) < (offDiagRatio beta gam) ^ k0 by positivity)
      (show (offDiagRatio beta gam) ^ k0 < 1 by
        exact lt_of_le_of_lt hk0 (by norm_num))
      (show (0:ℝ) < (3 / 4) * ((2 : ℝ) ^ m)⁻¹ by positivity)
    refine ⟨offDiagTail beta gam k0 J, offDiagTail_subset beta gam k0 J, ?_,
      isQuasiAssouadRegular_offDiagTail hbpos hblt hgam1 hk0pos hk0 J, ?_⟩
    · obtain ⟨x, hx⟩ := cantorMid_nonempty (cantorRatio gam) (k0 * (J + 0))
        (1 + 2 * offDiagLen beta gam k0 (J + 0)) (offDiagLen beta gam k0 (J + 0))
      exact ⟨x, Set.mem_iUnion.mpr ⟨0, hx⟩⟩
    · refine (offDiagTail_subset_Icc hgam hgam1 hk0 J).trans ?_
      intro x hx
      obtain ⟨h1, h2⟩ := hx
      refine ⟨h1, le_trans h2 ?_⟩
      have hlen : offDiagLen beta gam k0 J = (1 / 4) * ((offDiagRatio beta gam) ^ k0) ^ J :=
        offDiagLen_eq_pow k0 J
      have hbound := hJ J (le_refl J)
      rw [hlen]
      nlinarith [hbound]

open MeasureTheory Set ENNReal
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-! ### Band rates are inherited by subsets of the radius set -/

theorem hasAbsoluteBandRate_mono {d : ℕ} (hd : 0 < d) {E F : Set ℝ} (hEF : E ⊆ F)
    (hF : F ⊆ Ioi (0 : ℝ)) {phi : SchwartzMap (Euclidean d) ℂ}
    {hphiOne : ∀ xi : Euclidean d, ‖xi‖ ≤ 1 → phi xi = 1}
    {hphiZero : ∀ xi : Euclidean d, 2 ≤ ‖xi‖ → phi xi = 0} {p q : ℝ} (hp : 0 < p)
    (h : HasAbsoluteBandRate F phi hphiOne hphiZero p q) :
    HasAbsoluteBandRate E phi hphiOne hphiZero p q := by
  obtain ⟨C, rho, hCtop, hrho, hbound⟩ := h
  refine ⟨C, rho, hCtop, hrho, ?_⟩
  intro j hj f
  have hmono : eLpNorm (fractalDyadicBandpassMaximal d E
      (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume
      ≤ eLpNorm (fractalDyadicBandpassMaximal d F
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal q) volume := by
    refine eLpNorm_mono ?_
    intro x
    have h1 : 0 ≤ fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f x :=
      fractalDyadicBandpassMaximal_nonneg E _ f x
    have h2 : 0 ≤ fractalDyadicBandpassMaximal d F
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f x :=
      fractalDyadicBandpassMaximal_nonneg F _ f x
    rw [Real.norm_eq_abs, abs_of_nonneg h1, Real.norm_eq_abs, abs_of_nonneg h2]
    exact fractalDyadicBandpassMaximal_mono hd hEF hF _ f x
  have hfinal := hmono.trans (hbound j hj f).2
  refine ⟨⟨(measurable_fractalDyadicBandpassMaximal E _ f).aestronglyMeasurable, ?_⟩, hfinal⟩
  refine lt_of_le_of_lt hfinal ?_
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top hCtop (ENNReal.pow_lt_top (lt_of_lt_of_le hrho le_top)))
    (lt_top_iff_ne_top.mpr (eLpNorm_schwartz_ne_top hp f))

/-! ### Choosing the depths of the pieces -/

/-- For finitely many geometric rates one can choose a common depth making all of them small. -/
theorem exists_common_depth {n : ℕ} (C rho : ℕ → ℝ) (hC : ∀ k, 0 < C k)
    (hrho : ∀ k, 0 < rho k) (hrho1 : ∀ k, rho k < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ k, k ≤ n → C k * rho k ^ (M + 1) / (1 - rho k) ≤ ε := by
  classical
  have hone : ∀ k, 0 < 1 - rho k := fun k => by linarith [hrho1 k]
  have hstep : ∀ k : ℕ, ∃ M : ℕ, C k * rho k ^ (M + 1) / (1 - rho k) ≤ ε := by
    intro k
    have htarget : 0 < ε * (1 - rho k) / C k := by
      have := hone k
      have := hC k
      positivity
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one htarget (hrho1 k)
    refine ⟨M, ?_⟩
    have hpow : rho k ^ (M + 1) ≤ rho k ^ M :=
      pow_le_pow_of_le_one (hrho k).le (hrho1 k).le (by omega)
    have hkey : C k * rho k ^ (M + 1) ≤ ε * (1 - rho k) := by
      calc C k * rho k ^ (M + 1) ≤ C k * rho k ^ M :=
            mul_le_mul_of_nonneg_left hpow (hC k).le
        _ ≤ C k * (ε * (1 - rho k) / C k) := mul_le_mul_of_nonneg_left hM.le (hC k).le
        _ = ε * (1 - rho k) := by
              have hCk : C k ≠ 0 := ne_of_gt (hC k)
              field_simp
    rw [div_le_iff₀ (hone k)]
    exact hkey
  choose M hM using hstep
  refine ⟨(Finset.range (n + 1)).sup M, ?_⟩
  intro k hk
  have hMk : M k ≤ (Finset.range (n + 1)).sup M :=
    Finset.le_sup (Finset.mem_range.mpr (by omega))
  have hpow : rho k ^ ((Finset.range (n + 1)).sup M + 1) ≤ rho k ^ (M k + 1) :=
    pow_le_pow_of_le_one (hrho k).le (hrho1 k).le (by omega)
  calc C k * rho k ^ ((Finset.range (n + 1)).sup M + 1) / (1 - rho k)
      ≤ C k * rho k ^ (M k + 1) / (1 - rho k) := by
        rw [div_le_div_iff_of_pos_right (hone k)]
        exact mul_le_mul_of_nonneg_left hpow (hC k).le
    _ ≤ ε := hM k

open MeasureTheory Set ENNReal
open Auto.Spherical.SurfaceMeasureDecay
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.AHRSUpperBounds
open Auto.Spherical.FractalDilations.AHRSUpperBounds



/-! ### The exponent data of an interior point -/

/-- The four strict inequalities of an interior point of `Q(β,γ)`, in coordinates. -/
theorem interior_Q_coords {d : ℕ} (hd : 2 ≤ d) {beta gam : ℝ} (hbeta : 0 ≤ beta)
    (hbg : beta ≤ gam) (hgam1 : gam ≤ 1) {x : ExponentPoint}
    (hx : x ∈ interior (Q d beta gam)) :
    0 < x.2 ∧ x.2 < x.1 ∧ x.1 < (d : ℝ) * x.2 ∧ (d : ℝ) * x.1 < x.2 + ((d : ℝ) - 1) := by
  have hbeta1 : beta ≤ 1 := le_trans hbg hgam1
  have hgamnn : (0 : ℝ) ≤ gam := le_trans hbeta hbg
  have hD : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h21 : x.2 < x.1 := strict_second_lt_first_of_mem_interior_Q hd hbeta1 hgamnn hx
  have hcap : x.1 < (d : ℝ) * x.2 :=
    strict_first_lt_natCast_mul_second_of_mem_interior_Q hd hbeta hbeta1 hgamnn hx
  have hann : (d : ℝ) * x.1 < (1 - beta) * x.2 + ((d : ℝ) - 1) :=
    strict_annulus_of_mem_interior_Q hd hbeta hbg hbeta1 hx
  have hpos : 0 < x.2 := by
    nlinarith
  refine ⟨hpos, h21, hcap, ?_⟩
  nlinarith

/-! ### Realizing every interior point of a countable intersection -/

set_option maxHeartbeats 2000000 in
/-- **The construction of §7.**  Given a countable family of admissible exponent pairs and a
sequence of points in the interior of the intersection of the corresponding regions, there is a
single radius set whose type set contains all these points and which contains a regular set for
every member of the family. -/
theorem exists_iUnion_type_points {d : ℕ} (hd : 2 ≤ d)
    {bs gs : ℕ → ℝ} (hbg : ∀ n, 0 ≤ bs n ∧ bs n ≤ gs n ∧ gs n ≤ 1)
    (hdeg : ∀ n, bs n = 0 → gs n = 0)
    (z : ℕ → ExponentPoint)
    (hz : ∀ k, z k ∈ interior (⋂ n, Q d (bs n) (gs n))) :
    ∃ E : Set ℝ, E ⊆ Icc (1 : ℝ) 2 ∧ E.Nonempty ∧
      (∀ n, ∃ G : Set ℝ, G ⊆ E ∧ G.Nonempty ∧ IsQuasiAssouadRegular G (bs n) (gs n)) ∧
      ∀ k, z k ∈ fractalTypeSet d E := by
  classical
  obtain ⟨n0, rfl⟩ : ∃ n : ℕ, d = n + 1 := ⟨d - 1, by omega⟩
  have hn0 : 1 ≤ n0 := by omega
  have hd0 : 0 < n0 + 1 := Nat.succ_pos n0
  obtain ⟨phi, psi, hphiOne, hphiZero, hphiNorm, hphiRadial, hpsi, -⟩ :=
    exists_normRadial_smooth_absolute_dyadic_bandpass_family (n0 + 1)
  -- the regular sets and their shrinking families
  have hfam : ∀ n : ℕ, ∃ F : Set ℝ, F ⊆ Icc (1 : ℝ) 2 ∧ F.Nonempty ∧
      IsQuasiAssouadRegular F (bs n) (gs n) ∧
      ∀ m : ℕ, ∃ G : Set ℝ, G ⊆ F ∧ G.Nonempty ∧ IsQuasiAssouadRegular G (bs n) (gs n) ∧
        G ⊆ Icc (1 : ℝ) (1 + ((2 : ℝ) ^ m)⁻¹) := fun n =>
    exists_regular_subset_in_small_interval (hbg n).1 (hbg n).2.1 (hbg n).2.2 (hdeg n)
  choose F hFsub hFne hFreg hFfam using hfam
  -- the coordinates of the target points
  have hzn : ∀ k n : ℕ, z k ∈ interior (Q (n0 + 1) (bs n) (gs n)) := by
    intro k n
    exact interior_mono (Set.iInter_subset _ n) (hz k)
  have hcoord : ∀ k : ℕ, 0 < (z k).2 ∧ (z k).2 < (z k).1 ∧
      (z k).1 < ((n0 : ℝ) + 1) * (z k).2 ∧
      ((n0 : ℝ) + 1) * (z k).1 < (z k).2 + (n0 : ℝ) := by
    intro k
    obtain ⟨h1, h2, h3, h4⟩ := interior_Q_coords (by omega) (hbg 0).1 (hbg 0).2.1
      (hbg 0).2.2 (hzn k 0)
    have hcast : ((n0 + 1 : ℕ) : ℝ) = (n0 : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h3 h4
    exact ⟨h1, h2, h3, by linarith⟩
  -- the exponents
  set p : ℕ → ℝ := fun k => ((z k).1)⁻¹ with hpdef
  set q : ℕ → ℝ := fun k => ((z k).2)⁻¹ with hqdef
  have hxpos : ∀ k, 0 < (z k).1 := fun k => lt_trans (hcoord k).1 (hcoord k).2.1
  have hx1 : ∀ k, (z k).1 < 1 := by
    intro k
    obtain ⟨h1, h2, h3, h4⟩ := hcoord k
    have hn1 : (1 : ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hn0
    nlinarith
  have hy1 : ∀ k, (z k).2 < 1 := fun k => lt_trans (hcoord k).2.1 (hx1 k)
  have hp1 : ∀ k, 1 < p k := by
    intro k
    rw [hpdef]
    simp only
    rw [one_lt_inv_iff₀]
    exact ⟨hxpos k, hx1 k⟩
  have hpq : ∀ k, p k < q k := by
    intro k
    rw [hpdef, hqdef]
    simp only
    exact (inv_lt_inv₀ (lt_trans (hcoord k).1 (hcoord k).2.1) (hcoord k).1).mpr
      (hcoord k).2.1
  have hzrecip : ∀ k, z k = reciprocalExponentPoint (p k) (q k) := by
    intro k
    rw [reciprocalExponentPoint, hpdef, hqdef]
    simp only [inv_inv]
  -- the band rates of the big sets
  have hrate : ∀ n k : ℕ, ∃ C rho : ℝ, 0 < C ∧ 0 < rho ∧ rho < 1 ∧
      ∀ j : ℕ, 1 ≤ j → ∀ f : SchwartzMap (Euclidean (n0 + 1)) ℂ,
        eLpNorm (fractalDyadicBandpassMaximal (n0 + 1) (F n)
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal (q k)) volume
          ≤ ENNReal.ofReal (C * rho ^ j)
            * eLpNorm ((f : Euclidean (n0 + 1) → ℂ)) (ENNReal.ofReal (p k)) volume := by
    intro n k
    have hregion : reciprocalExponentPoint (p k) (q k)
        ∈ interior (Q (n0 + 1) (bs n) (gs n)) := by
      rw [← hzrecip k]
      exact hzn k n
    obtain ⟨C, rho, hCtop, hrho, hbound⟩ := bandRate_of_mem_interior_Q (by omega)
      (hFsub n) (hbg n).1 (hbg n).2.1 (hbg n).2.2 (hFreg n).1 (hFreg n).2.1
      (lt_trans zero_lt_one (hp1 k)) (le_of_lt (lt_trans (hp1 k) (hpq k)))
      phi psi hphiOne hphiZero hphiNorm hphiRadial hpsi hregion
    obtain ⟨C', rho', hC', hrho', hrho1', hconv⟩ := exists_real_rate_of_ennreal hCtop hrho
    refine ⟨C', rho', hC', hrho', hrho1', ?_⟩
    intro j hj f
    exact (hbound j hj f).2.trans (mul_le_mul' (hconv j) (le_refl _))
  choose C rho hC hrho hrho1 hbound using hrate
  -- the depths
  have hdepth : ∀ n : ℕ, ∃ M : ℕ, ∀ k, k ≤ n →
      C n k * rho n k ^ (M + 1) / (1 - rho n k) ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    exact exists_common_depth (C n) (rho n) (hC n) (hrho n) (hrho1 n) ((1 / 2 : ℝ) ^ n)
      (by positivity)
  choose M hM using hdepth
  set L : ℕ → ℕ := fun n => max n (M n) with hLdef
  have hLn : ∀ n, n ≤ L n := fun n => le_max_left _ _
  have hLM : ∀ n, M n ≤ L n := fun n => le_max_right _ _
  -- the pieces
  have hpieces : ∀ n : ℕ, ∃ G : Set ℝ, G ⊆ F n ∧ G.Nonempty ∧
      IsQuasiAssouadRegular G (bs n) (gs n) ∧
      G ⊆ Icc (1 : ℝ) (1 + ((2 : ℝ) ^ (L n))⁻¹) := fun n => hFfam n (L n)
  choose G hGF hGne hGreg hGloc using hpieces
  have hGsub : ∀ n, G n ⊆ Icc (1 : ℝ) 2 := fun n => (hGF n).trans (hFsub n)
  refine ⟨⋃ n, G n, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨n, htn⟩ := Set.mem_iUnion.mp ht
    exact hGsub n htn
  · obtain ⟨t, ht⟩ := hGne 0
    exact ⟨t, Set.mem_iUnion.mpr ⟨0, ht⟩⟩
  · intro n
    exact ⟨G n, Set.subset_iUnion G n, hGne n, hGreg n⟩
  -- the type points
  intro k
  refine ⟨p k, q k, lt_trans zero_lt_one (hp1 k),
    le_of_lt (lt_trans (hp1 k) (hpq k)), hzrecip k, ?_⟩
  -- the cell rate
  have hcell : HasOneCellBandRateReal phi hphiOne hphiZero (p k) (q k) := by
    obtain ⟨h1, h2, h3, h4⟩ := hcoord k
    have hrate := oneCell_bandRate_of_strict hn0 phi psi hphiOne hphiZero hphiNorm hpsi
      h1 h2 h3 h4
    have hp' : (1 : ℝ) / (z k).1 = p k := by
      rw [hpdef, one_div]
    have hq' : (1 : ℝ) / (z k).2 = q k := by
      rw [hqdef, one_div]
    rw [hp', hq'] at hrate
    exact hrate
  -- the rates of the pieces
  have hratesG : ∀ (n j : ℕ), 1 ≤ j → ∀ f : SchwartzMap (Euclidean (n0 + 1)) ℂ,
      eLpNorm (fractalDyadicBandpassMaximal (n0 + 1) (G n)
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f) (ENNReal.ofReal (q k)) volume
        ≤ ENNReal.ofReal (C n k * rho n k ^ j)
          * eLpNorm ((f : Euclidean (n0 + 1) → ℂ)) (ENNReal.ofReal (p k)) volume := by
    intro n j hj f
    refine le_trans ?_ (hbound n k j hj f)
    refine eLpNorm_mono ?_
    intro x
    have h1 : 0 ≤ fractalDyadicBandpassMaximal (n0 + 1) (G n)
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f x :=
      fractalDyadicBandpassMaximal_nonneg (G n) _ f x
    have h2 : 0 ≤ fractalDyadicBandpassMaximal (n0 + 1) (F n)
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f x :=
      fractalDyadicBandpassMaximal_nonneg (F n) _ f x
    rw [Real.norm_eq_abs, abs_of_nonneg h1, Real.norm_eq_abs, abs_of_nonneg h2]
    exact fractalDyadicBandpassMaximal_mono hd0 (hGF n)
      (fun t ht => lt_of_lt_of_le zero_lt_one (hFsub n ht).1) _ f x
  -- the summability
  have hsummable : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, C n k * rho n k ^ (L n + 1) / (1 - rho n k)
        ≤ (∑ n ∈ Finset.range k, C n k * rho n k ^ (L n + 1) / (1 - rho n k)) + 2 := by
    intro N
    have hterm : ∀ n : ℕ, k ≤ n →
        C n k * rho n k ^ (L n + 1) / (1 - rho n k) ≤ (1 / 2 : ℝ) ^ n := by
      intro n hkn
      have hpow : rho n k ^ (L n + 1) ≤ rho n k ^ (M n + 1) :=
        pow_le_pow_of_le_one (hrho n k).le (hrho1 n k).le
          (by have := hLM n; omega)
      have hone : 0 < 1 - rho n k := by linarith [hrho1 n k]
      calc C n k * rho n k ^ (L n + 1) / (1 - rho n k)
          ≤ C n k * rho n k ^ (M n + 1) / (1 - rho n k) := by
            rw [div_le_div_iff_of_pos_right hone]
            exact mul_le_mul_of_nonneg_left hpow (hC n k).le
        _ ≤ (1 / 2 : ℝ) ^ n := hM n k hkn
    have hnonneg : ∀ n : ℕ, 0 ≤ C n k * rho n k ^ (L n + 1) / (1 - rho n k) := by
      intro n
      have hone : 0 < 1 - rho n k := by linarith [hrho1 n k]
      have := (hC n k).le
      have := (hrho n k).le
      positivity
    rcases le_or_gt N k with hNk | hNk
    · have hsub : Finset.range N ⊆ Finset.range k := Finset.range_subset_range.mpr hNk
      have hmono : ∑ n ∈ Finset.range N, C n k * rho n k ^ (L n + 1) / (1 - rho n k)
          ≤ ∑ n ∈ Finset.range k, C n k * rho n k ^ (L n + 1) / (1 - rho n k) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnonneg n)
      linarith
    · -- split the sum at `k`
      have hsplit : ∑ n ∈ Finset.range N, C n k * rho n k ^ (L n + 1) / (1 - rho n k)
          = (∑ n ∈ Finset.range k, C n k * rho n k ^ (L n + 1) / (1 - rho n k))
            + ∑ n ∈ (Finset.range N).filter (fun n => k ≤ n),
                C n k * rho n k ^ (L n + 1) / (1 - rho n k) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun n => k ≤ n)]
        have hfilter : (Finset.range N).filter (fun n => ¬ k ≤ n) = Finset.range k := by
          ext n
          simp only [Finset.mem_filter, Finset.mem_range, not_le]
          constructor
          · rintro ⟨-, h⟩
            exact h
          · intro h
            exact ⟨by omega, h⟩
        rw [hfilter]
        ring
      rw [hsplit]
      refine add_le_add_right ?_ _
      calc ∑ n ∈ (Finset.range N).filter (fun n => k ≤ n),
            C n k * rho n k ^ (L n + 1) / (1 - rho n k)
          ≤ ∑ n ∈ (Finset.range N).filter (fun n => k ≤ n), (1 / 2 : ℝ) ^ n := by
            refine Finset.sum_le_sum fun n hn => ?_
            exact hterm n (Finset.mem_filter.mp hn).2
        _ ≤ ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro n _ _
            positivity
        _ ≤ 2 := by
            have hgeom : ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n
                = (1 - (1 / 2 : ℝ) ^ N) / (1 - 1 / 2) := by
              rw [geom_sum_eq (by norm_num) N]
              field_simp
              ring
            rw [hgeom]
            have hpow : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N := by positivity
            rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 - 1 / 2)]
            linarith
  -- assemble
  exact hasFractalSphericalStrongType_iUnion_of_bandRates (by omega) hGsub hLn hGloc
    phi hphiOne hphiZero hphiNorm (hp1 k) (hpq k)
    (fun n => (hC n k).le) (fun n => (hrho n k).le) (fun n => hrho1 n k)
    (fun n j hj f => hratesG n j hj f) hcell hsummable

open MeasureTheory Set ENNReal
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary



/-! ### Comparing the two Assouad vertices with the Minkowski vertex -/

theorem Q4_first_lt_Q3_first {d : ℕ} {beta : ℝ} (hd : 2 ≤ d) (hb : 0 < beta)
    (hb1 : beta ≤ 1) : (Q4 d beta).1 < (Q3 d beta).1 := by
  have hD : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hM : (0:ℝ) < (d:ℝ) - beta + 1 := by linarith
  have hNb : (0:ℝ) < (d:ℝ)^2 + 2*beta - 1 := by nlinarith
  show (d:ℝ) * ((d:ℝ) - 1) / ((d:ℝ)^2 + 2*beta - 1)
      < ((d:ℝ) - beta) / ((d:ℝ) - beta + 1)
  rw [div_lt_div_iff₀ hNb hM]
  nlinarith [hb, hb1, hD]

theorem Q4_second_lt_Q3_second {d : ℕ} {beta : ℝ} (hd : 2 ≤ d) (hb : 0 < beta)
    (hb1 : beta ≤ 1) : (Q4 d beta).2 < (Q3 d beta).2 := by
  have hD : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hM : (0:ℝ) < (d:ℝ) - beta + 1 := by linarith
  have hNb : (0:ℝ) < (d:ℝ)^2 + 2*beta - 1 := by nlinarith
  show ((d:ℝ) - 1) / ((d:ℝ)^2 + 2*beta - 1) < 1 / ((d:ℝ) - beta + 1)
  rw [div_lt_div_iff₀ hNb hM]
  nlinarith [hb, hD]

/-! ### The cluster functional of a pair reconstructed from a separating line -/

theorem clusterEdgeFunctional_of_line {d : ℕ} {s tau b' g' : ℝ} (hd : 2 ≤ d)
    (htau0 : 0 < tau) (htau1 : tau < 1)
    (hP : 0 < (d:ℝ) - s - tau * ((d:ℝ) + 1))
    (hb' : b' = ((d:ℝ) - s - tau * ((d:ℝ) + 1)) / (1 - tau))
    (hg' : g' = (((d:ℝ) - s - tau * ((d:ℝ) + 1)) * ((d:ℝ) - 1)) / (2 * tau))
    (x : ExponentPoint) :
    clusterEdgeFunctional d (b'/g') b' x = (tau - x.1 + s * x.2) / (1 - tau) := by
  subst hb'
  subst hg'
  have hD : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h1 : (0:ℝ) < 1 - tau := by linarith
  have hDm : (0:ℝ) < (d:ℝ) - 1 := by linarith
  set P : ℝ := (d:ℝ) - s - tau * ((d:ℝ) + 1) with hPdef
  have hPne : P ≠ 0 := ne_of_gt hP
  have hratio : (P / (1 - tau)) / ((P * ((d:ℝ) - 1)) / (2 * tau))
      = 2 * tau / ((1 - tau) * ((d:ℝ) - 1)) := by
    rw [div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm]
    field_simp
  show (P / (1 - tau)) / ((P * ((d:ℝ) - 1)) / (2 * tau)) / 2 * ((d:ℝ) - 1)
      + ((d:ℝ) - (P / (1 - tau))
        - (P / (1 - tau)) / ((P * ((d:ℝ) - 1)) / (2 * tau)) / 2 * ((d:ℝ) - 1)) * x.2
      - (1 + (P / (1 - tau)) / ((P * ((d:ℝ) - 1)) / (2 * tau)) / 2 * ((d:ℝ) - 1)) * x.1
      = (tau - x.1 + s * x.2) / (1 - tau)
  rw [hratio]
  have hA : 2 * tau / ((1 - tau) * ((d:ℝ) - 1)) / 2 * ((d:ℝ) - 1) = tau / (1 - tau) := by
    field_simp
  rw [hA, hPdef]
  field_simp
  ring

/-! ### The separating pair -/

set_option maxHeartbeats 2000000 in
/-- **The key geometric step of §7.**  If `W` is a closed convex set squeezed between
`Q(β,γ)` and `Q(β,β)` and `z ∈ Q(β,β) \ W`, then there is an admissible pair `(β',γ')` whose
region contains `W` but not `z`.  The pair is read off from a separating line: the line meets
the segment `[Q₃(β),Q₃(0)]` in `Q₃(β')` and the segment `[Q₄(γ),Q₄(β)]` in `Q₄(γ')`. -/
theorem exists_pair_separating {d : ℕ} (hd : 2 ≤ d) {beta gam : ℝ}
    (hb : 0 < beta) (hbg : beta < gam) (hg1 : gam ≤ 1)
    {W : Set ExponentPoint} (hWc : IsClosed W) (hWconv : Convex ℝ W)
    (hQW : Q d beta gam ⊆ W) (hWQ : W ⊆ Q d beta beta)
    {z : ExponentPoint} (hz : z ∈ Q d beta beta) (hzW : z ∉ W) :
    ∃ b' g' : ℝ, 0 ≤ b' ∧ b' ≤ beta ∧ beta ≤ g' ∧ g' ≤ gam ∧
      W ⊆ Q d b' g' ∧ z ∉ Q d b' g' := by
  have hD : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hb1 : beta ≤ 1 := le_trans hbg.le hg1
  have hg0 : 0 < gam := lt_trans hb hbg
  have hM : (0:ℝ) < (d:ℝ) - beta + 1 := by linarith
  have hNb : (0:ℝ) < (d:ℝ)^2 + 2*beta - 1 := by nlinarith
  have hNg : (0:ℝ) < (d:ℝ)^2 + 2*gam - 1 := by nlinarith
  have hMm : (0:ℝ) < (d:ℝ) - 1 + beta := by linarith
  obtain ⟨f, u, hfW, hfz⟩ := geometric_hahn_banach_closed_point hWconv hWc hzW
  set a : ℝ := f ((1:ℝ), (0:ℝ)) with ha_def
  set bb : ℝ := f ((0:ℝ), (1:ℝ)) with hbb_def
  have hf : ∀ x : ExponentPoint, f x = a * x.1 + bb * x.2 := by
    intro x
    have hx : x = x.1 • ((1:ℝ), (0:ℝ)) + x.2 • ((0:ℝ), (1:ℝ)) := by
      simp [Prod.ext_iff]
    conv_lhs => rw [hx]
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul, ha_def, hbb_def]
    ring
  -- the values of the separating functional at the vertices
  have hu0 : 0 < u := by
    have h := hfW _ (hQW (Q1_mem_Q d beta gam))
    rw [hf] at h
    simpa [Q1] using h
  have hu2 : a * (Q2 d beta).1 + bb * (Q2 d beta).2 < u := by
    have h := hfW _ (hQW (Q2_mem_Q d beta gam)); rwa [hf] at h
  have hu3 : a * (Q3 d beta).1 + bb * (Q3 d beta).2 < u := by
    have h := hfW _ (hQW (Q3_mem_Q d beta gam)); rwa [hf] at h
  have hu4g : a * (Q4 d gam).1 + bb * (Q4 d gam).2 < u := by
    have h := hfW _ (hQW (Q4_mem_Q d beta gam)); rwa [hf] at h
  have hzval : u < a * z.1 + bb * z.2 := by rwa [hf] at hfz
  have hu4b : u < a * (Q4 d beta).1 + bb * (Q4 d beta).2 := by
    by_contra hcon
    push_neg at hcon
    have hQ1' : exponentLinearMap a bb Q1 ≤ u := by
      show a * Q1.1 + bb * Q1.2 ≤ u
      simpa [Q1] using hu0.le
    have hsub := Q_subset_exponentHalfspace_of_vertices (d := d) (β := beta) (γ := beta)
      (a := a) (b := bb) (c := u) hQ1' hu2.le hu3.le hcon
    have hzin : a * z.1 + bb * z.2 ≤ u := hsub hz
    linarith
  -- cleared forms of the vertex inequalities
  have h3 : a*((d:ℝ)-beta) + bb < u * ((d:ℝ)-beta+1) := by
    have hexp : a * (Q3 d beta).1 + bb * (Q3 d beta).2
        = (a*((d:ℝ)-beta) + bb) / ((d:ℝ)-beta+1) := by
      show a * (((d:ℝ)-beta)/((d:ℝ)-beta+1)) + bb * (1/((d:ℝ)-beta+1)) = _
      field_simp
    rw [hexp, div_lt_iff₀ hM] at hu3
    linarith
  have h4g : ((d:ℝ)-1)*(a*(d:ℝ)+bb) < u * ((d:ℝ)^2+2*gam-1) := by
    have hexp : a * (Q4 d gam).1 + bb * (Q4 d gam).2
        = (((d:ℝ)-1)*(a*(d:ℝ)+bb)) / ((d:ℝ)^2+2*gam-1) := by
      show a * ((d:ℝ)*((d:ℝ)-1)/((d:ℝ)^2+2*gam-1))
          + bb * (((d:ℝ)-1)/((d:ℝ)^2+2*gam-1)) = _
      field_simp
    rw [hexp, div_lt_iff₀ hNg] at hu4g
    linarith
  have h4b : u * ((d:ℝ)^2+2*beta-1) < ((d:ℝ)-1)*(a*(d:ℝ)+bb) := by
    have hexp : a * (Q4 d beta).1 + bb * (Q4 d beta).2
        = (((d:ℝ)-1)*(a*(d:ℝ)+bb)) / ((d:ℝ)^2+2*beta-1) := by
      show a * ((d:ℝ)*((d:ℝ)-1)/((d:ℝ)^2+2*beta-1))
          + bb * (((d:ℝ)-1)/((d:ℝ)^2+2*beta-1)) = _
      field_simp
    rw [hexp, lt_div_iff₀ hNb] at hu4b
    linarith
  -- the sign of the linear part
  have hS : 0 < a*(d:ℝ) + bb := by nlinarith
  have hapos : 0 < a := by
    by_contra hacon
    push_neg at hacon
    have e2 : a*(d:ℝ)+bb ≤ a*((d:ℝ)-beta)+bb := by nlinarith
    have e3 : ((d:ℝ)-1)*((d:ℝ)-beta+1) ≤ (d:ℝ)^2+2*beta-1 := by nlinarith
    have e4 : (a*(d:ℝ)+bb) * ((d:ℝ)^2+2*beta-1) ≤ (a*((d:ℝ)-beta)+bb) * ((d:ℝ)^2+2*beta-1) :=
      mul_le_mul_of_nonneg_right e2 hNb.le
    have e5 : (a*(d:ℝ)+bb) * (((d:ℝ)-1)*((d:ℝ)-beta+1))
        ≤ (a*(d:ℝ)+bb) * ((d:ℝ)^2+2*beta-1) := mul_le_mul_of_nonneg_left e3 hS.le
    have e6 : (a*((d:ℝ)-beta)+bb) * ((d:ℝ)^2+2*beta-1)
        < ((d:ℝ)-1)*(a*(d:ℝ)+bb) * ((d:ℝ)-beta+1) := by
      have h3' : (a*((d:ℝ)-beta) + bb) * ((d:ℝ)^2+2*beta-1)
          < (u * ((d:ℝ)-beta+1)) * ((d:ℝ)^2+2*beta-1) :=
        mul_lt_mul_of_pos_right h3 hNb
      have h4b' : (u * ((d:ℝ)^2+2*beta-1)) * ((d:ℝ)-beta+1)
          < (((d:ℝ)-1)*(a*(d:ℝ)+bb)) * ((d:ℝ)-beta+1) :=
        mul_lt_mul_of_pos_right h4b hM
      nlinarith [h3', h4b']
    nlinarith [e4, e5, e6]
  have hbbneg : bb < 0 := by
    have hd1 : (Q4 d beta).1 - (Q3 d beta).1 < 0 :=
      sub_neg.mpr (Q4_first_lt_Q3_first hd hb hb1)
    have hd2 : (Q4 d beta).2 - (Q3 d beta).2 < 0 :=
      sub_neg.mpr (Q4_second_lt_Q3_second hd hb hb1)
    have hkey : 0 < a * ((Q4 d beta).1 - (Q3 d beta).1)
        + bb * ((Q4 d beta).2 - (Q3 d beta).2) := by nlinarith [hu3, hu4b]
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_neg_of_pos_of_neg hapos hd1, mul_nonneg hcon (neg_nonneg.mpr hd2.le)]
  -- the normalized separating line `x.1 - s * x.2 = tau`
  set s : ℝ := -bb/a with hs_def
  set tau : ℝ := u/a with htau_def
  have has : a * s = -bb := by rw [hs_def]; field_simp
  have hat : a * tau = u := by rw [htau_def]; field_simp
  have hspos : 0 < s := by
    rw [hs_def]
    exact div_pos (neg_pos.mpr hbbneg) hapos
  have htau0 : 0 < tau := by rw [htau_def]; exact div_pos hu0 hapos
  have hWline : ∀ w ∈ W, w.1 - s * w.2 < tau := by
    intro w hw
    have h := hfW w hw
    rw [hf] at h
    have h2 : a * s * w.2 = -bb * w.2 := by rw [has]
    have hmul : a * (w.1 - s * w.2) < a * tau := by
      rw [hat]
      linarith [h2, h]
    exact lt_of_mul_lt_mul_left hmul hapos.le
  have hzline : tau < z.1 - s * z.2 := by
    have h2 : a * s * z.2 = -bb * z.2 := by rw [has]
    have hmul : a * tau < a * (z.1 - s * z.2) := by
      rw [hat]
      linarith [h2, hzval]
    exact lt_of_mul_lt_mul_left hmul hapos.le
  -- the point `z` lies in the region, so `s < d`
  have hz1 : z.2 ≤ z.1 := Q_subset_second_le_first hd hb1 hb.le hz
  have hz2 : z.1 ≤ (d:ℝ) * z.2 := Q_subset_first_le_natCast_mul_second hd hb.le hb1 hb.le hz
  have hz2pos : 0 < z.2 := by
    rcases le_or_gt z.2 0 with hcon | h
    · nlinarith
    · exact h
  have hsd : s < (d:ℝ) := by nlinarith
  -- the two inequalities in `(s, tau)` coordinates
  have hii : (d:ℝ) - beta - s < tau * ((d:ℝ) - beta + 1) := by
    have hmul : a * ((d:ℝ) - beta - s) < a * (tau * ((d:ℝ) - beta + 1)) := by
      have hL : a * ((d:ℝ) - beta - s) = a*((d:ℝ)-beta) + bb := by nlinarith [has]
      have hR : a * (tau * ((d:ℝ) - beta + 1)) = u * ((d:ℝ)-beta+1) := by
        rw [← hat]; ring
      rw [hL, hR]; exact h3
    exact lt_of_mul_lt_mul_left hmul hapos.le
  have hiii : ((d:ℝ)-1)*((d:ℝ)-s) < tau * ((d:ℝ)^2+2*gam-1) := by
    have hmul : a * (((d:ℝ)-1)*((d:ℝ)-s)) < a * (tau * ((d:ℝ)^2+2*gam-1)) := by
      have hL : a * (((d:ℝ)-1)*((d:ℝ)-s)) = ((d:ℝ)-1)*(a*(d:ℝ)+bb) := by nlinarith [has]
      have hR : a * (tau * ((d:ℝ)^2+2*gam-1)) = u * ((d:ℝ)^2+2*gam-1) := by
        rw [← hat]; ring
      rw [hL, hR]; exact h4g
    exact lt_of_mul_lt_mul_left hmul hapos.le
  have hiv : tau * ((d:ℝ)^2+2*beta-1) < ((d:ℝ)-1)*((d:ℝ)-s) := by
    have hmul : a * (tau * ((d:ℝ)^2+2*beta-1)) < a * (((d:ℝ)-1)*((d:ℝ)-s)) := by
      have hR : a * (((d:ℝ)-1)*((d:ℝ)-s)) = ((d:ℝ)-1)*(a*(d:ℝ)+bb) := by nlinarith [has]
      have hL : a * (tau * ((d:ℝ)^2+2*beta-1)) = u * ((d:ℝ)^2+2*beta-1) := by
        rw [← hat]; ring
      rw [hL, hR]; exact h4b
    exact lt_of_mul_lt_mul_left hmul hapos.le
  have htau1 : tau < 1 := by nlinarith
  have hone : (0:ℝ) < 1 - tau := by linarith
  -- the pair of parameters
  have hP : 0 < (d:ℝ) - s - tau * ((d:ℝ)+1) := by nlinarith
  set P : ℝ := (d:ℝ) - s - tau * ((d:ℝ)+1) with hPdef
  have hb'0 : (0:ℝ) ≤ P/(1-tau) := le_of_lt (div_pos hP hone)
  have hb'b : P/(1-tau) ≤ beta := by
    rw [div_le_iff₀ hone, hPdef]; nlinarith
  have hbg' : beta ≤ P*((d:ℝ)-1)/(2*tau) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*tau), hPdef]; nlinarith
  refine ⟨P/(1-tau), P*((d:ℝ)-1)/(2*tau), hb'0, hb'b, hbg', ?_, ?_, ?_⟩
  · -- `γ' ≤ γ`
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*tau), hPdef]; nlinarith
  · -- `W ⊆ Q d β' γ'`
    intro w hw
    rw [mem_Q_iff_not_sharpnessViolation hd hb'0 (le_trans hb'b hb1)
      (le_trans hb'b hbg')]
    have hwQ := hWQ hw
    have hw1 : w.2 ≤ w.1 := Q_subset_second_le_first hd hb1 hb.le hwQ
    have hw2 : w.1 ≤ (d:ℝ) * w.2 := Q_subset_first_le_natCast_mul_second hd hb.le hb1 hb.le hwQ
    have hw3 : (d:ℝ) * w.1 ≤ (1 - beta) * w.2 + ((d:ℝ) - 1) :=
      Q_subset_annulus_halfspace hd hb.le (le_refl beta) hb1 hwQ
    have hw2nn : 0 ≤ w.2 := by nlinarith
    have hwl := hWline w hw
    have hcl : clusterEdgeFunctional d ((P/(1-tau))/(P*((d:ℝ)-1)/(2*tau))) (P/(1-tau)) w
        = (tau - w.1 + s * w.2)/(1-tau) :=
      clusterEdgeFunctional_of_line hd htau0 htau1 hP (by rw [hPdef]) (by rw [hPdef]) w
    intro hbad
    rcases hbad with hbad | hbad | hbad | hbad
    · linarith
    · linarith
    · nlinarith
    · rw [hcl] at hbad
      have hnn : 0 ≤ (tau - w.1 + s * w.2)/(1-tau) :=
        div_nonneg (by linarith) hone.le
      linarith
  · -- `z ∉ Q d β' γ'`
    refine not_mem_Q_of_sharpnessViolation hd hb'0 (le_trans hb'b hb1)
      (le_trans hb'b hbg') (Or.inr (Or.inr (Or.inr ?_)))
    have hcl : clusterEdgeFunctional d ((P/(1-tau))/(P*((d:ℝ)-1)/(2*tau))) (P/(1-tau)) z
        = (tau - z.1 + s * z.2)/(1-tau) :=
      clusterEdgeFunctional_of_line hd htau0 htau1 hP (by rw [hPdef]) (by rw [hPdef]) z
    rw [hcl]
    exact div_neg_of_neg_of_pos (by linarith) hone

open MeasureTheory Set ENNReal
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary



/-! ### `W` is a countable intersection of regions -/

/-- **Equation (7.3) of the paper.**  A closed convex set squeezed between `Q(β,γ)` and
`Q(β,β)` is a countable intersection of regions `Q(βₙ,γₙ)` with `βₙ ≤ β ≤ γₙ ≤ γ`. -/
theorem exists_countable_family_iInter {d : ℕ} (hd : 2 ≤ d) {beta gam : ℝ}
    (hb : 0 < beta) (hbg : beta < gam) (hg1 : gam ≤ 1)
    {W : Set ExponentPoint} (hWc : IsClosed W) (hWconv : Convex ℝ W)
    (hQW : Q d beta gam ⊆ W) (hWQ : W ⊆ Q d beta beta) :
    ∃ bs gs : ℕ → ℝ, (∀ n, 0 ≤ bs n) ∧ (∀ n, bs n ≤ beta) ∧ (∀ n, beta ≤ gs n) ∧
      (∀ n, gs n ≤ gam) ∧ W = ⋂ n, Q d (bs n) (gs n) := by
  classical
  set S : Set (ℝ × ℝ) :=
    {p | 0 ≤ p.1 ∧ p.1 ≤ beta ∧ beta ≤ p.2 ∧ p.2 ≤ gam ∧ W ⊆ Q d p.1 p.2} with hSdef
  have hbb : ((beta, beta) : ℝ × ℝ) ∈ S := ⟨hb.le, le_refl _, le_refl _, hbg.le, hWQ⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : S => (Q d (i : ℝ × ℝ).1 (i : ℝ × ℝ).2)ᶜ)
      (fun i => (isClosed_Q d _ _).isOpen_compl)
  have hT'c : (insert (⟨(beta, beta), hbb⟩ : S) T).Countable := hTc.insert _
  have hT'ne : (insert (⟨(beta, beta), hbb⟩ : S) T).Nonempty := ⟨_, Set.mem_insert _ _⟩
  obtain ⟨e, he⟩ := hT'c.exists_eq_range hT'ne
  refine ⟨fun n => (e n : ℝ × ℝ).1, fun n => (e n : ℝ × ℝ).2, fun n => (e n).2.1,
    fun n => (e n).2.2.1, fun n => (e n).2.2.2.1, fun n => (e n).2.2.2.2.1, ?_⟩
  refine subset_antisymm ?_ ?_
  · intro w hw
    refine Set.mem_iInter.mpr ?_
    intro n
    exact (e n).2.2.2.2.2 hw
  · intro z hz
    have hzmem : ∀ n, z ∈ Q d (e n : ℝ × ℝ).1 (e n : ℝ × ℝ).2 := Set.mem_iInter.mp hz
    have hzQ : z ∈ Q d beta beta := by
      have hmem : (⟨(beta, beta), hbb⟩ : S) ∈ insert (⟨(beta, beta), hbb⟩ : S) T :=
        Set.mem_insert _ _
      rw [he] at hmem
      obtain ⟨n, hn⟩ := hmem
      have := hzmem n
      rw [hn] at this
      exact this
    by_contra hzW
    obtain ⟨b', g', hb'0, hb'b, hbg', hg'g, hWsub, hznot⟩ :=
      exists_pair_separating hd hb hbg hg1 hWc hWconv hQW hWQ hzQ hzW
    have hmemS : ((b', g') : ℝ × ℝ) ∈ S := ⟨hb'0, hb'b, hbg', hg'g, hWsub⟩
    have hzU : z ∈ ⋃ i : S, (Q d (i : ℝ × ℝ).1 (i : ℝ × ℝ).2)ᶜ :=
      Set.mem_iUnion.mpr ⟨⟨(b', g'), hmemS⟩, hznot⟩
    rw [← hTU] at hzU
    obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.mp hzU
    have hiT' : i ∈ insert (⟨(beta, beta), hbb⟩ : S) T := Set.mem_insert_of_mem _ hiT
    rw [he] at hiT'
    obtain ⟨n, hn⟩ := hiT'
    have := hzmem n
    rw [hn] at this
    exact hzi this

open MeasureTheory Set ENNReal
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
/-! ### A countable dense sequence in the interior -/

theorem exists_dense_seq_interior {W : Set ExponentPoint} (h : (interior W).Nonempty) :
    ∃ u : ℕ → ExponentPoint, (∀ k, u k ∈ interior W) ∧
      interior W ⊆ closure (Set.range u) := by
  have hne : Nonempty ↥(interior W) := h.to_subtype
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ↥(interior W)
  refine ⟨fun k => ((u k : ExponentPoint)), fun k => (u k).2, ?_⟩
  intro x hx
  have h1 : Set.range (fun k => ((u k : ExponentPoint))) = Subtype.val '' (Set.range u) := by
    rw [← Set.range_comp]
    rfl
  rw [h1]
  have h3 : x ∈ Subtype.val '' (closure (Set.range u)) := by
    rw [hu.closure_eq]
    exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  exact image_closure_subset_closure_image continuous_subtype_val h3

/-! ### Theorem 1.2(i), the sufficiency, in the main case `0 < β < γ` -/

set_option maxHeartbeats 1000000 in
/-- **The main case of Theorem 1.2(i).**  Every closed convex set squeezed between `Q(β,γ)` and
`Q(β,β)` with `0 < β < γ` is the closure of a type set. -/
theorem exists_closure_fractalTypeSet_eq_of_sandwich_pos {d : ℕ} (hd : 2 ≤ d) {beta gam : ℝ}
    (hb : 0 < beta) (hbg : beta < gam) (hg1 : gam ≤ 1)
    {W : Set ExponentPoint} (hWc : IsClosed W) (hWconv : Convex ℝ W)
    (hQW : Q d beta gam ⊆ W) (hWQ : W ⊆ Q d beta beta) :
    ∃ E : Set ℝ, E ⊆ Icc (1:ℝ) 2 ∧ E.Nonempty ∧ closure (fractalTypeSet d E) = W := by
  classical
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hb1 : beta ≤ 1 := le_trans hbg.le hg1
  obtain ⟨bs, gs0, hbs0, hbsb, hbgs, hgsg, hWeq⟩ :=
    exists_countable_family_iInter hd hb hbg hg1 hWc hWconv hQW hWQ
  set gs : ℕ → ℝ := fun n => if bs n = 0 then 0 else gs0 n with hgsdef
  have hQeq : ∀ n, Q d (bs n) (gs n) = Q d (bs n) (gs0 n) := by
    intro n
    by_cases h : bs n = 0
    · have h1 : gs n = 0 := by simp only [hgsdef, h, if_pos]
      rw [h1, h]
      exact (Q_zero_beta_eq hd (le_trans hb.le (hbgs n))).symm
    · simp only [hgsdef, if_neg h]
  have hWeq' : W = ⋂ n, Q d (bs n) (gs n) := by
    rw [hWeq]
    exact (Set.iInter_congr hQeq).symm
  have hbgcond : ∀ n, 0 ≤ bs n ∧ bs n ≤ gs n ∧ gs n ≤ 1 := by
    intro n
    by_cases h : bs n = 0
    · have h1 : gs n = 0 := by simp only [hgsdef, h, if_pos]
      refine ⟨hbs0 n, ?_, ?_⟩
      · rw [h, h1]
      · rw [h1]; norm_num
    · have h1 : gs n = gs0 n := by simp only [hgsdef, if_neg h]
      refine ⟨hbs0 n, ?_, ?_⟩
      · rw [h1]; linarith [hbsb n, hbgs n]
      · rw [h1]; linarith [hgsg n]
  have hdeg : ∀ n, bs n = 0 → gs n = 0 := by
    intro n h
    simp only [hgsdef, h, if_pos]
  have hWi : (interior W).Nonempty :=
    Set.Nonempty.mono (interior_mono hQW) (interior_Q_nonempty hd hb.le hb1 hbg.le)
  obtain ⟨zz, hzzmem, hzzdense⟩ := exists_dense_seq_interior hWi
  have hzmem : ∀ k, zz k ∈ interior (⋂ n, Q d (bs n) (gs n)) := by
    intro k
    rw [← hWeq']
    exact hzzmem k
  obtain ⟨E, hE, hEne, hGfam, hztype⟩ := exists_iUnion_type_points hd hbgcond hdeg zz hzmem
  have hEpos : E ⊆ Ioi (0:ℝ) := by
    intro t ht
    have := hE ht
    exact lt_of_lt_of_le (by norm_num) this.1
  refine ⟨E, hE, hEne, subset_antisymm ?_ ?_⟩
  · rw [hWeq']
    refine closure_minimal ?_ (isClosed_iInter (fun n => isClosed_Q d _ _))
    intro x hx
    refine Set.mem_iInter.mpr ?_
    intro n
    obtain ⟨G, hGE, hGne, hGreg⟩ := hGfam n
    have hGsub : G ⊆ Icc (1:ℝ) 2 := hGE.trans hE
    have hxG : x ∈ fractalTypeSet d G := fractalTypeSet_mono hdpos hGE hEpos hx
    exact fractalTypeSet_subset_Q_of_regular hd hGsub hGne
      ⟨(hbgcond n).1, (hbgcond n).2.1, (hbgcond n).2.2⟩ hGreg hxG
  · have hWcl : closure (interior W) = W := by
      rw [hWconv.closure_interior_eq_closure_of_nonempty_interior hWi, hWc.closure_eq]
    intro x hxW
    rw [← hWcl] at hxW
    have h1 : closure (interior W) ⊆ closure (Set.range zz) :=
      closure_minimal hzzdense isClosed_closure
    have h2 : closure (Set.range zz) ⊆ closure (fractalTypeSet d E) := by
      refine closure_mono ?_
      intro y hy
      obtain ⟨k, rfl⟩ := hy
      exact hztype k
    exact h2 (h1 hxW)

open MeasureTheory Set ENNReal
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.Spherical.FractalDilations.AHRSLowerBounds



/-! ### The Minkowski parameter is determined -/

/-- If the diagonal Minkowski vertex `Q₂(β)` lies in `Q(β',γ')`, then `β' ≤ β`.  The annulus
halfspace of `Q(β',γ')` is the only constraint that is active there. -/
theorem le_of_Q2_mem_Q {d : ℕ} (hd : 2 ≤ d) {b b' g' : ℝ} (hb : 0 ≤ b)
    (hb'0 : 0 ≤ b') (hb'1 : b' ≤ 1) (hb'g' : b' ≤ g') (hmem : Q2 d b ∈ Q d b' g') :
    b' ≤ b := by
  have hD : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hden : (0:ℝ) < (d:ℝ) - 1 + b := by linarith
  have hann := Q_subset_annulus_halfspace hd hb'0 hb'g' hb'1 hmem
  have h1 : (Q2 d b).1 = ((d:ℝ) - 1)/((d:ℝ) - 1 + b) := rfl
  have h2 : (Q2 d b).2 = ((d:ℝ) - 1)/((d:ℝ) - 1 + b) := rfl
  rw [Set.mem_setOf_eq, h1, h2] at hann
  set m : ℝ := ((d:ℝ) - 1)/((d:ℝ) - 1 + b) with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    exact div_pos (by linarith) hden
  have hmid : m * ((d:ℝ) - 1 + b) = (d:ℝ) - 1 := by
    rw [hmdef]
    field_simp
  nlinarith [hann, hmid, hmpos]

/-- **Theorem 1.2(ii), the Minkowski part.**  If the closure of the type set is squeezed
between `Q(β,γ)` and `Q(β,β)`, then `β` is the upper Minkowski dimension of `E`. -/
theorem upperMinkowskiDimension_eq_of_sandwich {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1:ℝ) 2) (hEne : E.Nonempty) {beta gam : ℝ}
    (hb0 : 0 ≤ beta) (hbg : beta ≤ gam) (hg1 : gam ≤ 1)
    (hQW : Q d beta gam ⊆ closure (fractalTypeSet d E))
    (hWQ : closure (fractalTypeSet d E) ⊆ Q d beta beta) :
    upperMinkowskiDimension E = beta := by
  have hb1 : beta ≤ 1 := le_trans hbg hg1
  set bE : ℝ := upperMinkowskiDimension E with hbE
  set gE : ℝ := quasiAssouadDimension E with hgE
  have hbE0 : 0 ≤ bE := upperMinkowskiDimension_nonneg_of_subset_Icc hE
  have hbEgE : bE ≤ gE := upperMinkowskiDimension_le_quasiAssouadDimension hE
  have hgE1 : gE ≤ 1 := quasiAssouadDimension_le_one E
  have hbE1 : bE ≤ 1 := le_trans hbEgE hgE1
  have hQE : Q d bE gE ⊆ closure (fractalTypeSet d E) :=
    Q_subset_closure_fractalTypeSet hd hE hbE0 hbEgE hgE1 rfl rfl
  have hEQ : closure (fractalTypeSet d E) ⊆ Q d bE bE := by
    refine closure_minimal ?_ (isClosed_Q d _ _)
    exact fractalTypeSet_subset_Q_self hd hE hEne hbE0 hbE1 rfl
  refine le_antisymm ?_ ?_
  · exact le_of_Q2_mem_Q hd hb0 hbE0 hbE1 (le_refl bE)
      (hEQ (hQW (Q2_mem_Q d beta gam)))
  · exact le_of_Q2_mem_Q hd hbE0 hb0 hb1 (le_refl beta)
      (hWQ (hQE (Q2_mem_Q d bE gE)))

/-! ### The clustered-radius necessary condition on the critical ray -/

/-- The closed set cut out by the clustered-radius test at the parameters `(θ,α)`. -/
def clusterTestSet (d : ℕ) (theta al : ℝ) : Set ExponentPoint :=
  {x : ExponentPoint | al * x.2 - ((d:ℝ)-1)/2 * (1 - x.2 - x.1) ≤ 0 ∨
    x.1 ≤ (d:ℝ)*x.2 - (1-theta)*(al * x.2 - ((d:ℝ)-1)/2 * (1 - x.2 - x.1))}

theorem isClosed_clusterTestSet (d : ℕ) (theta al : ℝ) :
    IsClosed (clusterTestSet d theta al) := by
  have hcont : Continuous
      (fun x : ExponentPoint => al * x.2 - ((d:ℝ)-1)/2 * (1 - x.2 - x.1)) := by
    fun_prop
  refine IsClosed.union (isClosed_le hcont continuous_const) ?_
  exact isClosed_le continuous_fst (by fun_prop)

/-- **Lemma 5.1(i) of the paper, in the form of a closed necessary condition.**  Boundedness of
the maximal operator forces the clustered-radius inequality at every admissible pair `(θ,α)`
with `α` below the upper Assouad spectrum at `θ`. -/
theorem closure_fractalTypeSet_subset_clusterTestSet {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1:ℝ) 2) {theta al : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hal0 : 0 ≤ al) (hal : al < upperAssouadSpectrum E theta) :
    closure (fractalTypeSet d E) ⊆ clusterTestSet d theta al := by
  refine closure_minimal ?_ (isClosed_clusterTestSet d theta al)
  intro x hx
  obtain ⟨p, q, hp, hq, hxeq, hst⟩ := hx
  by_contra hbad
  rw [clusterTestSet, Set.mem_setOf_eq] at hbad
  push_neg at hbad
  obtain ⟨hk, hpower⟩ := hbad
  have hx1 : x.1 = p⁻¹ := by rw [hxeq]; rfl
  have hx2 : x.2 = q⁻¹ := by rw [hxeq]; rfl
  have hd1 : 1 ≤ d := by omega
  have hncast : ((d - 1 : ℕ) : ℝ) + 1 = (d:ℝ) := by
    have : ((d - 1 : ℕ) : ℝ) = (d:ℝ) - 1 := by
      have h := Nat.cast_sub (R := ℝ) hd1
      simpa using h
    rw [this]; ring
  have hncast' : ((d - 1 : ℕ) : ℝ) = (d:ℝ) - 1 := by linarith
  have hkq : 0 < al * q⁻¹ - (((d - 1 : ℕ) : ℝ)) / 2 * (1 - q⁻¹ - p⁻¹) := by
    rw [hncast', ← hx1, ← hx2]
    linarith
  have hpowerq : (((d - 1 : ℕ) : ℝ) + 1) * q⁻¹ -
      (1 - theta) * (al * q⁻¹ - (((d - 1 : ℕ) : ℝ)) / 2 * (1 - q⁻¹ - p⁻¹)) < p⁻¹ := by
    rw [hncast, hncast', ← hx1, ← hx2]
    linarith
  have hunb := fractalSphericalUnbounded_of_upper_spectrum_cluster_gap
    (n := d - 1) (E := E) (θ := theta) (α := al)
    (γ := upperAssouadSpectrum E theta) (p := p) (q := q)
    (by omega) hE hθ0 hθ1 rfl hal0 hal hp hq hkq hpowerq
  rw [Nat.sub_add_cancel hd1] at hunb
  exact not_unbounded_of_hasFractalSphericalStrongType hst hunb

/-- On the critical ray `1/p = d/q` the clustered-radius test is active for every `θ`, so the
quasi-Assouad dimension controls the whole ray. -/
theorem clusterTest_of_mem_closure {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1:ℝ) 2) {x : ExponentPoint} (hx : x ∈ closure (fractalTypeSet d E))
    (hray : x.1 = (d:ℝ) * x.2) {al : ℝ} (hal0 : 0 ≤ al)
    (hal : al < quasiAssouadDimension E) :
    al * x.2 - ((d:ℝ)-1)/2 * (1 - x.2 - x.1) ≤ 0 := by
  have hne : (upperAssouadSpectrum E '' Ico (0:ℝ) 1).Nonempty :=
    ⟨upperAssouadSpectrum E 0, ⟨0, ⟨le_refl (0:ℝ), zero_lt_one⟩, rfl⟩⟩
  rw [quasiAssouadDimension] at hal
  obtain ⟨y, hy, haly⟩ := exists_lt_of_lt_csSup hne hal
  obtain ⟨theta, hθ, hθeq⟩ := hy
  have hmem := closure_fractalTypeSet_subset_clusterTestSet hd hE hθ.1 hθ.2 hal0
    (by rw [hθeq]; exact haly) hx
  rw [clusterTestSet, Set.mem_setOf_eq] at hmem
  rcases hmem with h | h
  · exact h
  · have hpos : (0:ℝ) < 1 - theta := sub_pos.mpr hθ.2
    rw [hray] at h ⊢
    nlinarith [h, hpos]

/-- **Theorem 1.2(ii), the quasi-Assouad part.**  If `Q(β,γ) ⊆ closure (T_E)` and `γ` is minimal
with this property, then `γ` is the quasi-Assouad dimension of `E`. -/
theorem quasiAssouadDimension_eq_of_sandwich_minimal {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1:ℝ) 2) (hEne : E.Nonempty) {beta gam : ℝ}
    (hb0 : 0 ≤ beta) (hbg : beta ≤ gam) (hg1 : gam ≤ 1)
    (hQW : Q d beta gam ⊆ closure (fractalTypeSet d E))
    (hWQ : closure (fractalTypeSet d E) ⊆ Q d beta beta)
    (hmin : ∀ g' : ℝ, beta ≤ g' → g' ≤ 1 →
      Q d beta g' ⊆ closure (fractalTypeSet d E) → gam ≤ g') :
    quasiAssouadDimension E = gam := by
  have hD : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hbeta := upperMinkowskiDimension_eq_of_sandwich hd hE hEne hb0 hbg hg1 hQW hWQ
  set gE : ℝ := quasiAssouadDimension E with hgE
  have hbE0 : 0 ≤ upperMinkowskiDimension E :=
    upperMinkowskiDimension_nonneg_of_subset_Icc hE
  have hbEgE : upperMinkowskiDimension E ≤ gE :=
    upperMinkowskiDimension_le_quasiAssouadDimension hE
  have hgE1 : gE ≤ 1 := quasiAssouadDimension_le_one E
  have hQE : Q d beta gE ⊆ closure (fractalTypeSet d E) := by
    have := Q_subset_closure_fractalTypeSet hd hE hbE0 hbEgE hgE1 rfl rfl
    rwa [hbeta] at this
  have hle : gam ≤ gE := hmin gE (by rw [← hbeta]; exact hbEgE) hgE1 hQE
  refine le_antisymm ?_ hle
  by_contra hcon
  push_neg at hcon
  -- the vertex `Q₄(γ)` lies in the closure of the type set
  have hmem : Q4 d gam ∈ closure (fractalTypeSet d E) := hQW (Q4_mem_Q d beta gam)
  have hNg : (0:ℝ) < (d:ℝ)^2 + 2*gam - 1 := by
    have hg0 : 0 ≤ gam := le_trans hb0 hbg
    nlinarith
  have hray : (Q4 d gam).1 = (d:ℝ) * (Q4 d gam).2 := by
    show (d:ℝ)*((d:ℝ)-1)/((d:ℝ)^2+2*gam-1) = (d:ℝ) * (((d:ℝ)-1)/((d:ℝ)^2+2*gam-1))
    ring
  set al : ℝ := (gam + gE)/2 with haldef
  have hal0 : 0 ≤ al := by
    have hg0 : 0 ≤ gam := le_trans hb0 hbg
    rw [haldef]; linarith
  have halgE : al < gE := by rw [haldef]; linarith
  have hkey := clusterTest_of_mem_closure hd hE hmem hray hal0 (by rw [hgE] at halgE; exact halgE)
  -- the test functional at `Q₄(γ)` equals `(d-1)(α-γ)/(d²+2γ-1)`
  have hval : al * (Q4 d gam).2 - ((d:ℝ)-1)/2 * (1 - (Q4 d gam).2 - (Q4 d gam).1)
      = ((d:ℝ)-1)*(al - gam)/((d:ℝ)^2+2*gam-1) := by
    show al * (((d:ℝ)-1)/((d:ℝ)^2+2*gam-1)) - ((d:ℝ)-1)/2 *
      (1 - ((d:ℝ)-1)/((d:ℝ)^2+2*gam-1) - (d:ℝ)*((d:ℝ)-1)/((d:ℝ)^2+2*gam-1)) = _
    field_simp
    ring
  rw [hval] at hkey
  have halgam : gam < al := by rw [haldef]; linarith
  have hposv : 0 < ((d:ℝ)-1)*(al - gam)/((d:ℝ)^2+2*gam-1) :=
    div_pos (by nlinarith) hNg
  linarith

open MeasureTheory Set ENNReal
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.Spherical.FractalDilations.Auxiliary
open Auto.FractalDimensions
open Auto.FractalDimensions
open Auto.FractalDimensions



/-! ### Theorem 1.2(i): the sufficiency in all cases -/

/-- **The sufficiency in Theorem 1.2(i).**  Every closed convex set squeezed between `Q(β,γ)`
and `Q(β,β)` is the closure of a type set. -/
theorem exists_closure_fractalTypeSet_eq_of_sandwich {d : ℕ} (hd : 2 ≤ d) {beta gam : ℝ}
    (hb0 : 0 ≤ beta) (hbg : beta ≤ gam) (hg1 : gam ≤ 1)
    {W : Set ExponentPoint} (hWc : IsClosed W) (hWconv : Convex ℝ W)
    (hQW : Q d beta gam ⊆ W) (hWQ : W ⊆ Q d beta beta) :
    ∃ E : Set ℝ, E ⊆ Icc (1:ℝ) 2 ∧ E.Nonempty ∧ closure (fractalTypeSet d E) = W := by
  have hb1 : beta ≤ 1 := le_trans hbg hg1
  have hdegenerate : beta = 0 ∨ beta = gam → W = Q d beta beta := by
    intro hcase
    refine subset_antisymm hWQ ?_
    have hQQ : Q d beta beta = Q d beta gam := by
      rcases hcase with h0 | heq
      · rw [h0]
        exact (Q_zero_beta_eq hd (le_trans hb0 hbg)).symm
      · rw [heq]
    rw [hQQ]
    exact hQW
  rcases eq_or_lt_of_le hb0 with hb0' | hbpos
  · -- `β = 0`, so `W = Q(0,0)`
    have hWeq : W = Q d beta beta := hdegenerate (Or.inl hb0'.symm)
    obtain ⟨E, hE, hEne, hclos⟩ := exists_closure_fractalTypeSet_eq_Q' hd hb0 (le_refl beta) hb1
    exact ⟨E, hE, hEne, by rw [hclos, hWeq]⟩
  rcases eq_or_lt_of_le hbg with hbgeq | hbglt
  · -- `β = γ`, so `W = Q(β,β)`
    have hWeq : W = Q d beta beta := hdegenerate (Or.inr hbgeq)
    obtain ⟨E, hE, hEne, hclos⟩ := exists_closure_fractalTypeSet_eq_Q' hd hb0 (le_refl beta) hb1
    exact ⟨E, hE, hEne, by rw [hclos, hWeq]⟩
  · exact exists_closure_fractalTypeSet_eq_of_sandwich_pos hd hbpos hbglt hg1 hWc hWconv hQW hWQ

/-- **Theorem 1.2(i) of Roos--Seeger.**  A set `W` in the reciprocal-exponent plane is the closure
of the type set of some nonempty `E ⊆ [1,2]` if and only if `W` is closed, convex and squeezed
between `Q(β,γ)` and `Q(β,β)` for some `0 ≤ β ≤ γ ≤ 1`. -/
theorem closure_fractalTypeSet_iff_isClosed_convex_sandwich {d : ℕ} (hd : 2 ≤ d)
    (W : Set ExponentPoint) :
    (∃ E : Set ℝ, E ⊆ Icc (1:ℝ) 2 ∧ E.Nonempty ∧ closure (fractalTypeSet d E) = W) ↔
      (IsClosed W ∧ Convex ℝ W ∧ ∃ beta gam : ℝ, 0 ≤ beta ∧ beta ≤ gam ∧ gam ≤ 1 ∧
        Q d beta gam ⊆ W ∧ W ⊆ Q d beta beta) := by
  constructor
  · rintro ⟨E, hE, hEne, rfl⟩
    exact isClosed_convex_sandwich_closure_fractalTypeSet hd hE hEne
  · rintro ⟨hWc, hWconv, beta, gam, hb0, hbg, hg1, hQW, hWQ⟩
    exact exists_closure_fractalTypeSet_eq_of_sandwich hd hb0 hbg hg1 hWc hWconv hQW hWQ

/-! ### Theorem 1.2(ii): the parameters are the dimensions of `E` -/

/-- **Theorem 1.2(ii) of Roos--Seeger.**  If the closure of the type set of `E` is squeezed
between `Q(β,γ)` and `Q(β,β)`, then `β` is the upper Minkowski dimension of `E`, and if `γ` is
minimal with this property then `γ` is the quasi-Assouad dimension of `E`. -/
theorem dimensions_of_sandwich_closure_fractalTypeSet {d : ℕ} (hd : 2 ≤ d) {E : Set ℝ}
    (hE : E ⊆ Icc (1:ℝ) 2) (hEne : E.Nonempty) {beta gam : ℝ}
    (hb0 : 0 ≤ beta) (hbg : beta ≤ gam) (hg1 : gam ≤ 1)
    (hQW : Q d beta gam ⊆ closure (fractalTypeSet d E))
    (hWQ : closure (fractalTypeSet d E) ⊆ Q d beta beta) :
    upperMinkowskiDimension E = beta ∧
      ((∀ g' : ℝ, beta ≤ g' → g' ≤ 1 → Q d beta g' ⊆ closure (fractalTypeSet d E) → gam ≤ g') →
        quasiAssouadDimension E = gam) :=
  ⟨upperMinkowskiDimension_eq_of_sandwich hd hE hEne hb0 hbg hg1 hQW hWQ,
    fun hmin => quasiAssouadDimension_eq_of_sandwich_minimal hd hE hEne hb0 hbg hg1 hQW hWQ hmin⟩

end

end Auto.Spherical.FractalDilations.RSTypeSetCharacterization
