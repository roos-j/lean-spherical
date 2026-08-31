import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Slope

/-!
# Restricted real convex duality

This module provides a small, reusable real-valued convex-duality API. The
ordinary real `sSup` is intentionally used here rather than an extended-real
transform, so every theorem records the boundedness hypotheses that make the
suprema meaningful. This is useful for applications, such as
Legendre--Assouad profiles, whose natural slope and primal domains are
restricted intervals.
-/

namespace Auto.ConvexDuality

open Set

noncomputable section

/-- The real Fenchel conjugate of `f`, with its primal variable restricted to
`primal`.  Thus `restrictedConjugate f primal θ` is
`sup_{x ∈ primal} (x θ - f x)`. -/
def restrictedConjugate (f : ℝ → ℝ) (primal : Set ℝ) (θ : ℝ) : ℝ :=
  sSup ((fun x : ℝ => x * θ - f x) '' primal)

/-- The biconjugate obtained by restricting both the primal domain and the
set of admissible slopes. -/
def restrictedBiconjugate (f : ℝ → ℝ) (primal slopes : Set ℝ) (x : ℝ) : ℝ :=
  restrictedConjugate (restrictedConjugate f primal) slopes x

/-- Slopes for which the real-valued restricted conjugate is finite above.
For a minorizing affine function, its slope belongs to this set. -/
def effectiveSlopeSet (f : ℝ → ℝ) (primal : Set ℝ) : Set ℝ :=
  {θ | BddAbove ((fun x : ℝ => x * θ - f x) '' primal)}

@[simp]
theorem mem_effectiveSlopeSet {f : ℝ → ℝ} {primal : Set ℝ} {θ : ℝ} :
    θ ∈ effectiveSlopeSet f primal ↔
      BddAbove ((fun x : ℝ => x * θ - f x) '' primal) :=
  Iff.rfl

/-- A particular admissible primal point gives a lower bound for a restricted
conjugate. -/
theorem le_restrictedConjugate
    {f : ℝ → ℝ} {primal : Set ℝ} {x θ : ℝ}
    (hbounded : BddAbove ((fun y : ℝ => y * θ - f y) '' primal))
    (hx : x ∈ primal) :
    x * θ - f x ≤ restrictedConjugate f primal θ := by
  exact le_csSup hbounded ⟨x, hx, rfl⟩

/-- A pointwise affine upper bound controls the corresponding restricted
conjugate. -/
theorem restrictedConjugate_le
    {f : ℝ → ℝ} {primal : Set ℝ} {θ bound : ℝ}
    (hne : primal.Nonempty)
    (hbound : ∀ x ∈ primal, x * θ - f x ≤ bound) :
    restrictedConjugate f primal θ ≤ bound := by
  unfold restrictedConjugate
  apply csSup_le (hne.image _)
  rintro _ ⟨x, hx, rfl⟩
  exact hbound x hx

/-- An affine minorant on the primal domain supplies an upper bound for the
restricted conjugate. -/
theorem restrictedConjugate_le_neg_intercept
    {f : ℝ → ℝ} {primal : Set ℝ} {θ c : ℝ}
    (hne : primal.Nonempty)
    (hminor : ∀ x ∈ primal, θ * x + c ≤ f x) :
    restrictedConjugate f primal θ ≤ -c := by
  apply restrictedConjugate_le hne
  intro x hx
  have h := hminor x hx
  linarith [show x * θ = θ * x by ring]

/-- Every primal affine test lies below the restricted conjugate. -/
theorem affine_le_restrictedConjugate
    {f : ℝ → ℝ} {primal : Set ℝ} {x θ : ℝ}
    (hbounded : BddAbove ((fun y : ℝ => y * θ - f y) '' primal))
    (hx : x ∈ primal) :
    θ * x - f x ≤ restrictedConjugate f primal θ := by
  simpa [mul_comm] using le_restrictedConjugate hbounded hx

/-- A restricted conjugate is monotone in the slope parameter when its
primal domain consists of nonnegative points. -/
theorem restrictedConjugate_mono
    {f : ℝ → ℝ} {primal : Set ℝ} {θ η : ℝ}
    (hne : primal.Nonempty) (hprimal : primal ⊆ Ici (0 : ℝ))
    (hθη : θ ≤ η)
    (hbounded : BddAbove ((fun x : ℝ => x * η - f x) '' primal)) :
    restrictedConjugate f primal θ ≤ restrictedConjugate f primal η := by
  apply restrictedConjugate_le hne
  intro x hx
  calc
    x * θ - f x ≤ x * η - f x := by
      gcongr
      exact hprimal hx
    _ ≤ restrictedConjugate f primal η :=
      le_restrictedConjugate hbounded hx

/-- A finite restricted conjugate is convex in its slope parameter. -/
theorem restrictedConjugate_convex
    {f : ℝ → ℝ} {primal : Set ℝ}
    (hne : primal.Nonempty)
    (hbounded : ∀ θ : ℝ,
      BddAbove ((fun x : ℝ => x * θ - f x) '' primal)) :
    ConvexOn ℝ univ (restrictedConjugate f primal) := by
  constructor
  · exact convex_univ
  · intro θ hθ η hη a b ha hb hab
    apply restrictedConjugate_le hne
    intro x hx
    have hθ' : x * θ - f x ≤ restrictedConjugate f primal θ :=
      le_restrictedConjugate (hbounded θ) hx
    have hη' : x * η - f x ≤ restrictedConjugate f primal η :=
      le_restrictedConjugate (hbounded η) hx
    have hsum := add_le_add
      (mul_le_mul_of_nonneg_left hθ' ha)
      (mul_le_mul_of_nonneg_left hη' hb)
    simpa only [smul_eq_mul] using
      (show x * (a * θ + b * η) - f x ≤
          a * restrictedConjugate f primal θ +
            b * restrictedConjugate f primal η by
        calc
          x * (a * θ + b * η) - f x =
              a * (x * θ - f x) + b * (x * η - f x) := by
                calc
                  x * (a * θ + b * η) - f x =
                      a * (x * θ) + b * (x * η) - f x := by ring
                  _ = a * (x * θ - f x) + b * (x * η - f x) := by
                    calc
                      a * (x * θ) + b * (x * η) - f x =
                          a * (x * θ) + b * (x * η) - (1 : ℝ) * f x := by ring
                      _ = a * (x * θ) + b * (x * η) -
                          (a + b) * f x := by rw [hab]
                      _ = a * (x * θ - f x) + b * (x * η - f x) := by ring
          _ ≤ a * restrictedConjugate f primal θ +
            b * restrictedConjugate f primal η := hsum)

/-- If the primal variable is restricted to the unit interval, its restricted
conjugate is one-Lipschitz on any set on which the relevant suprema are finite.
This elementary estimate is useful when a convex-dual construction has to be
extended to an endpoint by continuity. -/
theorem restrictedConjugate_lipschitzOn_of_subset_Icc_zero_one
    {f : ℝ → ℝ} {primal slopes : Set ℝ}
    (hne : primal.Nonempty) (hprimal : primal ⊆ Icc (0 : ℝ) 1)
    (hbounded : ∀ θ ∈ slopes,
      BddAbove ((fun x : ℝ => x * θ - f x) '' primal)) :
    LipschitzOnWith 1 (restrictedConjugate f primal) slopes := by
  refine LipschitzOnWith.of_dist_le_mul fun θ hθ η hη => ?_
  have hforward : restrictedConjugate f primal θ ≤
      restrictedConjugate f primal η + dist θ η := by
    apply restrictedConjugate_le hne
    intro x hx
    have hx' := hprimal hx
    have hbase := le_restrictedConjugate (hbounded η hη) hx
    have hdelta : x * (θ - η) ≤ |θ - η| := by
      calc
        x * (θ - η) ≤ x * |θ - η| :=
          mul_le_mul_of_nonneg_left (le_abs_self (θ - η)) hx'.1
        _ ≤ 1 * |θ - η| :=
          mul_le_mul_of_nonneg_right hx'.2 (abs_nonneg _)
        _ = |θ - η| := by ring
    calc
      x * θ - f x = (x * η - f x) + x * (θ - η) := by ring
      _ ≤ restrictedConjugate f primal η + |θ - η| := by linarith
      _ = restrictedConjugate f primal η + dist θ η := by rw [Real.dist_eq]
  have hbackward : restrictedConjugate f primal η ≤
      restrictedConjugate f primal θ + dist θ η := by
    apply restrictedConjugate_le hne
    intro x hx
    have hx' := hprimal hx
    have hbase := le_restrictedConjugate (hbounded θ hθ) hx
    have hdelta : x * (η - θ) ≤ |η - θ| := by
      calc
        x * (η - θ) ≤ x * |η - θ| :=
          mul_le_mul_of_nonneg_left (le_abs_self (η - θ)) hx'.1
        _ ≤ 1 * |η - θ| :=
          mul_le_mul_of_nonneg_right hx'.2 (abs_nonneg _)
        _ = |η - θ| := by ring
    calc
      x * η - f x = (x * θ - f x) + x * (η - θ) := by ring
      _ ≤ restrictedConjugate f primal θ + |η - θ| := by linarith
      _ = restrictedConjugate f primal θ + dist θ η := by
        rw [Real.dist_eq, abs_sub_comm]
  rw [Real.dist_eq]
  simpa using (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- If `f` agrees with the identity on the tail `[1, ∞)`, then at every
slope at most one its conjugate over the nonnegative half-line is already
attained on the unit interval.  Since no regularity is assumed on the compact
part of `f`, boundedness of its unit-interval image is recorded explicitly. -/
theorem restrictedConjugate_Ici_eq_Icc_of_eq_id_on_Ici_one
    {f : ℝ → ℝ} {theta : ℝ}
    (htail : ∀ x : ℝ, 1 ≤ x → f x = x)
    (htheta : theta ≤ 1)
    (hbounded : BddAbove ((fun x : ℝ => x * theta - f x) '' Icc (0 : ℝ) 1)) :
    restrictedConjugate f (Ici (0 : ℝ)) theta =
      restrictedConjugate f (Icc (0 : ℝ) 1) theta := by
  have hIci : (Ici (0 : ℝ)).Nonempty := ⟨0, by simp⟩
  have hIcc : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  have hboundedIci : BddAbove
      ((fun x : ℝ => x * theta - f x) '' Ici (0 : ℝ)) := by
    rcases hbounded with ⟨bound, hbound⟩
    refine ⟨max bound (theta - 1), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rcases le_total x 1 with hx_one | hx_one
    · exact (hbound ⟨x, ⟨hx, hx_one⟩, rfl⟩).trans (le_max_left _ _)
    · have htail_x : f x = x := htail x hx_one
      have htail_bound : x * theta - f x ≤ theta - 1 := by
        calc
          x * theta - f x = x * (theta - 1) := by rw [htail_x]; ring
          _ ≤ 1 * (theta - 1) :=
            mul_le_mul_of_nonpos_right hx_one (sub_nonpos.mpr htheta)
          _ = theta - 1 := by ring
      exact htail_bound.trans (le_max_right _ _)
  apply le_antisymm
  · apply restrictedConjugate_le hIci
    intro x hx
    rcases le_total x 1 with hx_one | hx_one
    · exact le_restrictedConjugate hbounded ⟨hx, hx_one⟩
    · have htail_x : f x = x := htail x hx_one
      have htail_bound : x * theta - f x ≤ theta - 1 := by
        calc
          x * theta - f x = x * (theta - 1) := by rw [htail_x]; ring
          _ ≤ 1 * (theta - 1) :=
            mul_le_mul_of_nonpos_right hx_one (sub_nonpos.mpr htheta)
          _ = theta - 1 := by ring
      have hbase := le_restrictedConjugate hbounded
        (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
      have hbase' : theta - 1 ≤ restrictedConjugate f (Icc (0 : ℝ) 1) theta := by
        simpa [htail 1 (by norm_num : (1 : ℝ) ≤ 1)] using hbase
      exact htail_bound.trans hbase'
  · apply restrictedConjugate_le hIcc
    intro x hx
    exact le_restrictedConjugate hboundedIci hx.1

/-- The restricted biconjugate lies below the original function at an
admissible primal point. -/
theorem restrictedBiconjugate_le
    {f : ℝ → ℝ} {primal slopes : Set ℝ} {x : ℝ}
    (hslopes : slopes.Nonempty)
    (hconj_bounded : ∀ θ ∈ slopes,
      BddAbove ((fun y : ℝ => y * θ - f y) '' primal))
    (hx : x ∈ primal) :
    restrictedBiconjugate f primal slopes x ≤ f x := by
  unfold restrictedBiconjugate
  apply restrictedConjugate_le hslopes
  intro θ hθ
  have h := le_restrictedConjugate (hconj_bounded θ hθ) hx
  calc
    θ * x - restrictedConjugate f primal θ =
        x * θ - restrictedConjugate f primal θ := by ring
    _ ≤ f x := by linarith

/-- A single affine minorant gives a lower bound for the restricted
biconjugate. -/
theorem le_restrictedBiconjugate_of_affine_minorant
    {f : ℝ → ℝ} {primal slopes : Set ℝ} {x θ c : ℝ}
    (hprimal : primal.Nonempty)
    (hminor : ∀ y ∈ primal, θ * y + c ≤ f y)
    (hθ : θ ∈ slopes)
    (hbiconj_bounded : BddAbove
      ((fun u : ℝ => u * x - restrictedConjugate f primal u) '' slopes)) :
    θ * x + c ≤ restrictedBiconjugate f primal slopes x := by
  have hconj : restrictedConjugate f primal θ ≤ -c :=
    restrictedConjugate_le_neg_intercept hprimal hminor
  have h := le_restrictedConjugate hbiconj_bounded hθ
  change θ * x - restrictedConjugate f primal θ ≤ _ at h
  exact (by linarith : θ * x + c ≤ θ * x - restrictedConjugate f primal θ).trans h

/-- A biconjugate reconstructs a function whenever every strict sublevel at
the point has a supporting affine minorant whose slope is admissible.  This
is the real, slope-restricted form of the supporting-affine proof of
Fenchel--Moreau duality. -/
theorem restrictedBiconjugate_eq_of_supporting_affines
    {f : ℝ → ℝ} {primal slopes : Set ℝ} {x : ℝ}
    (hprimal : primal.Nonempty) (hslopes : slopes.Nonempty)
    (hconj_bounded : ∀ θ ∈ slopes,
      BddAbove ((fun y : ℝ => y * θ - f y) '' primal))
    (hbiconj_bounded : BddAbove
      ((fun θ : ℝ => θ * x - restrictedConjugate f primal θ) '' slopes))
    (hx : x ∈ primal)
    (hsupport : ∀ q : ℝ, q < f x → ∃ θ c : ℝ,
      θ ∈ slopes ∧ (∀ y ∈ primal, θ * y + c ≤ f y) ∧ q ≤ θ * x + c) :
    restrictedBiconjugate f primal slopes x = f x := by
  apply le_antisymm
  · exact restrictedBiconjugate_le hslopes hconj_bounded hx
  · apply le_of_forall_lt
    intro q hq
    let q' : ℝ := (q + f x) / 2
    have hqq' : q < q' := by
      dsimp [q']
      linarith
    have hq' : q' < f x := by
      dsimp [q']
      linarith
    obtain ⟨θ, c, hθ, hminor, hq_support⟩ := hsupport q' hq'
    exact hqq'.trans_le <|
      hq_support.trans
        (le_restrictedBiconjugate_of_affine_minorant hprimal hminor hθ hbiconj_bounded)

/-- A globally convex continuous real function has a supporting affine
minorant below every strict sublevel at a point. -/
theorem exists_global_affine_minorant_of_convex_continuous
    {f : ℝ → ℝ} {x q : ℝ}
    (hconv : ConvexOn ℝ univ f) (hcont : Continuous f)
    (hq : q < f x) :
    ∃ θ c : ℝ, (∀ y : ℝ, θ * y + c ≤ f y) ∧ θ * x + c = q := by
  obtain ⟨θ, c, hminor, hvalue⟩ :=
    hconv.exists_affine_le_of_lt_real (x := x) (a := q) (by simp) hq
      isClosed_univ (hcont.lowerSemicontinuous.lowerSemicontinuousOn univ)
  refine ⟨θ, c, ?_, hvalue⟩
  intro y
  exact hminor y (mem_univ y)

/-- A global affine minorant puts its slope in the effective slope set. -/
theorem mem_effectiveSlopeSet_of_affine_minorant
    {f : ℝ → ℝ} {primal : Set ℝ} {θ c : ℝ}
    (hminor : ∀ x ∈ primal, θ * x + c ≤ f x) :
    θ ∈ effectiveSlopeSet f primal := by
  refine ⟨-c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h := hminor x hx
  linarith [show x * θ = θ * x by ring]

/-- For a finite-valued convex continuous function on the real line, the
effective-domain biconjugate is the original function.  The result avoids
extended reals while retaining the correct effective slope domain. -/
theorem restrictedBiconjugate_effectiveSlopeSet_eq_of_convex_continuous
    {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f) (hcont : Continuous f)
    (x : ℝ) :
    restrictedBiconjugate f univ (effectiveSlopeSet f univ) x = f x := by
  have hglobal : ∃ θ c : ℝ, ∀ y : ℝ, θ * y + c ≤ f y := by
    obtain ⟨θ, c, hminor, _⟩ :=
      exists_global_affine_minorant_of_convex_continuous hconv hcont
        (x := x) (q := f x - 1) (by linarith)
    exact ⟨θ, c, hminor⟩
  obtain ⟨θ₀, c₀, hminor₀⟩ := hglobal
  have hprimal : (univ : Set ℝ).Nonempty := ⟨x, mem_univ x⟩
  have hslopes : (effectiveSlopeSet f univ).Nonempty :=
    ⟨θ₀, mem_effectiveSlopeSet_of_affine_minorant
      (fun y _ => hminor₀ y)⟩
  have hconj_bounded : ∀ θ ∈ effectiveSlopeSet f univ,
      BddAbove ((fun y : ℝ => y * θ - f y) '' univ) := by
    intro θ hθ
    exact hθ
  have hbiconj_bounded : BddAbove
      ((fun θ : ℝ => θ * x - restrictedConjugate f univ θ) ''
        effectiveSlopeSet f univ) := by
    refine ⟨f x, ?_⟩
    rintro _ ⟨θ, hθ, rfl⟩
    have h := le_restrictedConjugate hθ (show x ∈ (univ : Set ℝ) by simp)
    linarith [show x * θ = θ * x by ring]
  apply restrictedBiconjugate_eq_of_supporting_affines hprimal hslopes
    hconj_bounded hbiconj_bounded (show x ∈ (univ : Set ℝ) by simp)
  intro q hq
  obtain ⟨θ, c, hminor, hvalue⟩ :=
    exists_global_affine_minorant_of_convex_continuous hconv hcont hq
  refine ⟨θ, c,
    mem_effectiveSlopeSet_of_affine_minorant (fun y _ => hminor y), ?_, ?_⟩
  · intro y hy
    exact hminor y
  · rw [hvalue]

/-- A convex function on the nonnegative half-line which agrees with the
identity from `1` onwards lies above the identity everywhere on that
half-line. -/
theorem id_le_of_convexOn_eq_id_on_Ici_one
    {f : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici (0 : ℝ)) f)
    (hid : ∀ y : ℝ, 1 ≤ y → f y = y) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ f x := by
  rcases lt_or_ge x 1 with hlt | hge
  · have hsec := hconv.secant_mono_aux1
      (x := x) (y := 1) (z := 2) hx (by norm_num)
      hlt (by norm_num : (1 : ℝ) < 2)
    rw [hid 1 (by norm_num), hid 2 (by norm_num)] at hsec
    linarith
  · rw [hid x hge]

/-- Restricted Fenchel--Moreau duality on the nonnegative half-line.

If a real-valued function is convex and nondecreasing on `[0,∞)`, and equals
the identity on `[1,∞)`, then its conjugate over `[0,∞)` and its biconjugate
over the slope interval `[0,1]` recover the function.  The proof obtains
supporting affine lines from the real Hahn--Banach separation theorem; the
constant left extension forces their slopes to be nonnegative, while the
identity tail forces them to be at most one.
-/
theorem halfline_restrictedBiconjugate_eq_of_convexOn_monotone_eq_id
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Ici (0 : ℝ)))
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) f)
    (hid : ∀ y : ℝ, 1 ≤ y → f y = y)
    {x : ℝ} (hx : 0 ≤ x) :
    restrictedBiconjugate f (Ici (0 : ℝ)) (Icc (0 : ℝ) 1) x = f x := by
  have hprimal : (Ici (0 : ℝ)).Nonempty := ⟨0, by simp⟩
  have hslopes : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  have hdiag : ∀ y : ℝ, 0 ≤ y → y ≤ f y :=
    fun y hy => id_le_of_convexOn_eq_id_on_Ici_one hconv hid hy
  have hconj_bounded : ∀ θ ∈ Icc (0 : ℝ) 1,
      BddAbove ((fun y : ℝ => y * θ - f y) '' Ici (0 : ℝ)) := by
    intro θ hθ
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hy' : 0 ≤ y := hy
    have hmul : y * θ ≤ y := by
      calc
        y * θ ≤ y * 1 := mul_le_mul_of_nonneg_left hθ.2 hy'
        _ = y := by ring
    linarith [hdiag y hy']
  have hbiconj_bounded : BddAbove
      ((fun θ : ℝ => θ * x - restrictedConjugate f (Ici (0 : ℝ)) θ) ''
        Icc (0 : ℝ) 1) := by
    refine ⟨x + 1, ?_⟩
    rintro _ ⟨θ, hθ, rfl⟩
    have hconj := le_restrictedConjugate (hconj_bounded θ hθ)
      (show (1 : ℝ) ∈ Ici 0 by norm_num)
    have hvalue : f 1 = 1 := hid 1 (by norm_num)
    rw [hvalue] at hconj
    have hconj' : θ - 1 ≤ restrictedConjugate f (Ici (0 : ℝ)) θ := by
      simpa using hconj
    have hmul : θ * x ≤ x := by
      calc
        θ * x ≤ 1 * x := mul_le_mul_of_nonneg_right hθ.2 hx
        _ = x := by ring
    calc
      θ * x - restrictedConjugate f (Ici (0 : ℝ)) θ ≤ θ * x - (θ - 1) :=
        sub_le_sub_left hconj' _
      _ ≤ x + 1 := by linarith [hmul, hθ.1]
  apply restrictedBiconjugate_eq_of_supporting_affines hprimal hslopes
    hconj_bounded hbiconj_bounded hx
  intro q hq
  let F : ℝ → ℝ := fun y => f (max y 0)
  have hmax : ConvexOn ℝ univ (fun y : ℝ => max y 0) := by
    constructor
    · exact convex_univ
    · intro y _ z _ a b ha hb hab
      change max (a * y + b * z) 0 ≤ a * max y 0 + b * max z 0
      apply max_le
      · exact add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left y 0) ha)
          (mul_le_mul_of_nonneg_left (le_max_left z 0) hb)
      · exact add_nonneg
          (mul_nonneg ha (le_max_right y (0 : ℝ)))
          (mul_nonneg hb (le_max_right z (0 : ℝ)))
  have himage : (fun y : ℝ => max y 0) '' univ = Ici 0 := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      exact le_max_right z 0
    · intro hy
      exact ⟨y, mem_univ _, max_eq_left hy⟩
  have hFconv : ConvexOn ℝ univ F := by
    change ConvexOn ℝ univ (f ∘ fun y : ℝ => max y 0)
    apply ConvexOn.comp (s := univ)
    · rw [himage]
      exact hconv
    · exact hmax
    · rw [himage]
      exact hmono
  have hFcont : Continuous F :=
    continuousOn_univ.mp (hFconv.continuousOn isOpen_univ)
  have hqF : q < F x := by
    simpa [F, max_eq_left hx] using hq
  obtain ⟨θ, c, hminor, hvalue⟩ :=
    exists_global_affine_minorant_of_convex_continuous hFconv hFcont hqF
  have hθ0 : 0 ≤ θ := by
    by_contra hθ0
    have hθneg : θ < 0 := lt_of_not_ge hθ0
    let y : ℝ := min 0 ((f 0 - c + 1) / θ)
    have hy0 : y ≤ 0 := min_le_left _ _
    have hydiv : y ≤ (f 0 - c + 1) / θ := min_le_right _ _
    have hmul : f 0 - c + 1 ≤ y * θ :=
      (le_div_iff_of_neg hθneg).mp hydiv
    have htest := hminor y
    have hFy : F y = f 0 := by
      simp [F, max_eq_right hy0]
    rw [hFy] at htest
    nlinarith
  have hθ1 : θ ≤ 1 := by
    by_contra hθ1
    have hθgt : 1 < θ := lt_of_not_ge hθ1
    let y : ℝ := max 1 ((-c + 1) / (θ - 1))
    have hy1 : 1 ≤ y := le_max_left _ _
    have hydiv : (-c + 1) / (θ - 1) ≤ y := le_max_right _ _
    have hmul : -c + 1 ≤ y * (θ - 1) :=
      (div_le_iff₀ (sub_pos.mpr hθgt)).mp hydiv
    have htest := hminor y
    have hFy : F y = y := by
      change f (max y 0) = y
      rw [max_eq_left (zero_le_one.trans hy1)]
      exact hid y hy1
    rw [hFy] at htest
    nlinarith
  refine ⟨θ, c, ⟨hθ0, hθ1⟩, ?_, ?_⟩
  · intro y hy
    have hFy : F y = f y := by
      change f (max y 0) = f y
      rw [max_eq_left hy]
    simpa [hFy] using hminor y
  · rw [hvalue]

end

/-- A compact parameter set can be reduced to finitely many local eventual
estimates, with all of the selected estimates holding eventually at once.

This packages the finite-subcover step that commonly turns pointwise-in-a-
parameter asymptotic estimates into a uniform estimate on a compact set. -/
theorem IsCompact.exists_finset_nhds_subcover_eventually
    {X Y : Type*} [TopologicalSpace X] {K : Set X} {l : Filter Y}
    (hK : IsCompact K) (U : X → Set X)
    (hU : ∀ x ∈ K, U x ∈ nhds x)
    (P : X → Y → Prop)
    (hP : ∀ x ∈ K, ∀ᶠ y in l, P x y) :
    ∃ s : Finset X, (∀ x ∈ s, x ∈ K) ∧ K ⊆ ⋃ x ∈ s, U x ∧
      ∀ᶠ y in l, ∀ x ∈ s, P x y := by
  classical
  obtain ⟨s, hsK, hscover⟩ := hK.elim_nhds_subcover U hU
  refine ⟨s, hsK, hscover, ?_⟩
  rw [Filter.eventually_all_finset]
  intro x hx
  exact hP x (hsK x hx)

/-- Finitely many real constants have a common strictly positive upper bound.

This is convenient when a finite subcover supplies a separate multiplicative
constant for each member of the cover. -/
theorem exists_pos_uniform_majorant_finset
    {ι : Type*} (s : Finset ι) (C : ι → ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ i ∈ s, C i ≤ M := by
  classical
  refine ⟨(∑ i ∈ s, |C i|) + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun i _ => abs_nonneg (C i)) zero_lt_one
  · intro i hi
    calc
      C i ≤ |C i| := le_abs_self _
      _ ≤ ∑ j ∈ s, |C j| := by
        exact Finset.single_le_sum (f := fun j => |C j|)
          (fun j _ => abs_nonneg _) hi
      _ ≤ (∑ j ∈ s, |C j|) + 1 := by linarith

end Auto.ConvexDuality
