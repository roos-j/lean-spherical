import LeanSpherical.HarmonicAnalysis.PowerWeights.ThinRadialPartition

/-!
# Geometry of the smooth thin radial partition

This small bridge records that the literal smooth partition used in the
central negative-weight argument has precisely the buffered support accepted
by the five-neighbour sampling lemma.
-/

namespace LeanSpherical.HarmonicAnalysis

open Metric MeasureTheory Set

noncomputable section

/-- The smooth thin partition piece vanishes outside the quarter-width
buffered annulus. -/
theorem thinRadialPartition_zero_of_not_mem_bufferedThinRadialSlice
    {d : Nat} {s : Real} (hs : 0 < s) (m : Nat)
    (hm : 0 < s * ((m : Real) - 1 / 4)) {y : Euclidean d}
    (hy : y ∉ bufferedThinRadialSlice d s (m : Int)) :
    thinRadialPartition d s hs m y = 0 := by
  by_cases houter : s * ((m : Real) + 5 / 4) <= ‖y‖
  · exact thinRadialPartition_zero_of_outer_le hs m hm houter
  · have houterlt : ‖y‖ < s * ((m : Real) + 5 / 4) :=
      lt_of_not_ge houter
    have hclosed : y ∈ closedBall (0 : Euclidean d)
        (s * ((m : Real) + 5 / 4)) := by
      simpa only [mem_closedBall, dist_zero_right] using houterlt.le
    have hinner : y ∈ ball (0 : Euclidean d)
        (s * ((m : Real) - 1 / 4)) := by
      by_contra hnotinner
      apply hy
      unfold bufferedThinRadialSlice euclideanAnnulus
      exact ⟨hclosed, hnotinner⟩
    apply thinRadialPartition_zero_of_norm_le hs m hm
    have hinnerlt : ‖y‖ < s * ((m : Real) - 1 / 4) := by
      simpa only [mem_ball, dist_zero_right] using hinner
    exact hinnerlt.le

/-- A smooth partition piece contributes to the parameter window only for
the same five indices as a hard thin slice. -/
theorem thinRadialPartition_sample_zero_of_index_not_mem
    {d : Nat} {s r : Real} {m : Nat} {mu : Int} {x : Euclidean d}
    {omega : sphere (0 : Euclidean d) 1}
    (hs : 0 < s) (hr0 : 0 <= r) (hx : ‖x‖ <= s / 2)
    (hr : r ∈ thinRadiusWindow s mu)
    (hmpos : 0 < s * ((m : Real) - 1 / 4))
    (hm : (m : Int) ∉ Finset.Icc (mu - 2) (mu + 2)) :
    thinRadialPartition d s hs m (x + r • (omega : Euclidean d)) = 0 := by
  apply bufferedThinRadialSlice_sample_zero_of_index_not_mem
    (m := (m : Int)) (f := fun y => thinRadialPartition d s hs m y)
      hs hr0 hx hr (by
        intro y hy
        exact thinRadialPartition_zero_of_not_mem_bufferedThinRadialSlice
          (d := d) hs m hmpos hy) hm

/-- Multiplying a Schwartz input by a smooth thin partition piece remains
supported in the precise buffered annulus.  This is written using the
standard bilinear Schwartz pairing, so the result can be passed directly to
the cap-shell theorem. -/
theorem thinRadialPartition_piece_zero_of_not_mem_bufferedThinRadialSlice
    {d : Nat} {s : Real} (hs : 0 < s) (f : SchwartzMap (Euclidean d) Complex)
    (m : Nat) (hm : 0 < s * ((m : Real) - 1 / 4)) {y : Euclidean d}
    (hy : y ∉ bufferedThinRadialSlice d s (m : Int)) :
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
      (thinRadialPartition d s hs m)) y = 0 := by
  rw [SchwartzMap.pairing_apply_apply]
  rw [thinRadialPartition_zero_of_not_mem_bufferedThinRadialSlice
    (d := d) hs m hm hy]
  simp

/-- Exact annular-support form of the preceding fact.  This is exactly the
last hypothesis of the entropy cap-shell estimate. -/
theorem thinRadialPartition_piece_support_annulus
    {d : Nat} {s : Real} (hs : 0 < s) (f : SchwartzMap (Euclidean d) Complex)
    (m : Nat) (hm : 0 < s * ((m : Real) - 1 / 4)) :
    ∀ y, y ∉ euclideanAnnulus d
        (s * ((m : Real) - 1 / 4)) (s * ((m : Real) + 5 / 4)) ->
      (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
        (thinRadialPartition d s hs m)) y = 0 := by
  intro y hy
  apply thinRadialPartition_piece_zero_of_not_mem_bufferedThinRadialSlice
    hs f m hm
  simpa only [bufferedThinRadialSlice, Int.cast_natCast] using hy

/-- A finite block of thin radial pieces exactly reconstructs an input whose
support lies in the corresponding annulus. -/
theorem sum_thinRadialPartition_piece_Icc_eq_of_support
    {d : Nat} {s : Real} (hs : 0 < s)
    (f : SchwartzMap (Euclidean d) Complex) (lo hi : Nat)
    (hlohi : lo <= hi)
    (hlo : 0 < s * ((lo : Real) - 1 / 4))
    (hhi : 0 < s * (((hi + 1 : Nat) : Real) - 1 / 4))
    (hsupport : ∀ x : Euclidean d, f x ≠ 0 →
      s * ((lo : Real) + 1 / 4) <= ‖x‖ /\
        ‖x‖ <= s * (((hi + 1 : Nat) : Real) - 1 / 4)) :
    (∑ m ∈ Finset.Icc lo hi,
      SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
        (thinRadialPartition d s hs m)) = f := by
  ext x
  by_cases hfx : f x = 0
  · simp [hfx, SchwartzMap.pairing_apply_apply]
  · obtain ⟨hbelow, habove⟩ := hsupport x hfx
    have hsum := sum_thinRadialPartition_Icc_eq_one hs lo hi hlohi hlo hhi hbelow habove
    rw [SchwartzMap.sum_apply]
    simp only [SchwartzMap.pairing_apply_apply]
    change (∑ m ∈ Finset.Icc lo hi,
      f x * thinRadialPartition d s hs m x) = f x
    rw [← Finset.mul_sum, hsum, mul_one]

/-- The actual thin Schwartz input vanishes at a spherical sample outside
the five permitted parameter windows. -/
theorem thinRadialPartition_piece_sample_zero_of_index_not_mem
    {d : Nat} {s r : Real} {m : Nat} {mu : Int} {x : Euclidean d}
    {omega : sphere (0 : Euclidean d) 1}
    (hs : 0 < s) (hr0 : 0 <= r) (hx : ‖x‖ <= s / 2)
    (hr : r ∈ thinRadiusWindow s mu)
    (f : SchwartzMap (Euclidean d) Complex)
    (hmpos : 0 < s * ((m : Real) - 1 / 4))
    (hm : (m : Int) ∉ Finset.Icc (mu - 2) (mu + 2)) :
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
      (thinRadialPartition d s hs m))
        (x + r • (omega : Euclidean d)) = 0 := by
  rw [SchwartzMap.pairing_apply_apply]
  rw [thinRadialPartition_sample_zero_of_index_not_mem
    hs hr0 hx hr hmpos hm]
  simp

/-- The thin Schwartz product has the pointwise norm bound needed to
reassemble its input moments. -/
theorem norm_thinRadialPartition_piece_le_two_mul
    {d : Nat} {s : Real} (hs : 0 < s) (f : SchwartzMap (Euclidean d) Complex)
    (m : Nat) (x : Euclidean d) :
    ‖(SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
      (thinRadialPartition d s hs m)) x‖ <= 2 * ‖f x‖ := by
  rw [SchwartzMap.pairing_apply_apply]
  change ‖f x * thinRadialPartition d s hs m x‖ <= 2 * ‖f x‖
  rw [norm_mul]
  calc
    ‖f x‖ * ‖thinRadialPartition d s hs m x‖ <= ‖f x‖ * 2 :=
      mul_le_mul_of_nonneg_left (norm_thinRadialPartition_le_two hs m x) (norm_nonneg _)
    _ = 2 * ‖f x‖ := by ring

/-- At one spatial point, at most two of any finite family of smooth thin
partition products can be nonzero.  The input family is assumed to start
past the origin, as it does in the central annular decomposition. -/
theorem thinRadialPartition_piece_active_card_le_two
    {d : Nat} {s : Real} (hs : 0 < s) (f : SchwartzMap (Euclidean d) Complex)
    (M : Finset Nat)
    (hM : ∀ m ∈ M, 0 < s * ((m : Real) - 1 / 4))
    (y : Euclidean d) :
    (M.filter fun m =>
      (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
        (thinRadialPartition d s hs m)) y ≠ 0).card <= 2 := by
  classical
  let K : Finset Nat := M.filter fun m =>
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
      (thinRadialPartition d s hs m)) y ≠ 0
  by_cases hK : K.Nonempty
  · let m0 : Nat := K.min' hK
    have hm0K : m0 ∈ K := by
      exact Finset.min'_mem K hK
    have hmem {m : Nat} (hmK : m ∈ K) :
        y ∈ bufferedThinRadialSlice d s (m : Int) := by
      by_contra hymem
      have hmne :
          (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
            (thinRadialPartition d s hs m)) y ≠ 0 :=
        (Finset.mem_filter.mp hmK).2
      apply hmne
      exact thinRadialPartition_piece_zero_of_not_mem_bufferedThinRadialSlice
        hs f m (hM m (Finset.filter_subset _ _ hmK)) hymem
    have hupper (m : Nat) (hmK : m ∈ K) : m <= m0 + 1 := by
      by_contra hnot
      have hgap : m0 + 2 <= m := by omega
      have hm0mem := hmem hm0K
      have hmmem := hmem hmK
      have hm0upper : ‖y‖ <= s * ((m0 : Real) + 5 / 4) := by
        simpa only [bufferedThinRadialSlice, euclideanAnnulus,
          mem_closedBall, dist_zero_right, Int.cast_natCast] using hm0mem.1
      have hmlower : s * ((m : Real) - 1 / 4) <= ‖y‖ := by
        exact le_of_not_gt (by
          simpa only [bufferedThinRadialSlice, euclideanAnnulus,
            mem_ball, dist_zero_right, Int.cast_natCast] using hmmem.2)
      have hgapReal : (m0 : Real) + 2 <= (m : Real) := by
        exact_mod_cast hgap
      nlinarith
    have hsubset : K ⊆ Finset.Icc m0 (m0 + 1) := by
      intro m hmK
      apply Finset.mem_Icc.mpr
      constructor
      · exact Finset.min'_le K m hmK
      · exact hupper m hmK
    change K.card <= 2
    calc
      K.card <= (Finset.Icc m0 (m0 + 1)).card :=
        Finset.card_le_card hsubset
      _ = 2 := by
        rw [Nat.card_Icc]
        omega
  · have hKempty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    change K.card <= 2
    simp [hKempty]

/-- The finite family of thin partition products has a uniform pointwise
power-moment bound.  It combines the norm-two cutoff bound with the
two-fold radial overlap. -/
theorem sum_enorm_rpow_thinRadialPartition_piece_le
    {d : Nat} {s : Real} (hs : 0 < s) (f : SchwartzMap (Euclidean d) Complex)
    (M : Finset Nat)
    (hM : ∀ m ∈ M, 0 < s * ((m : Real) - 1 / 4))
    {p : Real} (hp : 0 < p) (y : Euclidean d) :
    (∑ m ∈ M,
      ‖(SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
        (thinRadialPartition d s hs m)) y‖ₑ ^ p) <=
      ((ENNReal.ofReal 2) ^ p * 2) * ‖f y‖ₑ ^ p := by
  classical
  let g : Nat -> SchwartzMap (Euclidean d) Complex := fun m =>
    SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
      (thinRadialPartition d s hs m)
  let K : Finset Nat := M.filter fun m => g m y ≠ 0
  have hpiece (m : Nat) :
      ‖g m y‖ₑ ^ p <= (ENNReal.ofReal 2) ^ p * ‖f y‖ₑ ^ p := by
    have hnorm : ‖g m y‖ₑ <= ENNReal.ofReal 2 * ‖f y‖ₑ := by
      calc
        ‖g m y‖ₑ = ENNReal.ofReal ‖g m y‖ := ofReal_norm_eq_enorm _ |>.symm
        _ <= ENNReal.ofReal (2 * ‖f y‖) :=
          ENNReal.ofReal_le_ofReal
            (norm_thinRadialPartition_piece_le_two_mul hs f m y)
        _ = ENNReal.ofReal 2 * ENNReal.ofReal ‖f y‖ := by
          rw [ENNReal.ofReal_mul (by norm_num)]
        _ = ENNReal.ofReal 2 * ‖f y‖ₑ := by
          rw [ofReal_norm_eq_enorm]
    calc
      ‖g m y‖ₑ ^ p <= (ENNReal.ofReal 2 * ‖f y‖ₑ) ^ p :=
        ENNReal.rpow_le_rpow hnorm hp.le
      _ = (ENNReal.ofReal 2) ^ p * ‖f y‖ₑ ^ p :=
        ENNReal.mul_rpow_of_nonneg _ _ hp.le
  have hsum_eq :
      (∑ m ∈ M, ‖g m y‖ₑ ^ p) = ∑ m ∈ K, ‖g m y‖ₑ ^ p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hmM
    by_cases hmzero : g m y = 0
    · simp [hmzero, ENNReal.zero_rpow_of_pos hp]
    · simp [hmzero]
  have hcard : (K.card : ENNReal) <= 2 := by
    exact_mod_cast thinRadialPartition_piece_active_card_le_two hs f M hM y
  have hsum :
      (∑ m ∈ K, ‖g m y‖ₑ ^ p) <=
        (K.card : ENNReal) * ((ENNReal.ofReal 2) ^ p * ‖f y‖ₑ ^ p) := by
    calc
      (∑ m ∈ K, ‖g m y‖ₑ ^ p) <=
          ∑ _m ∈ K, (ENNReal.ofReal 2) ^ p * ‖f y‖ₑ ^ p :=
        Finset.sum_le_sum (fun m hm => hpiece m)
      _ = (K.card : ENNReal) * ((ENNReal.ofReal 2) ^ p * ‖f y‖ₑ ^ p) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  change (∑ m ∈ M, ‖g m y‖ₑ ^ p) <=
    ((ENNReal.ofReal 2) ^ p * 2) * ‖f y‖ₑ ^ p
  rw [hsum_eq]
  calc
    (∑ m ∈ K, ‖g m y‖ₑ ^ p) <=
        (K.card : ENNReal) * ((ENNReal.ofReal 2) ^ p * ‖f y‖ₑ ^ p) := hsum
    _ <= 2 * ((ENNReal.ofReal 2) ^ p * ‖f y‖ₑ ^ p) :=
      mul_le_mul_of_nonneg_right hcard bot_le
    _ = ((ENNReal.ofReal 2) ^ p * 2) * ‖f y‖ₑ ^ p := by ring

/-- Integrating the bounded-overlap estimate for a finite family of thin
radial pieces.  This is the input-side summation used after the cap estimates
have been summed over the finitely many central radial indices. -/
theorem lintegral_sum_enorm_rpow_thinRadialPartition_piece_le
    {d : Nat} {s : Real} (hs : 0 < s) (f : SchwartzMap (Euclidean d) Complex)
    (M : Finset Nat)
    (hM : ∀ m ∈ M, 0 < s * ((m : Real) - 1 / 4))
    {p : Real} (hp : 0 < p) (mu : Measure (Euclidean d)) :
    (∫⁻ y : Euclidean d, ∑ m ∈ M,
      ‖(SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
        (thinRadialPartition d s hs m)) y‖ₑ ^ p ∂mu) ≤
      ((ENNReal.ofReal 2) ^ p * 2) *
        ∫⁻ y : Euclidean d, ‖f y‖ₑ ^ p ∂mu := by
  calc
    (∫⁻ y : Euclidean d, ∑ m ∈ M,
        ‖(SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
          (thinRadialPartition d s hs m)) y‖ₑ ^ p ∂mu) ≤
        ∫⁻ y : Euclidean d,
          ((ENNReal.ofReal 2) ^ p * 2) * ‖f y‖ₑ ^ p ∂mu := by
            apply lintegral_mono
            intro y
            exact sum_enorm_rpow_thinRadialPartition_piece_le hs f M hM hp y
    _ = ((ENNReal.ofReal 2) ^ p * 2) *
        ∫⁻ y : Euclidean d, ‖f y‖ₑ ^ p ∂mu := by
          change (∫⁻ y : Euclidean d, ((ENNReal.ofReal 2) ^ p * 2) *
              (fun z : Euclidean d => ‖f z‖ₑ ^ p) y ∂mu) = _
          exact lintegral_const_mul _
            (ENNReal.continuous_rpow_const.measurable.comp
              f.continuous.enorm.measurable)

/-- Split a finite thin radial reconstruction into the fifteen central
indices for a parameter window and its two integer tails.  The estimate of
the two tails is analytic; this lemma only supplies the exact finite
Schwartz-map identity used to feed that estimate. -/
theorem sum_thinRadialPartition_piece_split_central_tails
    {d : Nat} {s : Real} (hs : 0 < s)
    (f : SchwartzMap (Euclidean d) Complex) (M : Finset Nat) (mu : Int)
    (hreconstruct :
      (∑ m ∈ M,
        SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
          (thinRadialPartition d s hs m)) = f) :
    f =
      (∑ m ∈ M.filter (fun (m : Nat) =>
        (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)),
        SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
          (thinRadialPartition d s hs m)) +
        (∑ m ∈ M.filter (fun (m : Nat) => (m : Int) ≤ mu - 8),
          SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
            (thinRadialPartition d s hs m)) +
          ∑ m ∈ M.filter (fun (m : Nat) => mu + 8 ≤ (m : Int)),
            SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
              (thinRadialPartition d s hs m) := by
  classical
  let g : Nat → SchwartzMap (Euclidean d) Complex := fun m =>
    SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
      (thinRadialPartition d s hs m)
  have hterm (m : Nat) :
      (if (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7) then g m else 0) +
          (if (m : Int) ≤ mu - 8 then g m else 0) +
          (if mu + 8 ≤ (m : Int) then g m else 0) = g m := by
    rcases thinRadial_index_le_or_mem_central_or_ge m mu with hlow | hrest
    · have hcentralfalse : ¬ ((m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)) := by
        rw [Finset.mem_Icc]
        omega
      have hhighfalse : ¬ (mu + 8 ≤ (m : Int)) := by omega
      simp [hcentralfalse, hlow, hhighfalse]
    · rcases hrest with hcentral | hhigh
      · have hlowfalse : ¬ ((m : Int) ≤ mu - 8) := by
          rw [Finset.mem_Icc] at hcentral
          omega
        have hhighfalse : ¬ (mu + 8 ≤ (m : Int)) := by
          rw [Finset.mem_Icc] at hcentral
          omega
        simp [hcentral, hlowfalse, hhighfalse]
      · have hcentralfalse : ¬ ((m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)) := by
          rw [Finset.mem_Icc]
          omega
        have hlowfalse : ¬ ((m : Int) ≤ mu - 8) := by omega
        simp [hcentralfalse, hlowfalse, hhigh]
  change f =
    (∑ m ∈ M.filter (fun (m : Nat) =>
      (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)), g m) +
      (∑ m ∈ M.filter (fun (m : Nat) => (m : Int) ≤ mu - 8), g m) +
        ∑ m ∈ M.filter (fun (m : Nat) => mu + 8 ≤ (m : Int)), g m
  calc
    f = ∑ m ∈ M, g m := by simpa only [g] using hreconstruct.symm
    _ =
        (∑ m ∈ M.filter (fun (m : Nat) =>
          (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)), g m) +
          (∑ m ∈ M.filter (fun (m : Nat) => (m : Int) ≤ mu - 8), g m) +
            ∑ m ∈ M.filter (fun (m : Nat) => mu + 8 ≤ (m : Int)), g m := by
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      symm
      exact hterm m

end

end LeanSpherical.HarmonicAnalysis
