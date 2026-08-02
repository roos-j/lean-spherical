import LeanSpherical.Codex.Spherical.PowerWeights.RelativeMovingCapInterval
import LeanSpherical.Codex.Spherical.PowerWeights.FiniteFrequency
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LeanSpherical.HarmonicAnalysis

open Filter MeasureTheory Metric Set
open scoped ENNReal ContDiff NNReal Topology

/-- The additive radial slice at physical width s. -/
def thinRadialSlice (d : Nat) (s : Real) (m : Int) : Set (Euclidean d) :=
  euclideanAnnulus d (s * (m : Real)) (s * ((m : Real) + 1))

/-- The radius window associated to one thin radial slice. -/
def thinRadiusWindow (s : Real) (mu : Int) : Set Real :=
  Icc (s * ((mu : Real) - 1)) (s * ((mu : Real) + 2))

/-- The buffered version of a thin radial slice.  A smooth cutoff can equal
one on the unbuffered slice while being supported in this enlargement. -/
def bufferedThinRadialSlice (d : Nat) (s : Real) (m : Int) :
    Set (Euclidean d) :=
  euclideanAnnulus d (s * ((m : Real) - 1 / 4))
    (s * ((m : Real) + 5 / 4))

/-- If a spherical sample at an output scale at most s / 2 lands in
the mth radial slice, then only one of five neighbouring parameter
windows can be responsible. -/
theorem thinRadialSlice_index_mem_Icc_of_sample
    {d : Nat} {s r : Real} {m mu : Int} {x : Euclidean d}
    {omega : sphere (0 : Euclidean d) 1}
    (hs : 0 < s) (hr0 : 0 <= r) (hx : ‖x‖ <= s / 2)
    (hr : r ∈ thinRadiusWindow s mu)
    (hy : x + r • (omega : Euclidean d) ∈ thinRadialSlice d s m) :
    m ∈ Finset.Icc (mu - 2) (mu + 2) := by
  have homega : ‖(omega : Euclidean d)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp omega.property
  have hrs : ‖r • (omega : Euclidean d)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0, homega, mul_one]
  have hy_upper : ‖x + r • (omega : Euclidean d)‖ <=
      s * ((m : Real) + 1) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy.1
  have hy_lower : s * (m : Real) <= ‖x + r • (omega : Euclidean d)‖ := by
    exact le_of_not_gt (by
      simpa only [Metric.mem_ball, dist_zero_right] using hy.2)
  have hsample_upper : ‖x + r • (omega : Euclidean d)‖ <= ‖x‖ + r := by
    calc
      ‖x + r • (omega : Euclidean d)‖ <= ‖x‖ + ‖r • (omega : Euclidean d)‖ :=
        norm_add_le _ _
      _ = ‖x‖ + r := by rw [hrs]
  have hsample_lower : r <= ‖x + r • (omega : Euclidean d)‖ + ‖x‖ := by
    calc
      r = ‖r • (omega : Euclidean d)‖ := hrs.symm
      _ = ‖(x + r • (omega : Euclidean d)) - x‖ := by
        congr 1
        abel
      _ <= ‖x + r • (omega : Euclidean d)‖ + ‖x‖ := norm_sub_le _ _
  have hrlo : s * ((mu : Real) - 1) <= r := hr.1
  have hrhi : r <= s * ((mu : Real) + 2) := hr.2
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra hnot
    have hmmu : m <= mu - 3 := by omega
    have hmmu_real : (m : Real) <= (mu : Real) - 3 := by
      exact_mod_cast hmmu
    nlinarith
  · by_contra hnot
    have hmum : mu + 3 <= m := by omega
    have hmum_real : (mu : Real) + 3 <= (m : Real) := by
      exact_mod_cast hmum
    nlinarith

/-- The five-neighbour sampling fact remains true for a slice enlarged by a
quarter of its width on either side, which is the support margin supplied by
the smooth cutoff. -/
theorem bufferedThinRadialSlice_index_mem_Icc_of_sample
    {d : Nat} {s r : Real} {m mu : Int} {x : Euclidean d}
    {omega : sphere (0 : Euclidean d) 1}
    (hs : 0 < s) (hr0 : 0 <= r) (hx : ‖x‖ <= s / 2)
    (hr : r ∈ thinRadiusWindow s mu)
    (hy : x + r • (omega : Euclidean d) ∈ bufferedThinRadialSlice d s m) :
    m ∈ Finset.Icc (mu - 2) (mu + 2) := by
  have homega : ‖(omega : Euclidean d)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp omega.property
  have hrs : ‖r • (omega : Euclidean d)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0, homega, mul_one]
  have hy_upper : ‖x + r • (omega : Euclidean d)‖ <=
      s * ((m : Real) + 5 / 4) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy.1
  have hy_lower : s * ((m : Real) - 1 / 4) <=
      ‖x + r • (omega : Euclidean d)‖ := by
    exact le_of_not_gt (by
      simpa only [Metric.mem_ball, dist_zero_right] using hy.2)
  have hsample_upper : ‖x + r • (omega : Euclidean d)‖ <= ‖x‖ + r := by
    calc
      ‖x + r • (omega : Euclidean d)‖ <= ‖x‖ + ‖r • (omega : Euclidean d)‖ :=
        norm_add_le _ _
      _ = ‖x‖ + r := by rw [hrs]
  have hsample_lower : r <= ‖x + r • (omega : Euclidean d)‖ + ‖x‖ := by
    calc
      r = ‖r • (omega : Euclidean d)‖ := hrs.symm
      _ = ‖(x + r • (omega : Euclidean d)) - x‖ := by
        congr 1
        abel
      _ <= ‖x + r • (omega : Euclidean d)‖ + ‖x‖ := norm_sub_le _ _
  have hrlo : s * ((mu : Real) - 1) <= r := hr.1
  have hrhi : r <= s * ((mu : Real) + 2) := hr.2
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra hnot
    have hmmu : m <= mu - 3 := by omega
    have hmmu_real : (m : Real) <= (mu : Real) - 3 := by
      exact_mod_cast hmmu
    nlinarith
  · by_contra hnot
    have hmum : mu + 3 <= m := by omega
    have hmum_real : (mu : Real) + 3 <= (m : Real) := by
      exact_mod_cast hmum
    nlinarith

theorem thinRadialSlice_sample_zero_of_index_not_mem
    {d : Nat} {s r : Real} {m mu : Int} {x : Euclidean d}
    {omega : sphere (0 : Euclidean d) 1} (f : Euclidean d -> Complex)
    (hs : 0 < s) (hr0 : 0 <= r) (hx : ‖x‖ <= s / 2)
    (hr : r ∈ thinRadiusWindow s mu)
    (hf : ∀ y, y ∉ thinRadialSlice d s m -> f y = 0)
    (hm : m ∉ Finset.Icc (mu - 2) (mu + 2)) :
    f (x + r • (omega : Euclidean d)) = 0 := by
  apply hf
  intro hy
  exact hm (thinRadialSlice_index_mem_Icc_of_sample hs hr0 hx hr hy)

/-- A slice-supported input cannot contribute to a parameter window outside
its five permitted neighbours, also for the buffered smooth support. -/
theorem bufferedThinRadialSlice_sample_zero_of_index_not_mem
    {d : Nat} {s r : Real} {m mu : Int} {x : Euclidean d}
    {omega : sphere (0 : Euclidean d) 1} (f : Euclidean d -> Complex)
    (hs : 0 < s) (hr0 : 0 <= r) (hx : ‖x‖ <= s / 2)
    (hr : r ∈ thinRadiusWindow s mu)
    (hf : ∀ y, y ∉ bufferedThinRadialSlice d s m -> f y = 0)
    (hm : m ∉ Finset.Icc (mu - 2) (mu + 2)) :
    f (x + r • (omega : Euclidean d)) = 0 := by
  apply hf
  intro hy
  exact hm (bufferedThinRadialSlice_index_mem_Icc_of_sample hs hr0 hx hr hy)

theorem thinRadialSlice_neighbor_card_le_five (M : Finset Int) (m : Int) :
    (M.filter fun mu => m ∈ Finset.Icc (mu - 2) (mu + 2)).card <= 5 := by
  have hsubset :
      M.filter (fun mu => m ∈ Finset.Icc (mu - 2) (mu + 2)) ⊆
        Finset.Icc (m - 2) (m + 2) := by
    intro mu hmu
    have h : m ∈ Finset.Icc (mu - 2) (mu + 2) :=
      (Finset.mem_filter.mp hmu).2
    simp only [Finset.mem_Icc] at h ⊢
    omega
  calc
    (M.filter fun mu => m ∈ Finset.Icc (mu - 2) (mu + 2)).card <=
        (Finset.Icc (m - 2) (m + 2)).card :=
      Finset.card_le_card hsubset
    _ = 5 := by
      rw [Int.card_Icc]
      omega

/-- A smooth cutoff which is one on an arbitrary positive thin annulus and
vanishes outside its prescribed thin enlargement. -/
theorem exists_schwartz_thinRadialAnnular_cutoff
    (d : Nat) {a b eps : Real} (ha : 0 < a) (hab : a <= b)
    (heps : 0 < eps) (hepsa : eps < a) :
    ∃ eta : SchwartzMap (Euclidean d) Complex,
      (∀ x : Euclidean d, a <= ‖x‖ -> ‖x‖ <= b -> eta x = 1) ∧
      (∀ x : Euclidean d, ‖x‖ <= a - eps -> eta x = 0) ∧
      (∀ x : Euclidean d, b + eps <= ‖x‖ -> eta x = 0) ∧
      ∀ x : Euclidean d, ‖eta x‖ <= 1 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hain : 0 < a - eps := by linarith
  let outer : ContDiffBump (0 : Euclidean d) :=
    ⟨b, b + eps, hb, by linarith⟩
  let inner : ContDiffBump (0 : Euclidean d) :=
    ⟨a - eps, a, hain, by linarith⟩
  let o : Euclidean d -> Complex := fun x => (outer x : Complex)
  let i : Euclidean d -> Complex := fun x => (inner x : Complex)
  let q : Euclidean d -> Complex := fun x => o x * (1 - i x)
  have hoCompact : HasCompactSupport o := by
    change HasCompactSupport (Complex.ofRealCLM ∘ outer)
    exact outer.hasCompactSupport.comp_left (by rfl)
  have hoSmooth : ContDiff Real (⊤ : ENat) o := by
    change ContDiff Real (⊤ : ENat) (Complex.ofRealCLM ∘ outer)
    exact Complex.ofRealCLM.contDiff.comp outer.contDiff
  have hiSmooth : ContDiff Real (⊤ : ENat) i := by
    change ContDiff Real (⊤ : ENat) (Complex.ofRealCLM ∘ inner)
    exact Complex.ofRealCLM.contDiff.comp inner.contDiff
  have hqCompact : HasCompactSupport q := by
    change HasCompactSupport (fun x => o x * (1 - i x))
    exact hoCompact.mul_right
  have hqSmooth : ContDiff Real (⊤ : ENat) q := by
    change ContDiff Real (⊤ : ENat) (fun x => o x * (1 - i x))
    exact hoSmooth.mul (contDiff_const.sub hiSmooth)
  let eta : SchwartzMap (Euclidean d) Complex := hqCompact.toSchwartzMap hqSmooth
  refine ⟨eta, ?_, ?_, ?_, ?_⟩
  · intro x hax hxb
    have houter : outer x = 1 := by
      apply outer.one_of_mem_closedBall
      change x ∈ closedBall (0 : Euclidean d) b
      simpa only [mem_closedBall, dist_zero_right] using hxb
    have hinner : inner x = 0 := by
      apply inner.zero_of_le_dist
      simpa only [dist_zero_right] using hax
    change o x * (1 - i x) = 1
    simp [o, i, houter, hinner]
  · intro x hx
    have hinner : inner x = 1 := by
      apply inner.one_of_mem_closedBall
      change x ∈ closedBall (0 : Euclidean d) (a - eps)
      simpa only [mem_closedBall, dist_zero_right] using hx
    change o x * (1 - i x) = 0
    simp [i, hinner]
  · intro x hx
    have houter : outer x = 0 := by
      apply outer.zero_of_le_dist
      simpa only [dist_zero_right] using hx
    change o x * (1 - i x) = 0
    simp [o, houter]
  · intro x
    have houter_nonneg : 0 <= outer x := outer.nonneg
    have hinner_nonneg : 0 <= inner x := inner.nonneg
    have hsub_nonneg : 0 <= 1 - inner x := sub_nonneg.mpr inner.le_one
    have hsub_le_one : 1 - inner x <= 1 := by linarith
    have hnonneg : 0 <= outer x * (1 - inner x) :=
      mul_nonneg houter_nonneg hsub_nonneg
    have hbound : outer x * (1 - inner x) <= 1 := by
      exact mul_le_one₀
        outer.le_one hsub_nonneg hsub_le_one
    change ‖o x * (1 - i x)‖ <= 1
    have heq : o x * (1 - i x) = (outer x * (1 - inner x) : Real) := by
      simp [o, i, Complex.ofReal_mul, Complex.ofReal_sub]
    rw [heq]
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hnonneg]
    exact hbound

/-- A bounded additive radius interval is covered by the finitely many
three-width thin windows indexed between its floor and ceiling scales.
The floor choice is deliberately explicit so later finite reassembly can
sum over this exact `Finset.Icc`. -/
theorem exists_mem_thinRadiusWindow_finset_cover
    {A B s r : Real} (hs : 0 < s) (hr : r ∈ Icc A B) :
    ∃ μ ∈ Finset.Icc ⌊A / s⌋ ⌈B / s⌉, r ∈ thinRadiusWindow s μ := by
  let μ : Int := ⌊r / s⌋
  refine ⟨μ, ?_, ?_⟩
  · apply Finset.mem_Icc.mpr
    constructor
    · dsimp only [μ]
      exact Int.floor_le_floor ((div_le_div_iff_of_pos_right hs).2 hr.1)
    · calc
        μ = ⌊r / s⌋ := rfl
        _ ≤ ⌈r / s⌉ := Int.floor_le_ceil _
        _ ≤ ⌈B / s⌉ := Int.ceil_le_ceil ((div_le_div_iff_of_pos_right hs).2 hr.2)
  · unfold thinRadiusWindow
    constructor
    · have hfloor : ((μ : Int) : Real) ≤ r / s := by
        dsimp only [μ]
        exact Int.floor_le _
      have hmul : s * (μ : Real) ≤ r := by
        rw [mul_comm]
        exact (le_div_iff₀ hs).mp hfloor
      nlinarith

    · have hfloor : r / s < ((μ : Int) : Real) + 1 := by
        dsimp only [μ]
        exact Int.lt_floor_add_one _
      have hmul : r < (((μ : Int) : Real) + 1) * s := by
        exact (div_lt_iff₀ hs).mp hfloor
      nlinarith

/-- The integer input indices split into the central fifteen indices and the
two families to which the off-window estimates apply.  Keeping this elementary
split in the geometry file avoids repeating the integer/cast bookkeeping in
the cap--tail reassembly. -/
theorem thinRadial_index_le_or_mem_central_or_ge
    (m : Nat) (mu : Int) :
    (m : Int) <= mu - 8 \/
      (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7) \/
        mu + 8 <= (m : Int) := by
  by_cases hlow : (m : Int) <= mu - 8
  · exact Or.inl hlow
  by_cases hhigh : mu + 8 <= (m : Int)
  · exact Or.inr (Or.inr hhigh)
  right
  left
  rw [Finset.mem_Icc]
  constructor <;> omega

/-- The lower integer tail condition in the form required by the moving
window gap lemma. -/
theorem thinRadial_lower_tail_gap_of_int_le
    {m : Nat} {mu : Int} (h : (m : Int) <= mu - 8) :
    (m : Real) + 8 <= (mu : Real) := by
  exact_mod_cast (by omega : (m : Int) + 8 <= mu)

/-- The upper integer tail condition in the form required by the moving
window gap lemma. -/
theorem thinRadial_upper_tail_gap_of_int_ge
    {m : Nat} {mu : Int} (h : mu + 8 <= (m : Int)) :
    (mu : Real) + 8 <= (m : Real) := by
  exact_mod_cast h

/-- A fixed input thin index can be central for at most fifteen parameter
windows.  This is the finite-overlap count used after summing the central
cap moments over the radius windows. -/
theorem thinRadial_central_piece_card_le_fifteen
    (M : Finset Nat) (mu : Int) :
    (M.filter fun m : Nat =>
      (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)).card ≤ 15 := by
  have hcard :
      (M.filter fun m : Nat =>
        (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)).card ≤
        (Finset.Icc (mu - 7) (mu + 7)).card := by
    apply Finset.card_le_card_of_injOn (fun m : Nat => (m : Int))
    · intro m hm
      exact (Finset.mem_filter.mp hm).2
    · intro m hm r hr hmr
      exact Int.ofNat_inj.mp hmr
  calc
    (M.filter fun m : Nat =>
      (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)).card ≤
        (Finset.Icc (mu - 7) (mu + 7)).card := hcard
    _ = 15 := by
      rw [Int.card_Icc]
      omega

/-- A fixed input thin index can be central for at most fifteen parameter
windows.  This is the finite-overlap count used after summing the central
cap moments over the radius windows. -/
theorem thinRadial_central_window_card_le_fifteen
    (U : Finset Int) (m : Nat) :
    (U.filter fun mu => (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)).card ≤ 15 := by
  have hsubset :
      U.filter (fun mu => (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)) ⊆
        Finset.Icc ((m : Int) - 7) ((m : Int) + 7) := by
    intro mu hmu
    have hmem : (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7) :=
      (Finset.mem_filter.mp hmu).2
    rw [Finset.mem_Icc] at hmem ⊢
    omega
  calc
    (U.filter fun mu => (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)).card ≤
        (Finset.Icc ((m : Int) - 7) ((m : Int) + 7)).card :=
      Finset.card_le_card hsubset
    _ = 15 := by
      rw [Int.card_Icc]
      omega

/-- Summing a nonnegative input moment over all central parameter windows
costs only the fifteen-fold central overlap. -/
theorem sum_thinRadial_central_window_moments_le
    (U : Finset Int) (M : Finset Nat) (I : Nat → ENNReal) :
    (∑ mu ∈ U, ∑ m ∈ (M.filter fun m : Nat =>
      (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)), I m) ≤
      15 * ∑ m ∈ M, I m := by
  classical
  have hinterior (m : Nat) :
      (∑ mu ∈ U,
        if (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7) then I m else 0) ≤
        15 * I m := by
    calc
      (∑ mu ∈ U,
          if (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7) then I m else 0) =
          ((U.filter fun mu =>
            (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)).card : ENNReal) * I m := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 15 * I m := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast thinRadial_central_window_card_le_fifteen U m
        · exact bot_le
  calc
    (∑ mu ∈ U, ∑ m ∈ (M.filter fun m : Nat =>
        (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7)), I m) =
        ∑ m ∈ M, ∑ mu ∈ U,
          if (m : Int) ∈ Finset.Icc (mu - 7) (mu + 7) then I m else 0 := by
          simp_rw [Finset.sum_filter]
          exact Finset.sum_comm
    _ ≤ ∑ m ∈ M, 15 * I m := by
      apply Finset.sum_le_sum
      intro m hm
      exact hinterior m
    _ = 15 * ∑ m ∈ M, I m := by
      rw [Finset.mul_sum]

theorem Icc_subset_multiplicativeInterval_of_log_diameter
    {a b : Real} (ha : 0 < a) {diam : NNReal}
    (hdiam : 2 * (b - a) / (a * Real.log 2) <= (diam : Real)) :
    Icc a b ⊆ multiplicativeInterval ⟨a, ha⟩ diam := by
  intro r hr
  refine ⟨lt_of_lt_of_le ha hr.1, ?_⟩
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrpos : 0 < r := lt_of_lt_of_le ha hr.1
  have hlogmono : Real.log a <= Real.log r :=
    Real.strictMonoOn_log.monotoneOn ha hrpos hr.1
  have hsubnonneg : 0 <= Real.log r - Real.log a := sub_nonneg.mpr hlogmono
  rw [show logRadius (⟨a, ha⟩ : PositiveRadius) = Real.log a / Real.log 2 by rfl]
  rw [← sub_div]
  rw [abs_of_nonneg ((div_nonneg hsubnonneg hlogtwo.le))]
  apply (div_le_iff₀ hlogtwo).2
  have hlogratio : Real.log r - Real.log a <= r / a - 1 := by
    rw [← Real.log_div hrpos.ne' ha.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hrpos ha)
  have hratio : r / a - 1 = (r - a) / a := by
    rw [sub_div, div_self ha.ne']
  have hgap : (r - a) / a <= (b - a) / a := by
    apply div_le_div_of_nonneg_right
    · linarith [hr.2]
    · exact ha.le
  have hbound : Real.log r - Real.log a <= (b - a) / a :=
    hlogratio.trans (hratio ▸ hgap)
  have hscale : (b - a) / a <= (diam : Real) / 2 * Real.log 2 := by
    have hden : 0 < a * Real.log 2 := mul_pos ha hlogtwo
    have := (div_le_iff₀ hden).mp hdiam
    apply (div_le_iff₀ ha).2
    nlinarith
  exact hbound.trans hscale

/-- If the radius set meets a short additive window inside [1,2], the
left endpoint of that window is uniformly positive.  This is the condition
which lets the local multiplicative entropy hypothesis apply to the window. -/
theorem thinRadiusWindow_base_lower_of_inter_nonempty
    {E : Set Real} {s : Real} {mu : Int} (hs : s <= 1 / 4)
    (hE : E ⊆ Icc (1 : Real) 2)
    (hne : (E ∩ thinRadiusWindow s mu).Nonempty) :
    1 / 4 <= s * ((mu : Real) - 1) := by
  rcases hne with ⟨r, hrE, hr⟩
  have hrlo : 1 <= r := (hE hrE).1
  change s * ((mu : Real) - 1) <= r ∧
    r <= s * ((mu : Real) + 2) at hr
  have hgap : s * ((mu : Real) + 2) =
      s * ((mu : Real) - 1) + 3 * s := by
    ring
  rw [hgap] at hr
  nlinarith

/-- Every relevant three-width additive radius window is contained in a
multiplicative interval of diameter 48 times its physical width.  The
deliberately generous constant keeps the later entropy cover literal and
avoids tracking inessential endpoint fractions. -/
theorem thinRadiusWindow_subset_multiplicativeInterval
    {s : Real} {mu : Int} (hs : 0 < s)
    (hbase : 1 / 4 <= s * ((mu : Real) - 1)) :
    thinRadiusWindow s mu ⊆
      multiplicativeInterval
        ⟨s * ((mu : Real) - 1),
          lt_of_lt_of_le (by norm_num) hbase⟩
        ⟨48 * s, by positivity⟩ := by
  unfold thinRadiusWindow
  apply Icc_subset_multiplicativeInterval_of_log_diameter
  have hlog : (1 / 2 : Real) <= Real.log 2 := by
    exact (lt_trans (by norm_num) Real.log_two_gt_d9).le
  have hbasepos : 0 < s * ((mu : Real) - 1) :=
    lt_of_lt_of_le (by norm_num) hbase
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : (1 / 8 : Real) <=
      s * ((mu : Real) - 1) * Real.log 2 := by
    calc
      (1 / 8 : Real) = (1 / 4) * (1 / 2) := by norm_num
      _ <= s * ((mu : Real) - 1) * Real.log 2 :=
        mul_le_mul hbase hlog (by norm_num) hbasepos.le
  have hgap : s * ((mu : Real) + 2) - s * ((mu : Real) - 1) = 3 * s := by
    ring
  rw [hgap]
  change 2 * (3 * s) / (s * ((mu : Real) - 1) * Real.log 2) <= 48 * s
  apply (div_le_iff₀ (mul_pos hbasepos hlogpos)).2
  calc
    2 * (3 * s) = 48 * s * (1 / 8) := by ring
    _ <= 48 * s * (s * ((mu : Real) - 1) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)

/-- At the dyadic central scales used in the partition, with s at most 1/16,
a nonempty parameter window has a much better lower endpoint. -/
theorem thinRadiusWindow_base_lower_thirteen_sixteenths_of_inter_nonempty
    {E : Set Real} {s : Real} {mu : Int} (hs : s <= 1 / 16)
    (hE : E ⊆ Icc (1 : Real) 2)
    (hne : (E ∩ thinRadiusWindow s mu).Nonempty) :
    13 / 16 <= s * ((mu : Real) - 1) := by
  rcases hne with ⟨r, hrE, hr⟩
  have hrlo : 1 <= r := (hE hrE).1
  change s * ((mu : Real) - 1) <= r ∧
    r <= s * ((mu : Real) + 2) at hr
  have hgap : s * ((mu : Real) + 2) =
      s * ((mu : Real) - 1) + 3 * s := by
    ring
  rw [hgap] at hr
  nlinarith

/-- The central three-width parameter window has multiplicative diameter at
most 16 times its physical width.  This is the version used with a dyadic
width at most 1/16. -/
theorem thinRadiusWindow_subset_multiplicativeInterval_small_scale
    {s : Real} {mu : Int} (hs : 0 < s)
    (hbase : 13 / 16 <= s * ((mu : Real) - 1)) :
    thinRadiusWindow s mu ⊆
      multiplicativeInterval
        ⟨s * ((mu : Real) - 1),
          lt_of_lt_of_le (by norm_num) hbase⟩
        ⟨16 * s, by positivity⟩ := by
  unfold thinRadiusWindow
  apply Icc_subset_multiplicativeInterval_of_log_diameter
  have hlog : (1 / 2 : Real) <= Real.log 2 := by
    exact (lt_trans (by norm_num) Real.log_two_gt_d9).le
  have hbasepos : 0 < s * ((mu : Real) - 1) :=
    lt_of_lt_of_le (by norm_num) hbase
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : (3 / 8 : Real) <=
      s * ((mu : Real) - 1) * Real.log 2 := by
    calc
      (3 / 8 : Real) <= (13 / 16) * (1 / 2) := by norm_num
      _ <= s * ((mu : Real) - 1) * Real.log 2 :=
        mul_le_mul hbase hlog (by norm_num) hbasepos.le
  have hgap : s * ((mu : Real) + 2) - s * ((mu : Real) - 1) = 3 * s := by
    ring
  rw [hgap]
  change 2 * (3 * s) / (s * ((mu : Real) - 1) * Real.log 2) <= 16 * s
  apply (div_le_iff₀ (mul_pos hbasepos hlogpos)).2
  calc
    2 * (3 * s) = 16 * s * (3 / 8) := by ring
    _ <= 16 * s * (s * ((mu : Real) - 1) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)

/-- A local multiplicative entropy power bound gives the finite cover needed
by the cap estimate for a literal additive radius window.  The inclusion of
the window in the multiplicative interval is kept as an explicit hypothesis,
so callers can use the concrete 48-times-width estimate above. -/
theorem exists_entropy_nat_witness_of_thinRadiusWindow_local_power_bound
    {E : Set Real} {s : Real} {mu : Int} {delta : NNReal}
    {rho sigma : Real} (hdelta : 0 < delta)
    (c : PositiveRadius) (diam : Icc delta 1)
    (hwindow : thinRadiusWindow s mu ⊆ multiplicativeInterval c diam.1)
    (hbound :
      (localMultiplicativeEntropy E c diam.1 delta).toENNReal <=
        ((diam.1 : ENNReal) ^ rho) * ((delta : ENNReal)⁻¹) ^ sigma) :
    ∃ N : Nat, multiplicativeEntropy (E ∩ thinRadiusWindow s mu) delta <= N ∧
      (N : ENNReal) <=
        ((diam.1 : ENNReal) ^ rho) * ((delta : ENNReal)⁻¹) ^ sigma := by
  obtain ⟨N, hN, hNbound⟩ :=
    exists_local_entropy_nat_witness_of_power_bound
      (A := 1) (p := 1) (rho := rho) (s := sigma) hdelta c diam (by
        simpa using hbound)
  refine ⟨N, ?_, ?_⟩
  · calc
      multiplicativeEntropy (E ∩ thinRadiusWindow s mu) delta <=
          multiplicativeEntropy (E ∩ multiplicativeInterval c diam.1) delta :=
        multiplicativeEntropy_mono (by
          intro r hr
          exact ⟨hr.1, hwindow hr.2⟩) delta
      _ = localMultiplicativeEntropy E c diam.1 delta := rfl
      _ <= N := hN
  · simpa using hNbound

/-- The strict implicit hypothesis supplies the exact finite entropy cover
for every nonempty thin radius window that occurs in the central radial
decomposition.  Its diameter is the concrete bound 48 times the physical
slice width. -/
theorem exists_eventually_thinRadiusWindow_entropy_nat_bound_of_strict_implicit
    {d : Nat} (hd : 3 <= d) {E : Set Real} {p alpha : Real}
    (hp : 1 < p) (hE : E ⊆ Icc (1 : Real) 2)
    (hstrict :
      max ((alpha : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : Real) - 1) * (p - 2) - alpha)) <
        ((((d : Real) - 1) * (p - 1) : Real) : EReal)) :
    ∃ epsilon : Real, 0 < epsilon ∧
      epsilon < ((d : Real) - 1) * (p - 1) ∧
      ∀ᶠ delta : NNReal in 𝓝[>] (0 : NNReal),
        ∀ (s : Real) (mu : Int), 0 < s -> s <= 1 / 4 -> 48 * s <= 1 ->
          (delta : Real) <= 48 * s ->
          (E ∩ thinRadiusWindow s mu).Nonempty ->
          ∃ N : Nat, multiplicativeEntropy (E ∩ thinRadiusWindow s mu) delta <= N ∧
            (N : ENNReal) <=
              (ENNReal.ofReal (48 * s)) ^
                (((d : Real) - 1) * (p - 2) - alpha) *
              ((delta : ENNReal)⁻¹) ^
                (((d : Real) - 1) * (p - 1) - epsilon) := by
  obtain ⟨epsilon, hepsilon, hepsilonlt, _hMinkowski, _hLegendre, hlocal⟩ :=
    exists_eventually_local_entropy_nat_bound_of_strict_implicit hd hp hstrict
  refine ⟨epsilon, hepsilon, hepsilonlt, ?_⟩
  filter_upwards [hlocal] with delta hlocaldelta
  intro s mu hs hssmall hDone hdeltaD hne
  have hbase : 1 / 4 <= s * ((mu : Real) - 1) :=
    thinRadiusWindow_base_lower_of_inter_nonempty hssmall hE hne
  let D : NNReal := ⟨48 * s, by positivity⟩
  have hdeltaDnn : delta <= D := by
    exact_mod_cast hdeltaD
  have hDoneNN : D <= 1 := by
    exact_mod_cast hDone
  let diam : Icc delta 1 := ⟨D, hdeltaDnn, hDoneNN⟩
  let c : PositiveRadius :=
    ⟨s * ((mu : Real) - 1), lt_of_lt_of_le (by norm_num) hbase⟩
  have hwindow : thinRadiusWindow s mu ⊆ multiplicativeInterval c D := by
    simpa only [c, D] using
      (thinRadiusWindow_subset_multiplicativeInterval hs hbase)
  obtain ⟨N, hN, hNbound⟩ := hlocaldelta c diam
  refine ⟨N, ?_, ?_⟩
  · calc
      multiplicativeEntropy (E ∩ thinRadiusWindow s mu) delta <=
          multiplicativeEntropy (E ∩ multiplicativeInterval c D) delta :=
        multiplicativeEntropy_mono (by
          intro r hr
          exact ⟨hr.1, hwindow hr.2⟩) delta
      _ = localMultiplicativeEntropy E c D delta := rfl
      _ = localMultiplicativeEntropy E c diam.1 delta := by simp [diam]
      _ <= N := hN
  · have hDcoe : (D : ENNReal) = ENNReal.ofReal (48 * s) := by
      rw [ENNReal.coe_nnreal_eq]
      change ENNReal.ofReal (48 * s) = ENNReal.ofReal (48 * s)
      rfl
    change (N : ENNReal) <=
      (D : ENNReal) ^ (((d : Real) - 1) * (p - 2) - alpha) *
        ((delta : ENNReal)⁻¹) ^
          (((d : Real) - 1) * (p - 1) - epsilon) at hNbound
    simpa only [hDcoe] using hNbound

/-- The central thin partition has a sharper entropy-cover specialization:
when the physical width is at most 1/16, every nonempty window has
multiplicative diameter at most 16 times that width. -/
theorem exists_eventually_small_scale_thinRadiusWindow_entropy_nat_bound_of_strict_implicit
    {d : Nat} (hd : 3 <= d) {E : Set Real} {p alpha : Real}
    (hp : 1 < p) (hE : E ⊆ Icc (1 : Real) 2)
    (hstrict :
      max ((alpha : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : Real) - 1) * (p - 2) - alpha)) <
        ((((d : Real) - 1) * (p - 1) : Real) : EReal)) :
    ∃ epsilon : Real, 0 < epsilon ∧
      epsilon < ((d : Real) - 1) * (p - 1) ∧
      ∀ᶠ delta : NNReal in 𝓝[>] (0 : NNReal),
        ∀ (s : Real) (mu : Int), 0 < s -> s <= 1 / 16 ->
          (delta : Real) <= 16 * s ->
          (E ∩ thinRadiusWindow s mu).Nonempty ->
          ∃ N : Nat, multiplicativeEntropy (E ∩ thinRadiusWindow s mu) delta <= N ∧
            (N : ENNReal) <=
              (ENNReal.ofReal (16 * s)) ^
                (((d : Real) - 1) * (p - 2) - alpha) *
              ((delta : ENNReal)⁻¹) ^
                (((d : Real) - 1) * (p - 1) - epsilon) := by
  obtain ⟨epsilon, hepsilon, hepsilonlt, _hMinkowski, _hLegendre, hlocal⟩ :=
    exists_eventually_local_entropy_nat_bound_of_strict_implicit hd hp hstrict
  refine ⟨epsilon, hepsilon, hepsilonlt, ?_⟩
  filter_upwards [hlocal] with delta hlocaldelta
  intro s mu hs hssmall hdeltaD hne
  have hbase : 13 / 16 <= s * ((mu : Real) - 1) :=
    thinRadiusWindow_base_lower_thirteen_sixteenths_of_inter_nonempty
      hssmall hE hne
  have hDone : 16 * s <= 1 := by nlinarith
  let D : NNReal := ⟨16 * s, by positivity⟩
  have hdeltaDnn : delta <= D := by
    exact_mod_cast hdeltaD
  have hDoneNN : D <= 1 := by
    exact_mod_cast hDone
  let diam : Icc delta 1 := ⟨D, hdeltaDnn, hDoneNN⟩
  let c : PositiveRadius :=
    ⟨s * ((mu : Real) - 1), lt_of_lt_of_le (by norm_num) hbase⟩
  have hwindow : thinRadiusWindow s mu ⊆ multiplicativeInterval c D := by
    simpa only [c, D] using
      (thinRadiusWindow_subset_multiplicativeInterval_small_scale hs hbase)
  obtain ⟨N, hN, hNbound⟩ := hlocaldelta c diam
  refine ⟨N, ?_, ?_⟩
  · calc
      multiplicativeEntropy (E ∩ thinRadiusWindow s mu) delta <=
          multiplicativeEntropy (E ∩ multiplicativeInterval c D) delta :=
        multiplicativeEntropy_mono (by
          intro r hr
          exact ⟨hr.1, hwindow hr.2⟩) delta
      _ = localMultiplicativeEntropy E c D delta := rfl
      _ = localMultiplicativeEntropy E c diam.1 delta := by simp [diam]
      _ <= N := hN
  · have hDcoe : (D : ENNReal) = ENNReal.ofReal (16 * s) := by
      rw [ENNReal.coe_nnreal_eq]
      change ENNReal.ofReal (16 * s) = ENNReal.ofReal (16 * s)
      rfl
    change (N : ENNReal) <=
      (D : ENNReal) ^ (((d : Real) - 1) * (p - 2) - alpha) *
        ((delta : ENNReal)⁻¹) ^
          (((d : Real) - 1) * (p - 1) - epsilon) at hNbound
    simpa only [hDcoe] using hNbound

/-- Sequential form of the small-scale window cover at the relative
frequency scales used by the cap decomposition. -/
theorem exists_tail_small_scale_thinRadiusWindow_entropy_nat_bound_of_strict_implicit
    {d : Nat} (hd : 3 <= d) {E : Set Real} {p alpha : Real}
    (hp : 1 < p) (hE : E ⊆ Icc (1 : Real) 2)
    (hstrict :
      max ((alpha : EReal) + multiplicativeMinkowskiExponent E)
          (multiplicativeLegendreAssouadExponent E
            (((d : Real) - 1) * (p - 2) - alpha)) <
        ((((d : Real) - 1) * (p - 1) : Real) : EReal)) :
    ∃ epsilon : Real, 0 < epsilon ∧
      epsilon < ((d : Real) - 1) * (p - 1) ∧
      ∃ j0 : Nat, ∀ j ≥ j0, ∀ (s : Real) (mu : Int),
        0 < s -> s <= 1 / 16 ->
        (dyadicMultiplicativeScale j : Real) <= 16 * s ->
        (E ∩ thinRadiusWindow s mu).Nonempty ->
        ∃ N : Nat,
          multiplicativeEntropy (E ∩ thinRadiusWindow s mu)
              (dyadicMultiplicativeScale j) <= N ∧
          (N : ENNReal) <=
            (ENNReal.ofReal (16 * s)) ^
              (((d : Real) - 1) * (p - 2) - alpha) *
            ((dyadicMultiplicativeScale j : ENNReal)⁻¹) ^
              (((d : Real) - 1) * (p - 1) - epsilon) := by
  obtain ⟨epsilon, hepsilon, hepsilonlt, hlocal⟩ :=
    exists_eventually_small_scale_thinRadiusWindow_entropy_nat_bound_of_strict_implicit
      hd hp hE hstrict
  have htail : ∀ᶠ j : Nat in atTop,
      ∀ (s : Real) (mu : Int), 0 < s -> s <= 1 / 16 ->
        (dyadicMultiplicativeScale j : Real) <= 16 * s ->
        (E ∩ thinRadiusWindow s mu).Nonempty ->
        ∃ N : Nat,
          multiplicativeEntropy (E ∩ thinRadiusWindow s mu)
              (dyadicMultiplicativeScale j) <= N ∧
          (N : ENNReal) <=
            (ENNReal.ofReal (16 * s)) ^
              (((d : Real) - 1) * (p - 2) - alpha) *
            ((dyadicMultiplicativeScale j : ENNReal)⁻¹) ^
              (((d : Real) - 1) * (p - 1) - epsilon) :=
    tendsto_dyadicMultiplicativeScale_atTop_nhdsWithin_zero.eventually hlocal
  rcases eventually_atTop.1 htail with ⟨j0, hj0⟩
  exact ⟨epsilon, hepsilon, hepsilonlt, j0, hj0⟩

end LeanSpherical.HarmonicAnalysis
