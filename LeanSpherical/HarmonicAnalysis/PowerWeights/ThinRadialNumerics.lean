import LeanSpherical.HarmonicAnalysis.PowerWeights.ThinRadialCapShell

/-!
# Numerical balancing for the thin radial cap shell

The cap interpolation estimate has two coefficients `c₁` and `c₂`. The
choice `τ = c₁ / c₂` balances them exactly. This file records that algebra
in the `ENNReal` form used by the literal cap-shell theorem.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric
open scoped BigOperators ENNReal

noncomputable section

/-- The low-end interpolation coefficient after choosing `τ = x / y`. -/
theorem ennreal_balance_cap_low
    (x y : ENNReal) (hy0 : y ≠ 0) (hy_top : y ≠ ∞)
    (p : Real) (hp : p < 2) :
    y * (x / y) ^ (2 - p) = x ^ (2 - p) * y ^ (p - 1) := by
  have ha : 0 ≤ 2 - p := by linarith
  rw [ENNReal.div_rpow_of_nonneg _ _ ha]
  calc
    y * (x ^ (2 - p) / y ^ (2 - p)) =
        x ^ (2 - p) * (y / y ^ (2 - p)) := by
          simp only [div_eq_mul_inv]
          ac_rfl
    _ = x ^ (2 - p) * y ^ (1 - (2 - p)) := by
      rw [ENNReal.rpow_sub 1 (2 - p) hy0 hy_top]
      simp
    _ = x ^ (2 - p) * y ^ (p - 1) := by ring_nf

/-- The high-end interpolation coefficient after choosing `τ = x / y`. -/
theorem ennreal_balance_cap_high
    (x y : ENNReal) (hx0 : x ≠ 0) (hx_top : x ≠ ∞)
    (p : Real) (hp : 1 < p) :
    x * (x / y) ^ (1 - p) = x ^ (2 - p) * y ^ (p - 1) := by
  have hb : 0 ≤ p - 1 := by linarith
  have hxpow0 : x ^ (p - 1) ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hx0) hx_top)
  have hxpowtop : x ^ (p - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hb hx_top
  calc
    x * (x / y) ^ (1 - p) = x * (x / y) ^ (-(p - 1)) := by
      congr 2
      ring
    _ = x * ((x / y) ^ (p - 1))⁻¹ := by rw [ENNReal.rpow_neg]
    _ = x * (x ^ (p - 1) / y ^ (p - 1))⁻¹ := by
      rw [ENNReal.div_rpow_of_nonneg _ _ hb]
    _ = x * (y ^ (p - 1) / x ^ (p - 1)) := by
      rw [ENNReal.inv_div (Or.inr hxpowtop) (Or.inr hxpow0)]
    _ = y ^ (p - 1) * (x / x ^ (p - 1)) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = y ^ (p - 1) * x ^ (1 - (p - 1)) := by
      rw [ENNReal.rpow_sub 1 (p - 1) hx0 hx_top]
      simp
    _ = x ^ (2 - p) * y ^ (p - 1) := by ring_nf

/-- Finite positive coefficients yield the positive real splitting scale
accepted by the cap interpolation theorem. -/
theorem positive_toReal_div_of_ennreal
    {x y : ENNReal} (hx0 : x ≠ 0) (hx_top : x ≠ ∞)
    (hy0 : y ≠ 0) (hy_top : y ≠ ∞) :
    0 < (x / y).toReal ∧ ENNReal.ofReal (x / y).toReal = x / y := by
  constructor
  · exact ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hx0, hy_top⟩)
      (ENNReal.div_ne_top hx_top hy0)
  · exact ENNReal.ofReal_toReal (ENNReal.div_ne_top hx_top hy0)

/-- A product envelope for the two cap coefficients gives the balanced
interpolation-moment envelope. This is the numerical form consumed after
the literal thin cap-shell estimate. -/
theorem balanced_cap_interpolation_moment_le_of_product
    {p : Real} (hp1 : 1 < p) (hp2 : p < 2)
    {c1 c2 A1 A2 κ1 κ2 I K gain : ENNReal} {tau : Real}
    (hc10 : c1 ≠ 0) (hc1top : c1 ≠ ∞)
    (hc20 : c2 ≠ 0) (hc2top : c2 ≠ ∞)
    (htau : ENNReal.ofReal tau = c1 / c2)
    (hA1 : A1 ≤ κ1 * I) (hA2 : A2 ≤ κ2 * I)
    (hproduct : c1 ^ (2 - p) * c2 ^ (p - 1) ≤ K * gain) :
    ENNReal.ofReal p *
        (4 * c2 * ((ENNReal.ofReal tau) ^ (2 - p) * A2) +
          2 * c1 * ((ENNReal.ofReal tau) ^ (1 - p) * A1)) ≤
      ENNReal.ofReal p * (4 * κ2 + 2 * κ1) * K * gain * I := by
  let P : ENNReal := c1 ^ (2 - p) * c2 ^ (p - 1)
  have hlow : c2 * (ENNReal.ofReal tau) ^ (2 - p) = P := by
    rw [htau]
    exact ennreal_balance_cap_low c1 c2 hc20 hc2top p hp2
  have hhigh : c1 * (ENNReal.ofReal tau) ^ (1 - p) = P := by
    rw [htau]
    exact ennreal_balance_cap_high c1 c2 hc10 hc1top p hp1
  calc
    ENNReal.ofReal p *
        (4 * c2 * ((ENNReal.ofReal tau) ^ (2 - p) * A2) +
          2 * c1 * ((ENNReal.ofReal tau) ^ (1 - p) * A1)) =
        ENNReal.ofReal p * (4 * (c2 * (ENNReal.ofReal tau) ^ (2 - p)) * A2 +
          2 * (c1 * (ENNReal.ofReal tau) ^ (1 - p)) * A1) := by
            ring
    _ = ENNReal.ofReal p * (4 * P * A2 + 2 * P * A1) := by
      rw [hlow, hhigh]
    _ ≤ ENNReal.ofReal p * (4 * P * (κ2 * I) + 2 * P * (κ1 * I)) := by
      gcongr
    _ = ENNReal.ofReal p * (4 * κ2 + 2 * κ1) * P * I := by
      ring
    _ ≤ ENNReal.ofReal p * (4 * κ2 + 2 * κ1) * (K * gain) * I := by
      gcongr
    _ = ENNReal.ofReal p * (4 * κ2 + 2 * κ1) * K * gain * I := by
      ring

/-- The balanced real splitting scale exists and has the cap-moment bound
whenever the product of the two cap coefficients has a prescribed envelope. -/
theorem exists_positive_tau_balanced_cap_interpolation_moment_le_of_product
    {p : Real} (hp1 : 1 < p) (hp2 : p < 2)
    {c1 c2 A1 A2 κ1 κ2 I K gain : ENNReal}
    (hc10 : c1 ≠ 0) (hc1top : c1 ≠ ∞)
    (hc20 : c2 ≠ 0) (hc2top : c2 ≠ ∞)
    (hA1 : A1 ≤ κ1 * I) (hA2 : A2 ≤ κ2 * I)
    (hproduct : c1 ^ (2 - p) * c2 ^ (p - 1) ≤ K * gain) :
    ∃ tau : Real, 0 < tau ∧ ENNReal.ofReal tau = c1 / c2 ∧
      ENNReal.ofReal p *
          (4 * c2 * ((ENNReal.ofReal tau) ^ (2 - p) * A2) +
            2 * c1 * ((ENNReal.ofReal tau) ^ (1 - p) * A1)) ≤
        ENNReal.ofReal p * (4 * κ2 + 2 * κ1) * K * gain * I := by
  let tau : Real := (c1 / c2).toReal
  have htau := positive_toReal_div_of_ennreal hc10 hc1top hc20 hc2top
  refine ⟨tau, htau.1, htau.2, ?_⟩
  exact balanced_cap_interpolation_moment_le_of_product hp1 hp2
    hc10 hc1top hc20 hc2top htau.2 hA1 hA2 hproduct

/-- The cap interpolation bound may be balanced using positive finite
*envelopes* for its two coefficients.  This is the form appropriate for the
literal interval cover: the actual coefficients need not be analyzed for
positivity once they have been bounded by the explicit cap and entropy
envelopes. -/
theorem exists_positive_tau_cap_interpolation_moment_le_of_coefficient_envelopes
    {p : Real} (hp1 : 1 < p) (hp2 : p < 2)
    {c1 c2 d1 d2 A1 A2 κ1 κ2 I K gain : ENNReal}
    (hd10 : d1 ≠ 0) (hd1top : d1 ≠ ∞)
    (hd20 : d2 ≠ 0) (hd2top : d2 ≠ ∞)
    (hc1 : c1 ≤ d1) (hc2 : c2 ≤ d2)
    (hA1 : A1 ≤ κ1 * I) (hA2 : A2 ≤ κ2 * I)
    (hproduct : d1 ^ (2 - p) * d2 ^ (p - 1) ≤ K * gain) :
    ∃ tau : Real, 0 < tau ∧
      ENNReal.ofReal p *
          (4 * c2 * ((ENNReal.ofReal tau) ^ (2 - p) * A2) +
            2 * c1 * ((ENNReal.ofReal tau) ^ (1 - p) * A1)) ≤
        ENNReal.ofReal p * (4 * κ2 + 2 * κ1) * K * gain * I := by
  obtain ⟨tau, htau, htau_eq, hbalanced⟩ :=
    exists_positive_tau_balanced_cap_interpolation_moment_le_of_product
      hp1 hp2 (c1 := d1) (c2 := d2) hd10 hd1top hd20 hd2top
      hA1 hA2 hproduct
  refine ⟨tau, htau, ?_⟩
  calc
    ENNReal.ofReal p *
        (4 * c2 * ((ENNReal.ofReal tau) ^ (2 - p) * A2) +
          2 * c1 * ((ENNReal.ofReal tau) ^ (1 - p) * A1)) ≤
        ENNReal.ofReal p *
          (4 * d2 * ((ENNReal.ofReal tau) ^ (2 - p) * A2) +
            2 * d1 * ((ENNReal.ofReal tau) ^ (1 - p) * A1)) := by
          gcongr
    _ ≤ ENNReal.ofReal p * (4 * κ2 + 2 * κ1) * K * gain * I := hbalanced

private theorem interval_tail_reassembly
    {A q W : ENNReal} {j : Nat} (hj : 4 ≤ j)
    (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (U T : Nat → ENNReal)
    (hUT : ∀ m ∈ Finset.range (j - 3), U m ≤ 2 * T m) :
    (∑ m ∈ Finset.range (j - 3), U m) + A * q ^ (j - 3) * W ≤
      (2 + q⁻¹) * ((∑ m ∈ Finset.range (j - 2), T m) + A * q ^ (j - 2) * W) := by
  have hsub : Finset.range (j - 3) ⊆ Finset.range (j - 2) := by
    intro m hm
    simp only [Finset.mem_range] at hm ⊢
    omega
  have hsumUT :
      (∑ m ∈ Finset.range (j - 3), U m) ≤
        2 * (∑ m ∈ Finset.range (j - 3), T m) := by
    calc
      (∑ m ∈ Finset.range (j - 3), U m) ≤
          ∑ m ∈ Finset.range (j - 3), 2 * T m :=
        Finset.sum_le_sum hUT
      _ = 2 * (∑ m ∈ Finset.range (j - 3), T m) := by
        rw [Finset.mul_sum]
  have hsumT :
      (∑ m ∈ Finset.range (j - 3), T m) ≤
        ∑ m ∈ Finset.range (j - 2), T m :=
    Finset.sum_le_sum_of_subset hsub
  have hprefix :
      (∑ m ∈ Finset.range (j - 3), U m) ≤
        2 * (∑ m ∈ Finset.range (j - 2), T m) :=
    hsumUT.trans (mul_le_mul_right hsumT 2)
  have hpow : q⁻¹ * q ^ (j - 2) = q ^ (j - 3) := by
    have hsub' : j - 2 = (j - 3) + 1 := by omega
    rw [hsub', pow_add, pow_one]
    calc
      q⁻¹ * (q ^ (j - 3) * q) = q ^ (j - 3) * (q⁻¹ * q) := by
        ac_rfl
      _ = q ^ (j - 3) := by
        rw [ENNReal.inv_mul_cancel hq0 hqtop, mul_one]
  have hfar : A * q ^ (j - 3) * W = q⁻¹ * (A * q ^ (j - 2) * W) := by
    rw [← hpow]
    ring
  rw [hfar]
  calc
    (∑ m ∈ Finset.range (j - 3), U m) +
        q⁻¹ * (A * q ^ (j - 2) * W) ≤
      2 * (∑ m ∈ Finset.range (j - 2), T m) +
        q⁻¹ * (A * q ^ (j - 2) * W) := by
          exact add_le_add hprefix le_rfl
    _ ≤ (2 + q⁻¹) * (∑ m ∈ Finset.range (j - 2), T m) +
        (2 + q⁻¹) * (A * q ^ (j - 2) * W) := by
          apply add_le_add
          · exact mul_le_mul_left (le_add_of_nonneg_right bot_le) _
          · exact mul_le_mul_left (le_add_of_nonneg_left bot_le) _
    _ = (2 + q⁻¹) *
        ((∑ m ∈ Finset.range (j - 2), T m) + A * q ^ (j - 2) * W) := by
          rw [mul_add]

/-- A short interval cap tail is bounded by a fixed multiple of the
corresponding moving-radius cap tail at radius two. -/
theorem relativeIntervalBandCapTail_le_fixed_mul_relativeMovingBandCapTail
    (n j : Nat) (C a b s : Real) (hj : 4 ≤ j) (hb : b ≤ 2)
    (hwidth : b - a ≤ ((2 : Real) ^ j)⁻¹) :
    relativeIntervalBandCapTail n j C a b s ≤
      (2 + (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3)))⁻¹) *
        relativeMovingBandCapTail n j C 2 s := by
  let q : ENNReal := ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))
  let A : ENNReal := ENNReal.ofReal (C * (2 : Real) ^ j)
  let V : ENNReal := volume (ball (0 : Euclidean n) s)
  let W : ENNReal := volume (ball (0 : Euclidean (n + 1)) s)
  let U : Nat → ENNReal := fun m =>
    A * q ^ m * V * ENNReal.ofReal
      (6 * (b - a + b * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))
  let T : Nat → ENNReal := fun m =>
    A * q ^ m * V * ENNReal.ofReal
      (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))
  have hq0 : q ≠ 0 := by
    dsimp only [q]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hqtop : q ≠ ∞ := ENNReal.ofReal_ne_top
  have hterm (m : Nat) : U m ≤ 2 * T m := by
    have hD : 0 < (2 : Real) ^ j := by positivity
    have hDinv : 0 ≤ ((2 : Real) ^ j)⁻¹ := inv_nonneg.mpr hD.le
    have hT : 1 ≤ (2 : Real) ^ (m + 1) := by
      exact one_le_pow₀ (by norm_num : (1 : Real) ≤ 2)
    have htwoT : 1 ≤ 2 * (2 : Real) ^ (m + 1) := by nlinarith
    have hbase : ((2 : Real) ^ j)⁻¹ ≤
        2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j := by
      rw [div_eq_mul_inv]
      calc
        ((2 : Real) ^ j)⁻¹ = 1 * ((2 : Real) ^ j)⁻¹ := by ring
        _ ≤ (2 * (2 : Real) ^ (m + 1)) * ((2 : Real) ^ j)⁻¹ :=
          mul_le_mul_of_nonneg_right htwoT hDinv
    have hTnonneg : 0 ≤ (2 : Real) ^ (m + 1) / (2 : Real) ^ j := by positivity
    have hbterm : b * (2 : Real) ^ (m + 1) / (2 : Real) ^ j ≤
        2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j := by
      calc
        b * (2 : Real) ^ (m + 1) / (2 : Real) ^ j =
            b * ((2 : Real) ^ (m + 1) / (2 : Real) ^ j) := by ring
        _ ≤ 2 * ((2 : Real) ^ (m + 1) / (2 : Real) ^ j) :=
          mul_le_mul_of_nonneg_right hb hTnonneg
        _ = 2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j := by ring
    have hreal :
        6 * (b - a + b * (2 : Real) ^ (m + 1) / (2 : Real) ^ j) ≤
          2 * (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j)) := by
      nlinarith
    have hinside : ENNReal.ofReal
        (6 * (b - a + b * (2 : Real) ^ (m + 1) / (2 : Real) ^ j)) ≤
        2 * ENNReal.ofReal
          (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j)) := by
      calc
        ENNReal.ofReal
            (6 * (b - a + b * (2 : Real) ^ (m + 1) / (2 : Real) ^ j)) ≤
          ENNReal.ofReal
            (2 * (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))) :=
              ENNReal.ofReal_le_ofReal hreal
        _ = 2 * ENNReal.ofReal
            (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j)) := by
              rw [ENNReal.ofReal_mul (by norm_num)]
              norm_num
    dsimp only [U, T]
    calc
      A * q ^ m * V * ENNReal.ofReal
          (6 * (b - a + b * (2 : Real) ^ (m + 1) / (2 : Real) ^ j)) ≤
        A * q ^ m * V *
          (2 * ENNReal.ofReal
            (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))) := by
              gcongr
      _ = 2 * (A * q ^ m * V * ENNReal.ofReal
          (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))) := by ring
  have hcore := interval_tail_reassembly
    (A := A) (q := q) (W := W) hj hq0 hqtop U T
    (fun m _ => hterm m)
  simpa only [relativeIntervalBandCapTail, relativeMovingBandCapTail,
    q, A, V, W, U, T] using hcore

/-- Summing short interval cap tails costs only the cover cardinality. -/
theorem sum_relativeIntervalBandCapTail_le_fixed_mul_card_mul_relativeMovingBandCapTail
    (n j : Nat) (C s : Real) (R : Finset (Real × Real))
    (hj : 4 ≤ j)
    (hends : ∀ q ∈ R, q.2 ≤ 2)
    (hwidth : ∀ q ∈ R, q.2 - q.1 ≤ ((2 : Real) ^ j)⁻¹) :
    (∑ q ∈ R, relativeIntervalBandCapTail n j C q.1 q.2 s) ≤
      (2 + (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3)))⁻¹) *
        (R.card : ENNReal) * relativeMovingBandCapTail n j C 2 s := by
  let K : ENNReal :=
    2 + (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3)))⁻¹
  calc
    (∑ q ∈ R, relativeIntervalBandCapTail n j C q.1 q.2 s) ≤
        ∑ q ∈ R, K * relativeMovingBandCapTail n j C 2 s := by
          apply Finset.sum_le_sum
          intro q hq
          exact relativeIntervalBandCapTail_le_fixed_mul_relativeMovingBandCapTail
            n j C q.1 q.2 s hj (hends q hq) (hwidth q hq)
    _ = K * (R.card : ENNReal) * relativeMovingBandCapTail n j C 2 s := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

private theorem relativeMovingBandCapTail_near_term_eq
    {n j : Nat} {C s : Real} (hC : 0 < C) (m : Nat) :
    ENNReal.ofReal (C * (2 : Real) ^ j) *
        (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))) ^ m *
          ((ENNReal.ofReal s) ^ n * volume (ball (0 : Euclidean n) 1)) *
            ENNReal.ofReal (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j)) =
      (ENNReal.ofReal (24 * C) * volume (ball (0 : Euclidean n) 1) *
        (ENNReal.ofReal s) ^ n) *
        (2 * ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))) ^ m := by
  have hA : 0 ≤ C * (2 : Real) ^ j := by positivity
  have hcalc :
      (C * (2 : Real) ^ j) *
        (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j)) =
        24 * C * (2 : Real) ^ m := by
    field_simp
    ring
  calc
    _ = (ENNReal.ofReal (C * (2 : Real) ^ j) *
          ENNReal.ofReal (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))) *
        (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))) ^ m *
          ((ENNReal.ofReal s) ^ n * volume (ball (0 : Euclidean n) 1)) := by ring
    _ = ENNReal.ofReal ((C * (2 : Real) ^ j) *
          (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))) *
        (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))) ^ m *
          ((ENNReal.ofReal s) ^ n * volume (ball (0 : Euclidean n) 1)) := by
          rw [ENNReal.ofReal_mul hA]
    _ = ENNReal.ofReal (24 * C * (2 : Real) ^ m) *
        (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))) ^ m *
          ((ENNReal.ofReal s) ^ n * volume (ball (0 : Euclidean n) 1)) := by rw [hcalc]
    _ = (ENNReal.ofReal (24 * C) * (2 : ENNReal) ^ m) *
        (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))) ^ m *
          ((ENNReal.ofReal s) ^ n * volume (ball (0 : Euclidean n) 1)) := by
          rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 24 * C),
            ENNReal.ofReal_pow (by norm_num : (0 : Real) ≤ 2)]
          norm_num
    _ = _ := by
      rw [mul_pow]
      ring

private theorem relativeMovingBandCapTail_far_term_eq
    {n j : Nat} {C : Real} (hC : 0 < C) (hj : 2 ≤ j) :
    ENNReal.ofReal (C * (2 : Real) ^ j) *
        (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))) ^ (j - 2) =
      ENNReal.ofReal (4 * C) *
        (2 * ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))) ^ (j - 2) := by
  have hj' : j = (j - 2) + 2 := by omega
  rw [hj', pow_add]
  simp only [Nat.add_sub_cancel]
  have hreal : C * ((2 : Real) ^ (j - 2) * (2 : Real) ^ 2) =
      (4 * C) * (2 : Real) ^ (j - 2) := by
    norm_num
    ring
  rw [hreal, ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * C)]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : Real) ≤ 2)]
  rw [mul_pow]
  norm_num
  ring

private theorem relativeMovingBandCapTail_ratio_le_one (n : Nat) :
    2 * ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3)) ≤ (1 : ENNReal) := by
  have hpow : ((2 : Real)⁻¹) ^ (n + 1 + 3) ≤ ((2 : Real)⁻¹) ^ 2 := by
    apply pow_le_pow_of_le_one
    · positivity
    · norm_num
    · omega
  calc
    2 * ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3)) =
        ENNReal.ofReal (2 * (((2 : Real)⁻¹) ^ (n + 1 + 3))) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
          norm_num
    _ ≤ ENNReal.ofReal (2 * ((2 : Real)⁻¹) ^ 2) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow (by norm_num))
    _ ≤ 1 := by norm_num

/-- A uniform transverse-volume envelope for the moving cap tail. -/
def relativeMovingBandCapTailEnvelope (n : Nat) (C : Real) : ENNReal :=
  (ENNReal.ofReal (24 * C) * volume (ball (0 : Euclidean n) 1) *
      (1 - 2 * ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3)))⁻¹ +
    ENNReal.ofReal (4 * C) * volume (ball (0 : Euclidean (n + 1)) 1))

/-- The moving cap tail is uniformly controlled by its transverse
`s ^ n` volume factor. -/
theorem relativeMovingBandCapTail_le_envelope
    {n j : Nat} {C s : Real} (hC : 0 < C) (hj : 2 ≤ j)
    (hs : 0 < s) (hsone : s ≤ 1) :
    relativeMovingBandCapTail n j C 2 s ≤
      relativeMovingBandCapTailEnvelope n C * (ENNReal.ofReal s) ^ n := by
  let q : ENNReal := ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))
  let r : ENNReal := 2 * q
  let Vn : ENNReal := volume (ball (0 : Euclidean n) 1)
  let Vd : ENNReal := volume (ball (0 : Euclidean (n + 1)) 1)
  have hr : r ≤ 1 := by
    simpa only [r, q] using relativeMovingBandCapTail_ratio_le_one n
  have hsenn : ENNReal.ofReal s ≤ 1 := ENNReal.ofReal_le_one.mpr hsone
  have hsum :
      (∑ m ∈ Finset.range (j - 2),
        ENNReal.ofReal (C * (2 : Real) ^ j) * q ^ m *
          ((ENNReal.ofReal s) ^ n * Vn) *
            ENNReal.ofReal (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))) =
        (ENNReal.ofReal (24 * C) * Vn * (ENNReal.ofReal s) ^ n) *
          ∑ m ∈ Finset.range (j - 2), r ^ m := by
    calc
      (∑ m ∈ Finset.range (j - 2),
        ENNReal.ofReal (C * (2 : Real) ^ j) * q ^ m *
          ((ENNReal.ofReal s) ^ n * Vn) *
            ENNReal.ofReal (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))) =
          ∑ m ∈ Finset.range (j - 2),
            (ENNReal.ofReal (24 * C) * Vn * (ENNReal.ofReal s) ^ n) * r ^ m := by
          apply Finset.sum_congr rfl
          intro m hm
          simpa only [q, r, Vn] using
            relativeMovingBandCapTail_near_term_eq (n := n) (j := j) hC m
      _ = (ENNReal.ofReal (24 * C) * Vn * (ENNReal.ofReal s) ^ n) *
          ∑ m ∈ Finset.range (j - 2), r ^ m := by
            rw [Finset.mul_sum]
  have hgeometric : (∑ m ∈ Finset.range (j - 2), r ^ m) ≤ (1 - r)⁻¹ := by
    calc
      (∑ m ∈ Finset.range (j - 2), r ^ m) ≤ ∑' m : Nat, r ^ m :=
        ENNReal.sum_le_tsum (Finset.range (j - 2))
      _ = (1 - r)⁻¹ := ENNReal.tsum_geometric r
  have hfirst :
      (∑ m ∈ Finset.range (j - 2),
        ENNReal.ofReal (C * (2 : Real) ^ j) * q ^ m *
          ((ENNReal.ofReal s) ^ n * Vn) *
            ENNReal.ofReal (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))) ≤
        (ENNReal.ofReal (24 * C) * Vn * (1 - r)⁻¹) * (ENNReal.ofReal s) ^ n := by
    rw [hsum]
    calc
      (ENNReal.ofReal (24 * C) * Vn * (ENNReal.ofReal s) ^ n) *
          ∑ m ∈ Finset.range (j - 2), r ^ m ≤
          (ENNReal.ofReal (24 * C) * Vn * (ENNReal.ofReal s) ^ n) * (1 - r)⁻¹ := by
            simpa only [mul_comm] using
              (mul_le_mul_right hgeometric
                (ENNReal.ofReal (24 * C) * Vn * (ENNReal.ofReal s) ^ n))
      _ = (ENNReal.ofReal (24 * C) * Vn * (1 - r)⁻¹) *
          (ENNReal.ofReal s) ^ n := by ring
  have hfarcoeff :
      ENNReal.ofReal (C * (2 : Real) ^ j) * q ^ (j - 2) ≤ ENNReal.ofReal (4 * C) := by
    dsimp only [q, r]
    calc
      ENNReal.ofReal (C * (2 : Real) ^ j) *
          ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3)) ^ (j - 2) =
          ENNReal.ofReal (4 * C) *
            (2 * ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3))) ^ (j - 2) :=
        relativeMovingBandCapTail_far_term_eq (n := n) (j := j) hC hj
      _ ≤ ENNReal.ofReal (4 * C) * 1 := by
        simpa only [mul_comm] using
          (mul_le_mul_right (pow_le_one₀ bot_le hr) (ENNReal.ofReal (4 * C)))
      _ = ENNReal.ofReal (4 * C) := by rw [mul_one]
  have hspow : (ENNReal.ofReal s) ^ (n + 1) ≤ (ENNReal.ofReal s) ^ n :=
    pow_le_pow_of_le_one bot_le hsenn (Nat.le_succ n)
  have hfar :
      ENNReal.ofReal (C * (2 : Real) ^ j) * q ^ (j - 2) *
          ((ENNReal.ofReal s) ^ (n + 1) * Vd) ≤
        (ENNReal.ofReal (4 * C) * Vd) * (ENNReal.ofReal s) ^ n := by
    calc
      ENNReal.ofReal (C * (2 : Real) ^ j) * q ^ (j - 2) *
          ((ENNReal.ofReal s) ^ (n + 1) * Vd) ≤
          ENNReal.ofReal (4 * C) * ((ENNReal.ofReal s) ^ n * Vd) := by
            gcongr
      _ = (ENNReal.ofReal (4 * C) * Vd) * (ENNReal.ofReal s) ^ n := by ring
  rw [relativeMovingBandCapTail_eq_scaled n j C 2 hs]
  change
    (∑ m ∈ Finset.range (j - 2),
      ENNReal.ofReal (C * (2 : Real) ^ j) * q ^ m *
        ((ENNReal.ofReal s) ^ n * Vn) *
          ENNReal.ofReal (6 * (2 * (2 : Real) ^ (m + 1) / (2 : Real) ^ j))) +
      ENNReal.ofReal (C * (2 : Real) ^ j) * q ^ (j - 2) *
        ((ENNReal.ofReal s) ^ (n + 1) * Vd) ≤ _
  dsimp only [relativeMovingBandCapTailEnvelope]
  change _ ≤
    ((ENNReal.ofReal (24 * C) * Vn * (1 - r)⁻¹ +
      ENNReal.ofReal (4 * C) * Vd) * (ENNReal.ofReal s) ^ n)
  calc
    _ ≤ (ENNReal.ofReal (24 * C) * Vn * (1 - r)⁻¹) * (ENNReal.ofReal s) ^ n +
        (ENNReal.ofReal (4 * C) * Vd) * (ENNReal.ofReal s) ^ n :=
      add_le_add hfirst hfar
    _ = _ := by rw [add_mul]

/-- The interval-cover cap coefficient in the thin shell estimate is bounded
by the entropy cardinality times the uniform moving-tail envelope. -/
theorem relativeIntervalBandCapCoefficient_le_envelope
    (n j : Nat) (C s b α : Real) (R : Finset (Real × Real)) (N : Nat)
    (hC : 0 < C) (hj : 4 ≤ j) (hs : 0 < s) (hsone : s ≤ 1)
    (hcard : R.card ≤ N)
    (hends : ∀ q ∈ R, q.2 ≤ 2)
    (hwidth : ∀ q ∈ R, q.2 - q.1 ≤ ((2 : Real) ^ j)⁻¹) :
    (ENNReal.ofReal (s / 4)) ^ α *
        (∑ q ∈ R, relativeIntervalBandCapTail n j C q.1 q.2 s) *
          ((ENNReal.ofReal b) ^ α)⁻¹ ≤
      (ENNReal.ofReal (s / 4)) ^ α *
        ((2 + (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3)))⁻¹) *
          (N : ENNReal) * relativeMovingBandCapTailEnvelope n C *
            (ENNReal.ofReal s) ^ n) *
          ((ENNReal.ofReal b) ^ α)⁻¹ := by
  let K : ENNReal :=
    2 + (ENNReal.ofReal (((2 : Real)⁻¹) ^ (n + 1 + 3)))⁻¹
  have htail : relativeMovingBandCapTail n j C 2 s ≤
      relativeMovingBandCapTailEnvelope n C * (ENNReal.ofReal s) ^ n :=
    relativeMovingBandCapTail_le_envelope hC (by omega) hs hsone
  have hcard' : (R.card : ENNReal) ≤ N := by exact_mod_cast hcard
  have hsum :
      (∑ q ∈ R, relativeIntervalBandCapTail n j C q.1 q.2 s) ≤
        K * (N : ENNReal) * relativeMovingBandCapTailEnvelope n C *
          (ENNReal.ofReal s) ^ n := by
    calc
      (∑ q ∈ R, relativeIntervalBandCapTail n j C q.1 q.2 s) ≤
          K * (R.card : ENNReal) * relativeMovingBandCapTail n j C 2 s := by
            simpa only [K] using
              sum_relativeIntervalBandCapTail_le_fixed_mul_card_mul_relativeMovingBandCapTail
                n j C s R hj hends hwidth
      _ ≤ K * (N : ENNReal) * relativeMovingBandCapTail n j C 2 s := by
            gcongr
      _ ≤ K * (N : ENNReal) *
          (relativeMovingBandCapTailEnvelope n C * (ENNReal.ofReal s) ^ n) := by
            gcongr
      _ = K * (N : ENNReal) * relativeMovingBandCapTailEnvelope n C *
          (ENNReal.ofReal s) ^ n := by ring
  dsimp only [K] at hsum
  gcongr

/-- The square-function coefficient in the thin radial cap estimate has the
expected dyadic decay at a short parameter scale. -/
theorem thinRadialCapEntropySquare_le_dyadicDecay
    {n : Nat} (j : Nat) (C0 C1 D δ : Real)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hshort : 8 * Real.log 2 * δ ≤ (dyadicScale j)⁻¹) :
    2 * ((4 * C0) / (dyadicScale j) ^ ((n : Real) / 2)) ^ 2 +
      2 * (8 * Real.log 2 * δ) ^ 2 *
        (2 * ((4 * C1) / (dyadicScale j) ^ ((n : Real) / 2 - 1) +
          D / (dyadicScale j) ^ ((n : Real) / 2))) ^ 2 ≤
      (2 * (4 * C0) ^ 2 + 2 * (2 * (4 * C1 + D)) ^ 2) *
        (dyadicScale j) ^ (-(n : Real)) := by
  let x : Real := dyadicScale j
  have hx : 0 < x := dyadicScale_pos j
  have hxone : 1 ≤ x := by
    dsimp only [x, dyadicScale]
    exact one_le_pow₀ (by norm_num)
  have hxinv : x ^ (-1 : Real) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hxone (by norm_num)
  have hshort' : 8 * Real.log 2 * δ ≤ x ^ (-1 : Real) := by
    rw [Real.rpow_neg hx.le, Real.rpow_one]
    exact hshort
  have hbasenonneg : 0 ≤ x ^ (-((n : Real) / 2)) :=
    Real.rpow_nonneg hx.le _
  have hshift : x ^ (-1 : Real) * x ^ (-((n : Real) / 2 - 1)) =
      x ^ (-((n : Real) / 2)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hfirsteq : (4 * C0) / x ^ ((n : Real) / 2) =
      (4 * C0) * x ^ (-((n : Real) / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
  have hBeq : (4 * C1) / x ^ ((n : Real) / 2 - 1) =
      (4 * C1) * x ^ (-((n : Real) / 2 - 1)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
  have hUeq : D / x ^ ((n : Real) / 2) =
      D * x ^ (-((n : Real) / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
  have hsecondnonneg : 0 ≤
      2 * ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
          D / x ^ ((n : Real) / 2)) := by positivity
  have hinside :
      (8 * Real.log 2 * δ) *
          (2 * ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
            D / x ^ ((n : Real) / 2))) ≤
        2 * (4 * C1 + D) * x ^ (-((n : Real) / 2)) := by
    calc
      (8 * Real.log 2 * δ) *
          (2 * ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
            D / x ^ ((n : Real) / 2))) ≤
          x ^ (-1 : Real) *
            (2 * ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
              D / x ^ ((n : Real) / 2))) :=
        mul_le_mul_of_nonneg_right hshort' hsecondnonneg
      _ = 2 * (x ^ (-1 : Real) *
          ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
            D / x ^ ((n : Real) / 2))) := by ring
      _ ≤ 2 * ((4 * C1 + D) * x ^ (-((n : Real) / 2))) := by
        apply mul_le_mul_of_nonneg_left
        · calc
            x ^ (-1 : Real) *
                ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
                  D / x ^ ((n : Real) / 2)) =
                (4 * C1) * (x ^ (-1 : Real) *
                  x ^ (-((n : Real) / 2 - 1))) +
                  D * (x ^ (-1 : Real) * x ^ (-((n : Real) / 2))) := by
                    rw [hBeq, hUeq]
                    ring
            _ ≤ (4 * C1) * x ^ (-((n : Real) / 2)) +
                  D * x ^ (-((n : Real) / 2)) := by
                    apply add_le_add
                    · rw [hshift]
                    · exact mul_le_mul_of_nonneg_left
                        (calc
                          x ^ (-1 : Real) * x ^ (-((n : Real) / 2)) =
                              x ^ (-((n : Real) / 2)) * x ^ (-1 : Real) := by ring
                          _ ≤ x ^ (-((n : Real) / 2)) * 1 :=
                            mul_le_mul_of_nonneg_left hxinv
                              (Real.rpow_nonneg hx.le _)
                          _ = x ^ (-((n : Real) / 2)) := by ring) hD
            _ = (4 * C1 + D) * x ^ (-((n : Real) / 2)) := by ring
        · positivity
      _ = 2 * (4 * C1 + D) * x ^ (-((n : Real) / 2)) := by ring
  have hinside_nonneg : 0 ≤
      (8 * Real.log 2 * δ) *
        (2 * ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
          D / x ^ ((n : Real) / 2))) := by positivity
  have htarget_nonneg : 0 ≤ 2 * (4 * C1 + D) * x ^ (-((n : Real) / 2)) := by
    positivity
  have hsq :
      ((8 * Real.log 2 * δ) *
          (2 * ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
            D / x ^ ((n : Real) / 2)))) ^ 2 ≤
        (2 * (4 * C1 + D) * x ^ (-((n : Real) / 2))) ^ 2 :=
    (sq_le_sq₀ hinside_nonneg htarget_nonneg).mpr hinside
  have hpow : (x ^ (-((n : Real) / 2))) ^ 2 = x ^ (-(n : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  let a : Real := 8 * Real.log 2 * δ
  let b : Real := 2 * ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
    D / x ^ ((n : Real) / 2))
  have hsq' : (a * b) ^ 2 ≤
      (2 * (4 * C1 + D) * x ^ (-((n : Real) / 2))) ^ 2 := by
    simpa only [a, b] using hsq
  have hsec' : 2 * a ^ 2 * b ^ 2 ≤
      2 * (2 * (4 * C1 + D)) ^ 2 * x ^ (-(n : Real)) := by
    calc
      _ = 2 * (a * b) ^ 2 := by ring
      _ ≤ 2 * (2 * (4 * C1 + D) * x ^ (-((n : Real) / 2))) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq' (by norm_num)
      _ = 2 * (2 * (4 * C1 + D)) ^ 2 * x ^ (-(n : Real)) := by
        rw [mul_pow, hpow]
        ring
  have hsec :
      2 * (8 * Real.log 2 * δ) ^ 2 *
        (2 * ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
          D / x ^ ((n : Real) / 2))) ^ 2 ≤
      2 * (2 * (4 * C1 + D)) ^ 2 * x ^ (-(n : Real)) := by
    simpa only [a, b] using hsec'
  have hfst :
      2 * ((4 * C0) / x ^ ((n : Real) / 2)) ^ 2 ≤
        2 * (4 * C0) ^ 2 * x ^ (-(n : Real)) := by
    rw [hfirsteq, mul_pow, hpow]
    ring_nf
    exact le_refl (C0 ^ 2 * x ^ (-(n : Real)) * 32)
  have hmain :
    2 * ((4 * C0) / x ^ ((n : Real) / 2)) ^ 2 +
      2 * (8 * Real.log 2 * δ) ^ 2 *
        (2 * ((4 * C1) / x ^ ((n : Real) / 2 - 1) +
          D / x ^ ((n : Real) / 2))) ^ 2 ≤
      (2 * (4 * C0) ^ 2 + 2 * (2 * (4 * C1 + D)) ^ 2) *
        x ^ (-(n : Real)) := by
    calc
      _ ≤ 2 * (4 * C0) ^ 2 * x ^ (-(n : Real)) +
          2 * (2 * (4 * C1 + D)) ^ 2 * x ^ (-(n : Real)) :=
        add_le_add hfst hsec
      _ = (2 * (4 * C0) ^ 2 + 2 * (2 * (4 * C1 + D)) ^ 2) *
          x ^ (-(n : Real)) := by ring
  simpa only [x] using hmain

/-- The real and `ENNReal` conventions for the dyadic scale agree after the
power that occurs in the entropy coefficient. -/
theorem dyadicMultiplicativeScale_pow_eq_ofReal_dyadicScale_neg
    (n j : Nat) :
    (dyadicMultiplicativeScale j : ENNReal) ^ n =
      ENNReal.ofReal ((dyadicScale j) ^ (-(n : Real))) := by
  calc
    (dyadicMultiplicativeScale j : ENNReal) ^ n =
        (((2 : ENNReal)⁻¹) ^ j) ^ n := by
          change (↑(((2 : NNReal)⁻¹) ^ j) : ENNReal) ^ n = _
          rw [ENNReal.coe_pow, ENNReal.coe_inv (by norm_num)]
          norm_num
    _ = ((2 : ENNReal) ^ (j * n))⁻¹ := by
      rw [← pow_mul]
      exact ENNReal.inv_pow.symm
    _ = ((2 : ENNReal) ^ j) ^ (-(n : Real)) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ← pow_mul]
    _ = (ENNReal.ofReal ((2 : Real) ^ j)) ^ (-(n : Real)) := by
      rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : Real))]
      norm_num
    _ = ENNReal.ofReal (((2 : Real) ^ j) ^ (-(n : Real))) := by
      rw [ENNReal.ofReal_rpow_of_pos (by positivity : 0 < (2 : Real) ^ j)]
    _ = _ := by rfl

/-- `ENNReal` form of the short-scale square-coefficient estimate. -/
theorem ofReal_thinRadialCapEntropySquare_le_dyadicDecay
    {n : Nat} (j : Nat) (C0 C1 D δ : Real)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hshort : 8 * Real.log 2 * δ ≤ (dyadicScale j)⁻¹) :
    ENNReal.ofReal
      (2 * ((4 * C0) / (dyadicScale j) ^ ((n : Real) / 2)) ^ 2 +
        2 * (8 * Real.log 2 * δ) ^ 2 *
          (2 * ((4 * C1) / (dyadicScale j) ^ ((n : Real) / 2 - 1) +
            D / (dyadicScale j) ^ ((n : Real) / 2))) ^ 2) ≤
      ENNReal.ofReal (2 * (4 * C0) ^ 2 + 2 * (2 * (4 * C1 + D)) ^ 2) *
        (dyadicMultiplicativeScale j : ENNReal) ^ n := by
  let K : Real := 2 * (4 * C0) ^ 2 + 2 * (2 * (4 * C1 + D)) ^ 2
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hraw := thinRadialCapEntropySquare_le_dyadicDecay
    (n := n) j C0 C1 D δ hC0 hC1 hD hδ hshort
  calc
    ENNReal.ofReal
        (2 * ((4 * C0) / (dyadicScale j) ^ ((n : Real) / 2)) ^ 2 +
          2 * (8 * Real.log 2 * δ) ^ 2 *
            (2 * ((4 * C1) / (dyadicScale j) ^ ((n : Real) / 2 - 1) +
              D / (dyadicScale j) ^ ((n : Real) / 2))) ^ 2) ≤
        ENNReal.ofReal (K * (dyadicScale j) ^ (-(n : Real))) := by
          exact ENNReal.ofReal_le_ofReal (by simpa only [K] using hraw)
    _ = ENNReal.ofReal K * ENNReal.ofReal ((dyadicScale j) ^ (-(n : Real))) := by
          rw [ENNReal.ofReal_mul hK]
    _ = ENNReal.ofReal K * (dyadicMultiplicativeScale j : ENNReal) ^ n := by
          rw [← dyadicMultiplicativeScale_pow_eq_ofReal_dyadicScale_neg]

end

end LeanSpherical.HarmonicAnalysis
