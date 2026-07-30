/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.MinkowskiQ3PhysicalInterpolation
import LeanSpherical.HarmonicAnalysis.FractalDilations.MinkowskiFacts
import LeanSpherical.HarmonicAnalysis.FractalDilations.TheoremOneFourierInputs

/-!
# The strict physical `Q₃` dyadic rate

This file completes the scale calculation in Lemma 2.3 of
Anderson--Hughes--Roos--Seeger.  The physical shell estimate is of size
`R`, while a Minkowski cover of exponent `a` gives the square estimate of
size `R^(a - n)`.  Crossed interpolation from `L^(q/(q-1))` to `L^q` has
therefore the exact factor
```
R^(1 - (n + 2 - a) / q).
```
For a strict `Q₃` exponent this is a geometric dyadic gain.  The proof below
uses the literal physical endpoint, not the Fourier-volume endpoint.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory Set ENNReal

noncomputable section

/-- The frequency exponent obtained from the physical `L¹ → L∞` endpoint
and the Minkowski square endpoint in ambient dimension `n + 1`. -/
def q3PhysicalMinkowskiExponent (n : Nat) (a q : Real) : Real :=
  1 - ((n : Real) + 2 - a) / q

/-- The associated dyadic ratio. -/
def q3PhysicalMinkowskiRatio (n : Nat) (a q : Real) : Real :=
  (2 : Real) ^ q3PhysicalMinkowskiExponent n a q

/-- Strictness at `Q₃` is exactly negativity of the physical crossed
frequency exponent. -/
theorem q3PhysicalMinkowskiExponent_neg
    {n : Nat} {a q : Real} (hq : 0 < q)
    (hstrict : q < (n : Real) + 2 - a) :
    q3PhysicalMinkowskiExponent n a q < 0 := by
  unfold q3PhysicalMinkowskiExponent
  rw [sub_lt_zero]
  apply (lt_div_iff₀ hq).mpr
  linarith

/-- The strict physical `Q₃` frequency rate is positive and strictly below
one. -/
theorem q3PhysicalMinkowskiRatio_mem_Ioo
    {n : Nat} {a q : Real} (hq : 0 < q)
    (hstrict : q < (n : Real) + 2 - a) :
    q3PhysicalMinkowskiRatio n a q ∈ Ioo 0 1 := by
  constructor
  · unfold q3PhysicalMinkowskiRatio
    exact Real.rpow_pos_of_pos (by norm_num) _
  · unfold q3PhysicalMinkowskiRatio
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (q3PhysicalMinkowskiExponent_neg hq hstrict)

/-- A real normal form for the crossed interpolation constant. -/
def q3PhysicalCrossedRealConstant (A B q : Real) : Real :=
  q * (8 * B * ((q - 2)⁻¹ * (2 * A) ^ (q - 2)))

theorem q3PhysicalCrossedRealConstant_nonneg
    {A B q : Real} (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 2 ≤ q) :
    0 ≤ q3PhysicalCrossedRealConstant A B q := by
  have hq0 : 0 ≤ q := by linarith
  unfold q3PhysicalCrossedRealConstant
  exact mul_nonneg hq0
    (mul_nonneg (mul_nonneg (by norm_num) hB)
      (mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hq))
        (Real.rpow_nonneg (mul_nonneg (by norm_num) hA) _)))

/-- The `ENNReal` crossed constant is the image of its elementary real
normal form whenever the two endpoint constants have their natural signs. -/
theorem q3PhysicalCrossedConstant_eq_ofReal
    {A B q : Real} (hA : 0 < A) (hB : 0 ≤ B) (hq : 2 < q) :
    q3PhysicalCrossedConstant A B q =
      ENNReal.ofReal (q3PhysicalCrossedRealConstant A B q) := by
  have hq0 : 0 ≤ q := by linarith
  have hqminus : 0 < q - 2 := by linarith
  have hinv : 0 ≤ (q - 2)⁻¹ := inv_nonneg.mpr hqminus.le
  unfold q3PhysicalCrossedConstant q3PhysicalCrossedRealConstant
  rw [ENNReal.ofReal_mul hq0]
  congr 1
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hB)]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 8)]
  rw [ENNReal.ofReal_mul hinv, ENNReal.ofReal_inv_of_pos hqminus,
    ENNReal.ofReal_rpow_of_pos (mul_pos (by norm_num) hA)]
  norm_num
  ring

/-- Before taking the output `q`-th root, the crossed physical constant has
the expected scale power `a - n + q - 2`. -/
theorem q3PhysicalCrossedRealConstant_scale
    {n : Nat} {A B R a q : Real} (hA : 0 < A) (hR : 0 < R) :
    q3PhysicalCrossedRealConstant (A * R)
        (B * R ^ (a - (n : Real))) q =
      q3PhysicalCrossedRealConstant A B q *
        R ^ ((a - (n : Real)) + (q - 2)) := by
  have hpower :
      R ^ (a - (n : Real)) * R ^ (q - 2) =
        R ^ ((a - (n : Real)) + (q - 2)) := by
    rw [← Real.rpow_add hR]
  unfold q3PhysicalCrossedRealConstant
  rw [show 2 * (A * R) = (2 * A) * R by ring]
  rw [Real.mul_rpow (mul_nonneg (by norm_num) hA.le) hR.le]
  calc
    q * (8 * (B * R ^ (a - (n : Real))) *
        ((q - 2)⁻¹ * ((2 * A) ^ (q - 2) * R ^ (q - 2)))) =
        (q * (8 * B * ((q - 2)⁻¹ * (2 * A) ^ (q - 2)))) *
          (R ^ (a - (n : Real)) * R ^ (q - 2)) := by ring
    _ = _ := by rw [hpower]

/-- The same scale factorization in `ENNReal` before taking the output
root. -/
theorem q3PhysicalCrossedConstant_scale
    {n : Nat} {A B R a q : Real}
    (hA : 0 < A) (hB : 0 ≤ B) (hR : 0 < R) (hq : 2 < q) :
    q3PhysicalCrossedConstant (A * R)
        (B * R ^ (a - (n : Real))) q =
      q3PhysicalCrossedConstant A B q *
        (ENNReal.ofReal R) ^ ((a - (n : Real)) + (q - 2)) := by
  have hAR : 0 < A * R := mul_pos hA hR
  have hBR : 0 ≤ B * R ^ (a - (n : Real)) :=
    mul_nonneg hB (Real.rpow_nonneg hR.le _)
  have hreal := q3PhysicalCrossedRealConstant_scale
    (n := n) (A := A) (B := B) (R := R) (a := a) (q := q) hA hR
  have hpre : 0 ≤ q3PhysicalCrossedRealConstant A B q :=
    q3PhysicalCrossedRealConstant_nonneg hA.le hB hq.le
  have hbase := q3PhysicalCrossedConstant_eq_ofReal
    (A := A) (B := B) (q := q) hA hB hq
  calc
    q3PhysicalCrossedConstant (A * R)
        (B * R ^ (a - (n : Real))) q =
        ENNReal.ofReal
          (q3PhysicalCrossedRealConstant (A * R)
            (B * R ^ (a - (n : Real))) q) :=
      q3PhysicalCrossedConstant_eq_ofReal hAR hBR hq
    _ = ENNReal.ofReal
          (q3PhysicalCrossedRealConstant A B q *
            R ^ ((a - (n : Real)) + (q - 2))) := by rw [hreal]
    _ = ENNReal.ofReal (q3PhysicalCrossedRealConstant A B q) *
          ENNReal.ofReal (R ^ ((a - (n : Real)) + (q - 2))) :=
      ENNReal.ofReal_mul hpre
    _ = q3PhysicalCrossedConstant A B q *
          (ENNReal.ofReal R) ^ ((a - (n : Real)) + (q - 2)) := by
      rw [← hbase, ENNReal.ofReal_rpow_of_pos hR]

/-- After the output `q`-th root, the scale in the preceding theorem is
exactly the physical `Q₃` frequency exponent. -/
theorem q3PhysicalCrossedConstant_rpow_scale
    {n : Nat} {A B R a q : Real}
    (hA : 0 < A) (hB : 0 ≤ B) (hR : 0 < R) (hq : 2 < q) :
    (q3PhysicalCrossedConstant (A * R)
        (B * R ^ (a - (n : Real))) q) ^ q⁻¹ =
      (q3PhysicalCrossedConstant A B q) ^ q⁻¹ *
        (ENNReal.ofReal R) ^ q3PhysicalMinkowskiExponent n a q := by
  have hqpos : 0 < q := by linarith
  rw [q3PhysicalCrossedConstant_scale (n := n) (a := a) hA hB hR hq]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hqpos.le)]
  rw [← ENNReal.rpow_mul]
  congr 1
  unfold q3PhysicalMinkowskiExponent
  field_simp [hqpos.ne']
  ring

/-- Convert an unnormalized dyadic estimate to the normalized maximal
piece.  This is the one-line `surfaceMass⁻¹` conversion needed by
`absolute_off_diagonal_reassembly_from_eLpNorm`; it is kept as a separate
lemma so every `Q₃` rate below can be used by that reassembly directly. -/
theorem fractalDyadicBandpass_eLpNorm_le_of_unnormalized_rate
    {d : Nat} (hd : 0 < d) {E : Set Real} {psi f : SchwartzMap (Euclidean d) Complex}
    {j : Nat} {p q : Real} {CT rho : ENNReal}
    (hbound :
      eLpNorm (unnormalizedFractalDyadicBandpassMaximal d E psi f)
        (ENNReal.ofReal q) volume ≤
        CT * rho ^ j *
          eLpNorm (f : Euclidean d → Complex) (ENNReal.ofReal p) volume) :
    eLpNorm (fractalDyadicBandpassMaximal d E psi f)
      (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal ((surfaceMass d)⁻¹) * CT * rho ^ j *
        eLpNorm (f : Euclidean d → Complex) (ENNReal.ofReal p) volume := by
  let s : Real := surfaceMass d
  have hs : 0 < s := by
    dsimp only [s]
    exact surfaceMass_pos hd
  have hsInv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hrewrite : fractalDyadicBandpassMaximal d E psi f =
      fun x => s⁻¹ * unnormalizedFractalDyadicBandpassMaximal d E psi f x := by
    funext x
    dsimp only [s]
    unfold unnormalizedFractalDyadicBandpassMaximal
    field_simp [ne_of_gt hs]
  rw [hrewrite]
  change eLpNorm (s⁻¹ • unnormalizedFractalDyadicBandpassMaximal d E psi f)
      (ENNReal.ofReal q) volume ≤ _
  rw [eLpNorm_const_smul]
  have hcoeff : ‖(s⁻¹ : Real)‖ₑ = ENNReal.ofReal s⁻¹ :=
    Real.enorm_eq_ofReal hsInv
  rw [hcoeff]
  calc
    ENNReal.ofReal s⁻¹ *
        eLpNorm (unnormalizedFractalDyadicBandpassMaximal d E psi f)
          (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal s⁻¹ *
          (CT * rho ^ j *
            eLpNorm (f : Euclidean d → Complex) (ENNReal.ofReal p) volume) :=
      mul_le_mul_right hbound _
    _ = _ := by ring

/-- The literal strict dyadic `Q₃` estimate.  A global upper Minkowski
covering exponent `alpha`, used with its unavoidable loss `eps`, gives a
single positive coefficient and a single ratio below one for every positive
dyadic level.  The `L¹ → L∞` input in this proof is the physical shell bound
from `AbsoluteDyadicPhysicalEndpoint`.

The conclusion is intentionally on the Schwartz carrier: it is the exact
fixed-level estimate consumed by the later interpolation and density steps. -/
theorem q3_physical_strict_dyadic_rate_of_hasUpperMinkowskiExponent_of_sharp
    {n : Nat} (hn : 2 ≤ n)
    (C0 C1 : Real) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ xi : Euclidean (n + 1), 1 ≤ ‖xi‖ →
      ‖surfaceFourier (n + 1) xi‖ ≤ C0 / ‖xi‖ ^ ((n : Real) / 2))
    (hderiv : ∀ xi : Euclidean (n + 1), ∀ s : Real, 1 ≤ ‖xi‖ →
      s ∈ Icc (1 : Real) 2 →
      ‖deriv (fun t : Real => surfaceFourier (n + 1) (t • xi)) s‖ ≤
        C1 / ‖xi‖ ^ ((n : Real) / 2 - 1))
    {E : Set Real} (hE : E ⊆ Icc (1 : Real) 2) (hEne : E.Nonempty)
    {alpha eps p q : Real} (hM : HasUpperMinkowskiExponent E alpha)
    (heps : 0 < eps) (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (hstrict : q < (n : Real) + 2 - (alpha + eps))
    (phi psi : SchwartzMap (Euclidean (n + 1)) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi, ‖phi xi‖ ≤ 1)
    (hpsi : ∀ xi : Euclidean (n + 1),
      psi xi = phi (((2 : Real) ^ (0 + 1))⁻¹ • xi) -
        phi (((2 : Real) ^ 0)⁻¹ • xi)) :
    ∃ CT rho : ENNReal, 0 < CT ∧ CT < ∞ ∧ rho < 1 ∧
      rho = ENNReal.ofReal (q3PhysicalMinkowskiRatio n (alpha + eps) q) ∧
      ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean (n + 1)) Complex,
        eLpNorm (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal q) volume ≤
          CT * rho ^ j *
            eLpNorm (f : Euclidean (n + 1) → Complex)
              (ENNReal.ofReal p) volume := by
  let a : Real := alpha + eps
  obtain ⟨Ccover, hCcover, hCovers⟩ := hM eps heps
  obtain ⟨D, hD, hphysical⟩ :=
    exists_absoluteDyadicBandpass_lone_linf_endpoint (d := n + 1)
      (by omega) E hE phi hphiOne hphiZero
  let B2 : Real := 8 * C0 ^ 2 + 8 * C1 ^ 2
  let A0 : Real := surfaceMass (n + 1) * D
  let B0 : Real := Ccover * B2
  let CT : ENNReal := 1 + (q3PhysicalCrossedConstant A0 B0 q) ^ q⁻¹
  let rho : ENNReal :=
    ENNReal.ofReal (q3PhysicalMinkowskiRatio n a q)
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hqpos : 0 < q := by
    rw [hq]
    exact div_pos hp0 (by linarith)
  have hqtwo : 2 < q := by
    rw [hq]
    have hpminus : 0 < p - 1 := by linarith
    apply (lt_div_iff₀ hpminus).mpr
    nlinarith
  have ha : a = alpha + eps := rfl
  have hstricta : q < (n : Real) + 2 - a := by
    simpa only [ha] using hstrict
  have hrho : rho < 1 := by
    dsimp only [rho]
    exact ENNReal.ofReal_lt_one.mpr
      (q3PhysicalMinkowskiRatio_mem_Ioo hqpos hstricta).2
  have hCT : 0 < CT := by
    dsimp only [CT]
    exact zero_lt_one.trans_le (le_add_of_nonneg_right bot_le)
  have hcrossTop : q3PhysicalCrossedConstant A0 B0 q < ∞ := by
    unfold q3PhysicalCrossedConstant
    apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · apply ENNReal.mul_lt_top
      · apply ENNReal.mul_lt_top
        · norm_num
        · exact ENNReal.ofReal_lt_top
      · apply ENNReal.mul_lt_top
        · exact ENNReal.inv_lt_top.mpr
            (ENNReal.ofReal_pos.mpr (by linarith : 0 < q - 2))
        · exact ENNReal.rpow_lt_top_of_nonneg (by linarith)
            ENNReal.ofReal_ne_top
  have hCTtop : CT < ∞ := by
    dsimp only [CT]
    apply ENNReal.add_lt_top
    · norm_num
    · exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr hqpos.le)
        hcrossTop.ne
  refine ⟨CT, rho, hCT, hCTtop, hrho, rfl, ?_⟩
  intro j hj f
  let R : Real := LeanSpherical.HarmonicAnalysis.dyadicScale j
  let delta : Real := R⁻¹
  have hR : 0 < R := by
    dsimp only [R]
    exact LeanSpherical.HarmonicAnalysis.dyadicScale_pos j
  have hRone : 1 ≤ R := by
    dsimp only [R]
    exact one_le_absolute_dyadicScale j
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact inv_pos.mpr hR
  have hdeltaone : delta < 1 := by
    dsimp only [delta, R]
    exact inv_absolute_dyadicScale_lt_one hj
  have hdeltaR : delta ≤ R⁻¹ := by rfl
  obtain ⟨cover, hcover, hcard⟩ := hCovers delta hdelta hdeltaone
  have hcard' : (cover.card : Real) ≤ Ccover * delta ^ (-a) := by
    simpa only [a] using hcard
  have hdeltaScale : delta ^ (-a) = R ^ a := by
    dsimp only [delta]
    exact inv_rpow_neg_eq_rpow
  have hB2 : 0 ≤ B2 := by
    dsimp only [B2]
    positivity
  have hB0 : 0 ≤ B0 := by
    dsimp only [B0]
    exact mul_nonneg hCcover.le hB2
  have hA0 : 0 < A0 := by
    dsimp only [A0]
    exact mul_pos (surfaceMass_pos (by omega)) hD
  have hcoef :
      (Ccover * delta ^ (-a)) *
          ((8 * C0 ^ 2 + 8 * C1 ^ 2) * R ^ (-(n : Real))) =
        B0 * R ^ (a - (n : Real)) := by
    have hpower : R ^ a * R ^ (-(n : Real)) = R ^ (a - (n : Real)) := by
      rw [← Real.rpow_add hR]
      congr 1
    rw [hdeltaScale]
    dsimp only [B0, B2]
    calc
      (Ccover * R ^ a) *
          ((8 * C0 ^ 2 + 8 * C1 ^ 2) * R ^ (-(n : Real))) =
          (Ccover * (8 * C0 ^ 2 + 8 * C1 ^ 2)) *
            (R ^ a * R ^ (-(n : Real))) := by ring
      _ = _ := by rw [hpower]
  have hl2 : ∀ g : SchwartzMap (Euclidean (n + 1)) Complex,
      MemLp (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g) 2 volume ∧
      (∫ x : Euclidean (n + 1),
        ‖unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) g x‖ ^ (2 : Nat)) ≤
        (B0 * R ^ (a - (n : Real))) *
          ∫ x : Euclidean (n + 1), ‖g x‖ ^ (2 : Nat) := by
    intro g
    have hlocal := q3_literal_minkowski_cover_ltwo_of_sharp
      hn C0 C1 hC0 hC1 hdecay hderiv hE hEne hR hRone hdelta hdeltaone hdeltaR
      cover hcover hcard' phi psi hphiOne hphiZero hphiNorm hpsi hj (by rfl)
    rcases hlocal g with ⟨hmem, hbound⟩
    exact ⟨hmem, by simpa only [hcoef] using hbound⟩
  have hendpoint : ∀ g : SchwartzMap (Euclidean (n + 1)) Complex,
      ∀ x : Euclidean (n + 1),
      fractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) g x ≤
        D * R * ∫ y, ‖(g : Euclidean (n + 1) → Complex) y‖ := by
    intro g x
    simpa only [R, LeanSpherical.HarmonicAnalysis.dyadicScale] using
      hphysical j g x
  have hBscale : 0 ≤ B0 * R ^ (a - (n : Real)) :=
    mul_nonneg hB0 (Real.rpow_nonneg hR.le _)
  have hpiece :=
    q3_rational_schwartz_crossed_eLpNorm_of_physical_lone_ltwo_homogeneous
      (n := n) (E := E) (R := R) (D := D)
      (B := B0 * R ^ (a - (n : Real)))
      hE hR hD hBscale phi hphiOne hphiZero hendpoint hl2 hp1 hp2 hq f
  have hscale := q3PhysicalCrossedConstant_rpow_scale
    (n := n) (A := A0) (B := B0) (R := R) (a := a) (q := q)
    hA0 hB0 hR hqtwo
  have hRrate :
      (ENNReal.ofReal R) ^ q3PhysicalMinkowskiExponent n a q = rho ^ j := by
    dsimp only [R, rho, q3PhysicalMinkowskiRatio]
    rw [LeanSpherical.HarmonicAnalysis.dyadicScale]
    calc
      (ENNReal.ofReal ((2 : Real) ^ j)) ^ q3PhysicalMinkowskiExponent n a q =
          ENNReal.ofReal
            (((2 : Real) ^ j) ^ q3PhysicalMinkowskiExponent n a q) :=
        (ENNReal.ofReal_rpow_of_pos (pow_pos (by norm_num) j)).symm
      _ = ENNReal.ofReal
          (((2 : Real) ^ q3PhysicalMinkowskiExponent n a q) ^ j) := by
        congr 1
        calc
          ((2 : Real) ^ j) ^ q3PhysicalMinkowskiExponent n a q =
              (2 : Real) ^ ((j : Real) * q3PhysicalMinkowskiExponent n a q) := by
            rw [← Real.rpow_natCast,
              ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
          _ = (2 : Real) ^
              (q3PhysicalMinkowskiExponent n a q * (j : Real)) := by
            congr 1
            ring
          _ = ((2 : Real) ^ q3PhysicalMinkowskiExponent n a q) ^ j :=
            Real.rpow_mul_natCast (by norm_num) _ _
      _ = (ENNReal.ofReal
          ((2 : Real) ^ q3PhysicalMinkowskiExponent n a q)) ^ j := by
        rw [ENNReal.ofReal_pow
          (Real.rpow_nonneg (by norm_num) _)]
  calc
    eLpNorm (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal q) volume ≤
        (q3PhysicalCrossedConstant (A0 * R)
          (B0 * R ^ (a - (n : Real))) q) ^ q⁻¹ *
          eLpNorm (f : Euclidean (n + 1) → Complex)
            (ENNReal.ofReal p) volume := by
      simpa only [A0, mul_assoc] using hpiece
    _ = ((q3PhysicalCrossedConstant A0 B0 q) ^ q⁻¹ *
          (ENNReal.ofReal R) ^ q3PhysicalMinkowskiExponent n a q) *
          eLpNorm (f : Euclidean (n + 1) → Complex)
            (ENNReal.ofReal p) volume := by rw [hscale]
    _ = (q3PhysicalCrossedConstant A0 B0 q) ^ q⁻¹ * rho ^ j *
          eLpNorm (f : Euclidean (n + 1) → Complex)
            (ENNReal.ofReal p) volume := by rw [hRrate]
    _ ≤ CT * rho ^ j *
          eLpNorm (f : Euclidean (n + 1) → Complex)
            (ENNReal.ofReal p) volume := by
      exact mul_le_mul_left
        (mul_le_mul_left (le_add_of_nonneg_right bot_le) (rho ^ j))
        (eLpNorm (f : Euclidean (n + 1) → Complex)
          (ENNReal.ofReal p) volume)

/-- The preceding strict-rate theorem with the upper Minkowski dimension
written as an equality.  Splitting the loss in half is necessary because
`HasUpperMinkowskiExponent` itself includes an arbitrarily small loss. -/
theorem q3_physical_strict_dyadic_rate_of_upperMinkowskiDimension_eq_of_sharp
    {n : Nat} (hn : 2 ≤ n)
    (C0 C1 : Real) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hdecay : ∀ xi : Euclidean (n + 1), 1 ≤ ‖xi‖ →
      ‖surfaceFourier (n + 1) xi‖ ≤ C0 / ‖xi‖ ^ ((n : Real) / 2))
    (hderiv : ∀ xi : Euclidean (n + 1), ∀ s : Real, 1 ≤ ‖xi‖ →
      s ∈ Icc (1 : Real) 2 →
      ‖deriv (fun t : Real => surfaceFourier (n + 1) (t • xi)) s‖ ≤
        C1 / ‖xi‖ ^ ((n : Real) / 2 - 1))
    {E : Set Real} (hE : E ⊆ Icc (1 : Real) 2) (hEne : E.Nonempty)
    {beta eps p q : Real} (hMinkowski : upperMinkowskiDimension E = beta)
    (heps : 0 < eps) (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (hstrict : q < (n : Real) + 2 - (beta + eps))
    (phi psi : SchwartzMap (Euclidean (n + 1)) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi, ‖phi xi‖ ≤ 1)
    (hpsi : ∀ xi : Euclidean (n + 1),
      psi xi = phi (((2 : Real) ^ (0 + 1))⁻¹ • xi) -
        phi (((2 : Real) ^ 0)⁻¹ • xi)) :
    ∃ CT rho : ENNReal, 0 < CT ∧ CT < ∞ ∧ rho < 1 ∧
      rho = ENNReal.ofReal (q3PhysicalMinkowskiRatio n (beta + eps) q) ∧
      ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean (n + 1)) Complex,
        eLpNorm (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal q) volume ≤
          CT * rho ^ j *
            eLpNorm (f : Euclidean (n + 1) → Complex)
              (ENNReal.ofReal p) volume := by
  let half : Real := eps / 2
  have hhalf : 0 < half := by
    dsimp only [half]
    linarith
  have hM : HasUpperMinkowskiExponent E (beta + half) := by
    exact hasUpperMinkowskiExponent_add_of_upperMinkowskiDimension_eq
      hE hMinkowski hhalf
  have hsum : (beta + half) + half = beta + eps := by
    dsimp only [half]
    ring
  have hstrict' : q < (n : Real) + 2 - ((beta + half) + half) := by
    rw [hsum]
    exact hstrict
  obtain ⟨CT, rho, hCT, hCTtop, hrho, hrhoeq, hbound⟩ :=
    q3_physical_strict_dyadic_rate_of_hasUpperMinkowskiExponent_of_sharp
      hn C0 C1 hC0 hC1 hdecay hderiv hE hEne hM hhalf hp1 hp2 hq hstrict'
      phi psi hphiOne hphiZero hphiNorm hpsi
  refine ⟨CT, rho, hCT, hCTtop, hrho, ?_, hbound⟩
  rw [hrhoeq, hsum]

/-- The actual higher-dimensional `Q₃` strict rate, with the sharp Fourier
inputs supplied by the existing Stein surface theorem.  Indeed, this is the
direct specialization of
`exists_theoremOneSharpSurfaceFourierInput (d := n + 1) (gamma := 0)` to
the `d = n + 1 ≥ 3` branch. -/
theorem q3_physical_strict_dyadic_rate_of_upperMinkowskiDimension_eq
    {n : Nat} (hn : 2 ≤ n)
    {E : Set Real} (hE : E ⊆ Icc (1 : Real) 2) (hEne : E.Nonempty)
    {beta eps p q : Real} (hMinkowski : upperMinkowskiDimension E = beta)
    (heps : 0 < eps) (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (hstrict : q < (n : Real) + 2 - (beta + eps))
    (phi psi : SchwartzMap (Euclidean (n + 1)) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi, ‖phi xi‖ ≤ 1)
    (hpsi : ∀ xi : Euclidean (n + 1),
      psi xi = phi (((2 : Real) ^ (0 + 1))⁻¹ • xi) -
        phi (((2 : Real) ^ 0)⁻¹ • xi)) :
    ∃ CT rho : ENNReal, 0 < CT ∧ CT < ∞ ∧ rho < 1 ∧
      rho = ENNReal.ofReal (q3PhysicalMinkowskiRatio n (beta + eps) q) ∧
      ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean (n + 1)) Complex,
        eLpNorm (unnormalizedFractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal q) volume ≤
          CT * rho ^ j *
            eLpNorm (f : Euclidean (n + 1) → Complex)
              (ENNReal.ofReal p) volume := by
  obtain ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩ :=
    exists_theoremOneSharpSurfaceFourierInput
      (d := n + 1) (gamma := (0 : Real)) (Or.inl (by omega))
  exact q3_physical_strict_dyadic_rate_of_upperMinkowskiDimension_eq_of_sharp
    hn C0 C1 hC0 hC1 hdecay hderiv hE hEne hMinkowski heps hp1 hp2 hq hstrict
    phi psi hphiOne hphiZero hphiNorm hpsi

/-- The normalized, finite-constant form of the higher-dimensional strict
`Q₃` rate.  Besides the explicit inverse surface-mass normalization, this
packages measurability and finiteness into `MemLp`; it is therefore the
literal fixed-dyadic input for both ordinary T123 interpolation and the
dyadic reassembly theorem. -/
theorem q3_physical_strict_normalized_dyadic_rate_of_upperMinkowskiDimension_eq
    {n : Nat} (hn : 2 ≤ n)
    {E : Set Real} (hE : E ⊆ Icc (1 : Real) 2) (hEne : E.Nonempty)
    {beta eps p q : Real} (hMinkowski : upperMinkowskiDimension E = beta)
    (heps : 0 < eps) (hp1 : 1 < p) (hp2 : p < 2)
    (hq : q = p / (p - 1))
    (hstrict : q < (n : Real) + 2 - (beta + eps))
    (phi psi : SchwartzMap (Euclidean (n + 1)) Complex)
    (hphiOne : ∀ xi, ‖xi‖ ≤ 1 → phi xi = 1)
    (hphiZero : ∀ xi, 2 ≤ ‖xi‖ → phi xi = 0)
    (hphiNorm : ∀ xi, ‖phi xi‖ ≤ 1)
    (hpsi : ∀ xi : Euclidean (n + 1),
      psi xi = phi (((2 : Real) ^ (0 + 1))⁻¹ • xi) -
        phi (((2 : Real) ^ 0)⁻¹ • xi)) :
    ∃ C rho : ENNReal, 0 < C ∧ C < ∞ ∧ rho < 1 ∧
      rho = ENNReal.ofReal (q3PhysicalMinkowskiRatio n (beta + eps) q) ∧
      ∀ j : Nat, 1 ≤ j → ∀ f : SchwartzMap (Euclidean (n + 1)) Complex,
        MemLp (fractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal q) volume ∧
        eLpNorm (fractalDyadicBandpassMaximal (n + 1) E
          (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
          (ENNReal.ofReal q) volume ≤
          C * rho ^ j *
            eLpNorm (f : Euclidean (n + 1) → Complex)
              (ENNReal.ofReal p) volume := by
  obtain ⟨CT, rho, hCT, hCTtop, hrho, hrhoeq, hraw⟩ :=
    q3_physical_strict_dyadic_rate_of_upperMinkowskiDimension_eq
      hn hE hEne hMinkowski heps hp1 hp2 hq hstrict
      phi psi hphiOne hphiZero hphiNorm hpsi
  let C : ENNReal := ENNReal.ofReal ((surfaceMass (n + 1))⁻¹) * CT
  have hmass : 0 < surfaceMass (n + 1) := surfaceMass_pos (by omega)
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (ENNReal.ofReal_pos.mpr (inv_pos.mpr hmass)) hCT
  have hCtop : C < ∞ := by
    dsimp only [C]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCTtop
  refine ⟨C, rho, hC, hCtop, hrho, hrhoeq, ?_⟩
  intro j hj f
  have hnorm := fractalDyadicBandpass_eLpNorm_le_of_unnormalized_rate
    (d := n + 1) (p := p) (q := q) (by omega) (hraw j hj f)
  have hnorm' :
      eLpNorm (fractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal q) volume ≤
        C * rho ^ j *
          eLpNorm (f : Euclidean (n + 1) → Complex)
            (ENNReal.ofReal p) volume := by
    simpa only [C] using hnorm
  have hrhotop : rho < ∞ := lt_trans hrho (by simp)
  have hfactorTop : C * rho ^ j < ∞ :=
    ENNReal.mul_lt_top hCtop (ENNReal.pow_lt_top hrhotop)
  have hinputTop :
      eLpNorm (f : Euclidean (n + 1) → Complex)
        (ENNReal.ofReal p) volume < ∞ :=
    (f.memLp (ENNReal.ofReal p) volume).2
  have hnormTop :
      eLpNorm (fractalDyadicBandpassMaximal (n + 1) E
        (absoluteDyadicBandpass phi hphiOne hphiZero j) f)
        (ENNReal.ofReal q) volume < ∞ :=
    lt_of_le_of_lt hnorm' (ENNReal.mul_lt_top hfactorTop hinputTop)
  refine ⟨?_, hnorm'⟩
  exact ⟨(measurable_fractalDyadicBandpassMaximal E
    (absoluteDyadicBandpass phi hphiOne hphiZero j) f).aestronglyMeasurable,
    hnormTop⟩

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
