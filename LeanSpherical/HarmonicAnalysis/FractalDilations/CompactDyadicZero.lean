/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.CompactLowpassImproving
import LeanSpherical.HarmonicAnalysis.FractalDilations.TheoremOneFourierInputs
import LeanSpherical.HarmonicAnalysis.FractalDilations.CircleDyadicL2

/-!
# The fixed zero-th absolute dyadic band

The off-diagonal argument only has a geometric estimate at positive dyadic
frequencies.  The `j = 0` term is a single compact multiplier,
```
  phi(xi / 2) - phi(xi),
```
whose support is allowed to reach radius four and whose norm is allowed to
reach two.  This file treats that term directly.  In particular it does not
misapply the lowpass theorem, whose normalization is different.

The two local endpoints are the actual physical short-interval `L¹` bound
and the actual sharp-Fourier `L²` bound.  A one-element cover of `[1,2]`
then supplies the raw endpoints required by the compact Marcinkiewicz
calculation, and the Schwartz kernel gives the strict improving estimate.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Filter MeasureTheory FourierTransform Metric Set ENNReal
open scoped FourierTransform

noncomputable section

/-- A single fixed radius interval turns a literal local square estimate for
the zero-th canonical bandpass into the two raw endpoints used by the
compact interpolation calculation.  The `L¹` endpoint is constructed here
from the physical kernel; the only supplied datum is the genuine local
`L²` estimate. -/
theorem exists_absoluteDyadicBandpass_zero_unnormalized_endpoints_of_local_ltwo
    {d : Nat} (hd : 0 < d) (E : Set Real) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ <= 1 -> phi xi = 1)
    (hphiZero : ∀ xi, 2 <= ‖xi‖ -> phi xi = 0)
    {c₂ : Real} (hc₂ : 0 <= c₂)
    (hlocal₂ : ∀ g : SchwartzMap (Euclidean d) Complex,
      MemLp (sphericalIntervalMaximalRaw (1 : Real) 2
        (dyadicBandpassProjection
          (absoluteDyadicBandpass phi hphiOne hphiZero 0) g)) 2 volume ∧
      (∫ x : Euclidean d,
        ‖sphericalIntervalMaximalRaw (1 : Real) 2
          (dyadicBandpassProjection
            (absoluteDyadicBandpass phi hphiOne hphiZero 0) g) x‖ ^ (2 : Nat)) <=
        c₂ * ∫ x : Euclidean d, ‖g x‖ ^ (2 : Nat)) :
    ∃ c₁ : Real, 0 <= c₁ ∧
      (∀ g : SchwartzMap (Euclidean d) Complex,
        MemLp (unnormalizedFractalDyadicBandpassMaximal d E
          (absoluteDyadicBandpass phi hphiOne hphiZero 0) g) 1 volume ∧
        (∫ x : Euclidean d,
          ‖unnormalizedFractalDyadicBandpassMaximal d E
            (absoluteDyadicBandpass phi hphiOne hphiZero 0) g x‖) <=
          c₁ * ∫ x : Euclidean d, ‖g x‖) ∧
      (∀ g : SchwartzMap (Euclidean d) Complex,
        MemLp (unnormalizedFractalDyadicBandpassMaximal d E
          (absoluteDyadicBandpass phi hphiOne hphiZero 0) g) 2 volume ∧
        (∫ x : Euclidean d,
          ‖unnormalizedFractalDyadicBandpassMaximal d E
            (absoluteDyadicBandpass phi hphiOne hphiZero 0) g x‖ ^ (2 : Nat)) <=
          c₂ * ∫ x : Euclidean d, ‖g x‖ ^ (2 : Nat)) := by
  let psi : SchwartzMap (Euclidean d) Complex :=
    absoluteDyadicBandpass phi hphiOne hphiZero 0
  let s : Finset Unit := Finset.univ
  let a : Unit -> Real := fun _ => 1
  let b : Unit -> Real := fun _ => 2
  let c₁ : Real := surfaceMass d *
    ((∫ x : Euclidean d, ‖(𝓕⁻ psi : SchwartzMap (Euclidean d) Complex) x‖) +
      ∫ x : Euclidean d,
        ‖fderiv Real ((𝓕⁻ psi : SchwartzMap (Euclidean d) Complex) :
          Euclidean d -> Complex) x‖)
  have hs : s.Nonempty := by
    refine ⟨(), ?_⟩
    simp only [s, Finset.mem_univ]
  have hEpos : E ⊆ Ioi (0 : Real) := by
    intro r hr
    exact lt_of_lt_of_le zero_lt_one (hE hr).1
  have hcover : E ⊆ ⋃ i ∈ s, Icc (a i) (b i) := by
    intro r hr
    rw [Set.mem_iUnion]
    refine ⟨(), ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨by simp only [s, Finset.mem_univ], ?_⟩
    simpa only [a, b] using hE hr
  have hinterval : ∀ i ∈ s, Icc (a i) (b i) ⊆ Ioi (0 : Real) := by
    intro i hi r hr
    have hrone : 1 <= r := by simpa only [a] using hr.1
    exact lt_of_lt_of_le zero_lt_one hrone
  have hab : ∀ i ∈ s, a i <= b i := by
    intro i hi
    norm_num [a, b]
  have hc₁ : 0 <= c₁ := by
    dsimp only [c₁]
    apply mul_nonneg (surfaceMass_pos hd).le
    exact add_nonneg
      (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨c₁, hc₁, ?_, ?_⟩
  · intro g
    have hlocal : ∀ i ∈ s,
        MemLp (sphericalIntervalMaximalRaw (a i) (b i)
          (dyadicBandpassProjection psi g)) 1 volume ∧
        (∫ x : Euclidean d,
          ‖sphericalIntervalMaximalRaw (a i) (b i)
            (dyadicBandpassProjection psi g) x‖) <=
          c₁ * ∫ x : Euclidean d, ‖g x‖ := by
      intro i hi
      simpa only [psi, a, b, c₁] using
        (sphericalIntervalMaximalRaw_l1_uniform_of_scaled
          hd psi psi g (R := (1 : Real)) (a := (1 : Real)) (b := (2 : Real))
          (by norm_num) (by norm_num) (by norm_num) (fun xi => by simp))
    have hraw := unnormalizedFractalDyadicBandpass_memLp_one_of_finite_raw_cover
      (d := d) (ι := Unit) hd E psi s hs a b hcover hEpos hinterval hab g hlocal
    simpa [psi, s] using hraw
  · intro g
    have hlocal : ∀ i ∈ s,
        MemLp (sphericalIntervalMaximalRaw (a i) (b i)
          (dyadicBandpassProjection psi g)) 2 volume ∧
        (∫ x : Euclidean d,
          ‖sphericalIntervalMaximalRaw (a i) (b i)
            (dyadicBandpassProjection psi g) x‖ ^ (2 : Nat)) <=
          c₂ * ∫ x : Euclidean d, ‖g x‖ ^ (2 : Nat) := by
      intro i hi
      simpa only [psi, a, b] using hlocal₂ g
    have hraw := unnormalizedFractalDyadicBandpass_memLp_two_of_finite_raw_cover
      (d := d) (ι := Unit) hd E psi s hs a b hcover hEpos hinterval hab g hlocal
    simpa [psi, s] using hraw

/-- The literal zero-th absolute dyadic bandpass has concrete unnormalised
`L¹` and `L²` endpoints in the full dimensional range of Theorem 1.  The
two branches differ only in the already formalized sharp local square
estimate; neither branch assumes a maximal theorem. -/
theorem exists_absoluteDyadicBandpass_zero_unnormalized_endpoints
    {d : Nat} {gamma : Real}
    (hd : 3 <= d ∨ d = 2 ∧ gamma <= 1 / 2)
    (E : Set Real) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ <= 1 -> phi xi = 1)
    (hphiZero : ∀ xi, 2 <= ‖xi‖ -> phi xi = 0)
    (hphiNorm : ∀ xi, ‖phi xi‖ <= 1) :
    ∃ c₁ c₂ : Real, 0 <= c₁ ∧ 0 <= c₂ ∧
      (∀ g : SchwartzMap (Euclidean d) Complex,
        MemLp (unnormalizedFractalDyadicBandpassMaximal d E
          (absoluteDyadicBandpass phi hphiOne hphiZero 0) g) 1 volume ∧
        (∫ x : Euclidean d,
          ‖unnormalizedFractalDyadicBandpassMaximal d E
            (absoluteDyadicBandpass phi hphiOne hphiZero 0) g x‖) <=
          c₁ * ∫ x : Euclidean d, ‖g x‖) ∧
      (∀ g : SchwartzMap (Euclidean d) Complex,
        MemLp (unnormalizedFractalDyadicBandpassMaximal d E
          (absoluteDyadicBandpass phi hphiOne hphiZero 0) g) 2 volume ∧
        (∫ x : Euclidean d,
          ‖unnormalizedFractalDyadicBandpassMaximal d E
            (absoluteDyadicBandpass phi hphiOne hphiZero 0) g x‖ ^ (2 : Nat)) <=
          c₂ * ∫ x : Euclidean d, ‖g x‖ ^ (2 : Nat)) := by
  rcases exists_theoremOneSharpSurfaceFourierInput (d := d) (gamma := gamma) hd with
    ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩
  rcases hd with hd3 | hd2
  · obtain ⟨n, hn, rfl⟩ : ∃ n : Nat, 2 <= n ∧ d = n + 1 := by
      refine ⟨d - 1, ?_, ?_⟩ <;> omega
    let c₂ : Real :=
      2 * ((2 * C0) / (dyadicScale 0) ^ ((n : Real) / 2)) ^ 2 +
        2 * ((2 : Real) - 1) ^ 2 *
          ((2 * C1) / (dyadicScale 0) ^ ((n : Real) / 2 - 1)) ^ 2
    have hc₂ : 0 <= c₂ := by
      dsimp only [c₂]
      positivity
    obtain ⟨c₁, hc₁, hone, htwo⟩ :=
      exists_absoluteDyadicBandpass_zero_unnormalized_endpoints_of_local_ltwo
        (d := n + 1) (by omega) E hE phi hphiOne hphiZero hc₂ (by
          intro g
          simpa only [c₂] using
            (sphericalIntervalMaximalRaw_memLp_two_of_sharp
              hn C0 C1 hC0 hC1 hdecay hderiv phi g
              (absoluteDyadicBandpass phi hphiOne hphiZero 0)
              hphiOne hphiZero hphiNorm 0
              (absoluteDyadicBandpass_spec phi hphiOne hphiZero 0)
              (absoluteDyadicBandpass_compact phi hphiOne hphiZero 0)
              (by norm_num) (by
                intro r hr
                exact hr)))
    exact ⟨c₁, c₂, hc₁, hc₂, hone, htwo⟩
  · rcases hd2 with ⟨hdim, _⟩
    subst d
    let c₂ : Real :=
      2 * ((2 * C0) / (dyadicScale 0) ^ ((1 : Real) / 2)) ^ 2 +
        2 * ((2 : Real) - 1) ^ 2 *
          (4 * C1 * (dyadicScale 0) ^ ((1 : Real) / 2)) ^ 2
    have hc₂ : 0 <= c₂ := by
      dsimp only [c₂]
      positivity
    obtain ⟨c₁, hc₁, hone, htwo⟩ :=
      exists_absoluteDyadicBandpass_zero_unnormalized_endpoints_of_local_ltwo
        (d := 2) (by norm_num) E hE phi hphiOne hphiZero hc₂ (by
          intro g
          simpa only [c₂] using
            (sphericalIntervalMaximalRaw_memLp_two_of_circle_sharp
              C0 C1 hC0 hC1 hdecay hderiv phi g
              (absoluteDyadicBandpass phi hphiOne hphiZero 0)
              hphiOne hphiZero hphiNorm 0
              (absoluteDyadicBandpass_spec phi hphiOne hphiZero 0)
              (absoluteDyadicBandpass_compact phi hphiOne hphiZero 0)
              (by norm_num) (by
                intro r hr
                exact hr)))
    exact ⟨c₁, c₂, hc₁, hc₂, hone, htwo⟩

/-- The fixed `j = 0` absolute dyadic band is a literal compact improving
operator.  This is the finite term which supplements the geometrically
summable `j >= 1` Q4 bounds in the final proof of Theorem 1. -/
theorem absoluteDyadicBandpass_zero_improving_eLpNorm
    {d : Nat} {gamma p q : Real}
    (hd : 3 <= d ∨ d = 2 ∧ gamma <= 1 / 2)
    (E : Set Real) (hE : E ⊆ Icc (1 : Real) 2)
    (phi : SchwartzMap (Euclidean d) Complex)
    (hphiOne : ∀ xi, ‖xi‖ <= 1 -> phi xi = 1)
    (hphiZero : ∀ xi, 2 <= ‖xi‖ -> phi xi = 0)
    (hphiNorm : ∀ xi, ‖phi xi‖ <= 1)
    (hp : 1 < p) (hpq : p < q) :
    ∃ C : ENNReal, C < ⊤ ∧ ∀ f : SchwartzMap (Euclidean d) Complex,
      MemLp (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero 0) f)
        (ENNReal.ofReal q) volume ∧
      eLpNorm (fractalDyadicBandpassMaximal d E
        (absoluteDyadicBandpass phi hphiOne hphiZero 0) f)
        (ENNReal.ofReal q) volume <=
        C * eLpNorm (f : Euclidean d -> Complex) (ENNReal.ofReal p) volume := by
  have hd0 : 0 < d := by
    rcases hd with hd3 | hd2 <;> omega
  obtain ⟨c₁, c₂, hc₁, hc₂, hone, htwo⟩ :=
    exists_absoluteDyadicBandpass_zero_unnormalized_endpoints
      hd E hE phi hphiOne hphiZero hphiNorm
  obtain ⟨B, hB, hdiagonal⟩ :=
    compact_bandpass_diagonal_all_exponents_of_unnormalized_endpoints
      hd0 E hE (absoluteDyadicBandpass phi hphiOne hphiZero 0)
      hc₁ hc₂ hone htwo hp
  exact compact_bandpass_improving_eLpNorm_of_diagonal
    hd0 E hE (absoluteDyadicBandpass phi hphiOne hphiZero 0) hp hpq
    ⟨B, hB, hdiagonal⟩

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
