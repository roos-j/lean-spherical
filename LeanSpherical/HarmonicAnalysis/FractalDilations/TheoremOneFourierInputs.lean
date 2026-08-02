/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.CircleSurface
import LeanSpherical.HarmonicAnalysis.SurfaceHeight

/-!
# Fourier inputs in the dimensional range of Theorem 1

The fractal-dilation proof needs the sharp decay of the Fourier transform of
surface measure and its radial derivative.  These are not additional
hypotheses: in dimensions at least three they are the literal stationary
phase inputs already proved for Stein's theorem, while in dimension two they
are supplied by the circle calculation.

This small file packages the two cases with the exponent written in ambient
dimension.  It is deliberately separate from the `Q3` and `Q4` arguments:
those arguments use these Fourier estimates only for their pairwise `L2`
multiplier endpoint, whereas their physical kernel estimates are proved from
the paper's radius-gap argument.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open Metric Set

noncomputable section

/-- The sharp surface-Fourier data used in the nonendpoint proof. -/
def HasTheoremOneSharpSurfaceFourierInput (d : Nat) : Prop :=
  exists C0 C1 : Real, 0 < C0 /\ 0 < C1 /\
    (forall xi : Euclidean d, 1 <= norm xi ->
      norm (surfaceFourier d xi) <=
        C0 / norm xi ^ (((d - 1 : Nat) : Real) / 2)) /\
    (forall xi : Euclidean d, forall r : Real, 1 <= norm xi -> r ∈ Icc (1 : Real) 2 ->
      norm (deriv (fun s : Real => surfaceFourier d (s • xi)) r) <=
        C1 / norm xi ^ (((d - 1 : Nat) : Real) / 2 - 1))

/-- In exactly the dimensional range of Theorem 1, the sharp Fourier decay
and radial-derivative estimates are available as proved input. -/
theorem exists_theoremOneSharpSurfaceFourierInput
    {d : Nat} {gamma : Real}
    (hd : 3 <= d \/ d = 2 /\ gamma <= 1 / 2) :
    HasTheoremOneSharpSurfaceFourierInput d := by
  rcases hd with hd | hcircle
  · obtain ⟨n, hn, rfl⟩ : exists n : Nat, 2 <= n /\ d = n + 1 := by
      refine ⟨d - 1, ?_, ?_⟩ <;> omega
    obtain ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩ :=
      exists_sharp_surfaceFourier_succ_decay_and_deriv hn
    exact ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩
  · rcases hcircle with ⟨hdim, _⟩
    subst d
    obtain ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩ :=
      exists_sharp_surfaceFourier_two_decay_and_deriv
    refine ⟨C0, C1, hC0, hC1, ?_, ?_⟩
    · intro xi hxi
      simpa using hdecay xi hxi
    · intro xi r hxi hr
      simpa using hderiv xi r hxi hr

/-- The decay component of the packaged Fourier input. -/
theorem HasTheoremOneSharpSurfaceFourierInput.decay
    {d : Nat} (h : HasTheoremOneSharpSurfaceFourierInput d) :
    exists C : Real, 0 < C /\ forall xi : Euclidean d, 1 <= norm xi ->
      norm (surfaceFourier d xi) <=
        C / norm xi ^ (((d - 1 : Nat) : Real) / 2) := by
  rcases h with ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩
  exact ⟨C0, hC0, hdecay⟩

/-- The radial-derivative component of the packaged Fourier input. -/
theorem HasTheoremOneSharpSurfaceFourierInput.deriv
    {d : Nat} (h : HasTheoremOneSharpSurfaceFourierInput d) :
    exists C : Real, 0 < C /\ forall xi : Euclidean d, forall r : Real,
      1 <= norm xi -> r ∈ Icc (1 : Real) 2 ->
        norm (deriv (fun s : Real => surfaceFourier d (s • xi)) r) <=
          C / norm xi ^ (((d - 1 : Nat) : Real) / 2 - 1) := by
  rcases h with ⟨C0, C1, hC0, hC1, hdecay, hderiv⟩
  exact ⟨C1, hC1, hderiv⟩

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
