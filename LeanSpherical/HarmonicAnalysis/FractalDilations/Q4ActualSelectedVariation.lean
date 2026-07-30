/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4MinkowskiVariation
import LeanSpherical.HarmonicAnalysis.FractalDilations.Q4DerivativeVariationBridge

/-!
# From the actual selected derivative to the FTOC variation estimate

For every local offset, the paper estimates the finite active maximum of the
scaled radius derivatives.  The maximum is a continuous finite supremum of
literal derivative pieces; it is therefore jointly measurable in the offset
and spatial variable without making a joint-measurability assertion about an
argmax selector.  The selector is used only for the exact identification of
its norm with that finite supremum.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory Set ENNReal

noncomputable section

/-- The literal scaled radius derivative is jointly continuous in its radius
and spatial arguments. -/
theorem continuous_uncurry_q4ScaledNormalizedDyadicSurfaceRadiusDerivative
    {d : Nat} (psi f : SchwartzMap (Euclidean d) Complex) (j : Nat) :
    Continuous (fun z : Real × Euclidean d =>
      q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j z.1 z.2) := by
  simpa only [q4ScaledNormalizedDyadicSurfaceRadiusDerivative_eq_scale_mul] using
    ((continuous_const : Continuous fun _ : Real × Euclidean d =>
      (dyadicScale j : Complex)).mul
      (continuous_uncurry_normalizedSphericalAverageRadiusDerivative
        (dyadicBandpassProjection psi f)))

/-- The finite active supremum in the scaled FTOC term is jointly continuous.
This is the measurable family to which the interval Minkowski estimate is
applied. -/
theorem continuous_uncurry_activeDyadicScaledDerivativeSup
    {d : Nat} (E : Set Real) (j : Nat)
    (hs : (activeDyadicIndices E j).Nonempty)
    (psi f : SchwartzMap (Euclidean d) Complex) :
    Continuous (fun z : Real × Euclidean d =>
      activeDyadicDerivativeSup E j hs
        (fun t => q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j t z.2) z.1) := by
  unfold activeDyadicDerivativeSup dyadicDerivativeSup
  apply Continuous.finset_sup'_apply hs
  intro i hi
  exact
    ((continuous_uncurry_q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j).comp
      ((continuous_const.add continuous_fst).prodMk continuous_snd)).norm

/-- One literal scaled derivative piece has every positive finite moment on
Schwartz data.  The compact Fourier multiplier realization supplies the
Schwartz representative and the displayed pointwise identity returns to the
physical derivative. -/
theorem integrable_norm_q4ScaledNormalizedDyadicSurfaceRadiusDerivative_rpow_of_schwartz
    {d : Nat} (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    (j : Nat) (r : Real) (f : SchwartzMap (Euclidean d) Complex)
    {q : Real} (hq : 0 < q) :
    Integrable (fun x : Euclidean d =>
      ‖q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j r x‖ ^ q) volume := by
  have hschwartz : MemLp
      (q4ScaledNormalizedDyadicSurfaceRadiusDerivativeSchwartzPiece
        psi hpsiCompact j r f : Euclidean d -> Complex)
      (ENNReal.ofReal q) volume :=
    (q4ScaledNormalizedDyadicSurfaceRadiusDerivativeSchwartzPiece
      psi hpsiCompact j r f).memLp (ENNReal.ofReal q) volume
  have hphysical : MemLp
      (fun x : Euclidean d =>
        q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j r x)
      (ENNReal.ofReal q) volume := by
    apply hschwartz.ae_eq
    filter_upwards with x
    exact q4ScaledNormalizedDyadicSurfaceRadiusDerivativeSchwartzPiece_apply_eq
      psi hpsiCompact j r f x
  have hpow := hphysical.integrable_norm_rpow
    (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal hq.le] using hpow

/-- At every fixed local offset the literal finite derivative supremum has
an integrable positive power on Schwartz input.  This is obtained directly
from the finite family of compact-frequency Schwartz pieces; it is not a
consequence of the maximal estimate that will later bound its moment. -/
theorem integrable_activeDyadicScaledDerivativeSup_rpow_of_schwartz
    {d : Nat} (E : Set Real) (j : Nat)
    (hs : (activeDyadicIndices E j).Nonempty)
    (psi : SchwartzMap (Euclidean d) Complex)
    (hpsiCompact : HasCompactSupport (psi : Euclidean d -> Complex))
    (f : SchwartzMap (Euclidean d) Complex) (u : Real)
    {q : Real} (hq : 0 < q) :
    Integrable (fun x : Euclidean d =>
      activeDyadicDerivativeSup E j hs
        (fun t => q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j t x) u ^ q)
      volume := by
  let pieces : Int -> Euclidean d -> Complex := fun i x =>
    q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j (dyadicLeft j i + u) x
  have hfibre : ∀ i ∈ activeDyadicIndices E j,
      Integrable (fun x => ‖pieces i x‖ ^ q) volume := by
    intro i hi
    simpa only [pieces] using
      integrable_norm_q4ScaledNormalizedDyadicSurfaceRadiusDerivative_rpow_of_schwartz
        psi hpsiCompact j (dyadicLeft j i + u) f hq
  have hsum : Integrable (fun x : Euclidean d =>
      ∑ i ∈ activeDyadicIndices E j, ‖pieces i x‖ ^ q) volume :=
    integrable_finsetSum (activeDyadicIndices E j) hfibre
  have hmaxcont : Continuous (q4FiniteProductMaximal (activeDyadicIndices E j) hs pieces) := by
    unfold q4FiniteProductMaximal
    have happly :
        ((activeDyadicIndices E j).sup' hs
          (fun i => fun x : Euclidean d => ‖pieces i x‖) : Euclidean d -> Real) =
          fun x => (activeDyadicIndices E j).sup' hs (fun i => ‖pieces i x‖) := by
      funext x
      exact Finset.sup'_apply hs _ x
    rw [← happly]
    apply Continuous.finset_sup'_apply hs
    intro i hi
    exact (continuous_q4ScaledNormalizedDyadicSurfaceRadiusDerivative
      psi f j (dyadicLeft j i + u)).norm
  have hmaxint : Integrable (fun x : Euclidean d =>
      q4FiniteProductMaximal (activeDyadicIndices E j) hs pieces x ^ q) volume := by
    apply Integrable.mono' hsum
    · exact ((continuous_id.rpow_const (fun _ => Or.inr hq.le)).measurable.comp
        hmaxcont.measurable).aestronglyMeasurable
    · filter_upwards with x
      exact q4FiniteProductMaximal_rpow_le_fibreSum
        (activeDyadicIndices E j) hs q pieces x
  refine hmaxint.congr ?_
  filter_upwards with x
  rfl

/-- The actual selected scaled derivative variation term has the expected
`L^q` bound once the literal finite active family has the uniform fixed-offset
root estimate.  No `hvariation` assumption occurs: joint measurability comes
from the finite supremum above, Tonelli supplies product integrability, and
the selector equality identifies the resulting interval integral with the
term left by FTOC. -/
theorem q4ActiveDyadicScaledDerivativeVariationTerm_eLpNorm_le_of_uniform_root_bound
    {d : Nat} (E : Set Real) (j : Nat)
    (hs : (activeDyadicIndices E j).Nonempty)
    (psi f : SchwartzMap (Euclidean d) Complex)
    {q A : Real} (hq : 1 < q) (hA : 0 <= A)
    (hfibint : forall u, u ∈ Ioc (0 : Real) (dyadicScale j) ->
      Integrable (fun x =>
        activeDyadicDerivativeSup E j hs
          (fun t => q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j t x) u ^ q)
        volume)
    (hroot : forall u, u ∈ Ioc (0 : Real) (dyadicScale j) ->
      (integral fun x =>
        activeDyadicDerivativeSup E j hs
          (fun t => q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j t x) u ^ q
        ∂volume) ^ (1 / q) <= A) :
    MemLp (q4ActiveDyadicScaledDerivativeVariationTerm E j hs psi f)
      (ENNReal.ofReal q) volume /\
      eLpNorm (q4ActiveDyadicScaledDerivativeVariationTerm E j hs psi f)
        (ENNReal.ofReal q) volume <= ENNReal.ofReal (dyadicScale j * A) := by
  let H : Real -> Euclidean d -> Real := fun u x =>
    activeDyadicDerivativeSup E j hs
      (fun t => q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j t x) u
  have hHmeas : Measurable (Function.uncurry H) := by
    simpa only [H] using
      (continuous_uncurry_activeDyadicScaledDerivativeSup E j hs psi f).measurable
  have hHnonneg : forall u x, 0 <= H u x := by
    intro u x
    simpa only [H] using activeDyadicDerivativeSup_nonneg E j hs
      (fun t => q4ScaledNormalizedDyadicSurfaceRadiusDerivative psi f j t x) u
  have hprod : Integrable (fun z : Real × Euclidean d => H z.1 z.2 ^ q)
      ((volume.restrict (Ioc (0 : Real) (dyadicScale j))).prod volume) := by
    apply integrable_uncurry_rpow_of_uniform_interval_root_bound
      volume (dyadicScale j) H (dyadicScale_pos j) hq hA hHmeas hHnonneg
    · intro u hu
      simpa only [H] using hfibint u hu
    · intro u hu
      simpa only [H] using hroot u hu
  have hinterval := intervalIntegral_eLpNorm_le_of_uniform_root_bound
    volume (dyadicScale j) H (dyadicScale_pos j) hq hA hHmeas hHnonneg hprod
    (by
      intro u hu
      simpa only [H] using hroot u hu)
  have hvariationEq : q4ActiveDyadicScaledDerivativeVariationTerm E j hs psi f =
      fun x => ∫ u in (0 : Real)..dyadicScale j, H u x := by
    funext x
    simpa only [H] using
      q4ActiveDyadicScaledDerivativeVariationTerm_eq_integral_activeSup E j hs psi f x
  simpa only [hvariationEq] using hinterval

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
