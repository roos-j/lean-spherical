import LeanSpherical.Auto.FractalDimensions
import LeanSpherical.Auto.LittlewoodPaley
import LeanSpherical.Auto.MikhlinHormander
import LeanSpherical.Auto.RadialFourierTransform
import LeanSpherical.Auto.Spherical.Bourgain
import LeanSpherical.Auto.Spherical.FractalDilations.Auxiliary
import LeanSpherical.Auto.Spherical.LegendreAssouad
import LeanSpherical.Auto.Spherical.MSS
import LeanSpherical.Auto.Spherical.SurfaceMeasureDecay
import LeanSpherical.Auto.SteinInterpolation
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The BRRS fractal local-smoothing problem: analytic core

This module fixes the literal Euclidean (rather than logarithmic-radius)
objects in Beltran--Roos--Rutar--Seeger, *A fractal local smoothing problem
for the wave equation*, arXiv:2501.12805.  It contains the literal
definitions, statement-level packaging, and explicit bridges to the existing
planar local-smoothing inputs.  In particular, no declaration below asserts
Theorem 1.1.

Mathlib uses the Fourier character `exp (-2 pi i <x, xi>)`.  Accordingly the
physical-speed-one half-wave below has multiplier `exp (2 pi i t |xi|)`.
-/

namespace Auto.Spherical.FractalDilations.BRRS

open Set Filter MeasureTheory FourierTransform
open Auto.LittlewoodPaley
open Auto.Spherical.SurfaceMeasureDecay
open scoped BigOperators Convolution ENNReal FourierTransform Topology

noncomputable section

/-- The Euclidean spatial domain for the dimension-generic BRRS statement. -/
abbrev BRRSSpace (d : Nat) := Euclidean d

/-- The Schwartz test-function domain for the literal Fourier formula. -/
abbrev BRRSSchwartz (d : Nat) := SchwartzMap (BRRSSpace d) Complex

/-- A function is radial when it depends only on Euclidean distance from the
origin.  This is the reusable norm-radiality predicate from the
Mathlib-only radial Fourier API. -/
abbrev IsRadial {d : Nat} (f : BRRSSpace d → Complex) : Prop :=
  Auto.RadialFourierTransform.IsNormRadial f

/-- Invariance under every orthogonal change of Euclidean coordinates.
This is the reusable Fourier-stable form of radial symmetry. -/
abbrev IsOrthogonallyInvariant {d : Nat} (f : BRRSSpace d → Complex) : Prop :=
  Auto.RadialFourierTransform.IsOrthogonallyInvariant f

namespace IsOrthogonallyInvariant

/-- Orthogonal invariance is preserved by the Euclidean Fourier transform. -/
theorem fourier {d : Nat} {f : BRRSSpace d → Complex}
    (hf : IsOrthogonallyInvariant f) :
    IsOrthogonallyInvariant (𝓕 f) :=
  Auto.RadialFourierTransform.IsOrthogonallyInvariant.fourier hf

/-- Orthogonal invariance is also preserved by inverse Fourier transform. -/
theorem fourierInv {d : Nat} {f : BRRSSpace d → Complex}
    (hf : IsOrthogonallyInvariant f) :
    IsOrthogonallyInvariant (𝓕⁻ f) :=
  Auto.RadialFourierTransform.IsOrthogonallyInvariant.fourierInv hf

end IsOrthogonallyInvariant

/-- The repository's norm-based radiality hypothesis supplies the
orthogonal-invariance certificate used by Fourier-side reductions. -/
theorem IsRadial.orthogonallyInvariant {d : Nat} {f : BRRSSpace d → Complex}
    (hf : IsRadial f) : IsOrthogonallyInvariant f :=
  Auto.RadialFourierTransform.IsNormRadial.orthogonallyInvariant hf

/-- On a real inner-product space, the orthogonal group acts transitively on
each sphere.  Thus the Fourier-stable invariance formulation is equivalent to
the repository's norm-based notion of radiality.  The reflection in the
orthogonal complement of the span of `x - y` sends `x` to `y` whenever the
two points have equal norm. -/
theorem IsOrthogonallyInvariant.isRadial {d : Nat} {f : BRRSSpace d → Complex}
    (hf : IsOrthogonallyInvariant f) : IsRadial f := by
  intro x y hxy
  have hA := congrFun (hf ((ℝ ∙ (x - y))ᗮ.reflection)) x
  change f ((ℝ ∙ (x - y))ᗮ.reflection x) = f x at hA
  rw [Submodule.reflection_sub hxy] at hA
  exact hA.symm

/-- The norm-based and orthogonal-invariance formulations of radiality agree
on Euclidean space. -/
theorem isRadial_iff_orthogonallyInvariant {d : Nat} {f : BRRSSpace d → Complex} :
    IsRadial f ↔ IsOrthogonallyInvariant f :=
  ⟨IsRadial.orthogonallyInvariant, IsOrthogonallyInvariant.isRadial⟩

/-- The scalar smooth annular bump used in BRRS Theorem 1.1.

The paper writes `P_j = φ(2⁻ʲ |D|)` for a nonzero smooth bump with
`supp φ ⊆ (1 / 4, 4)`.  Giving the scalar symbol directly, rather than an
arbitrary Euclidean multiplier, makes the required radiality of the cutoff
part of the data. -/
structure BRRSAnnularCutoff where
  symbol : SchwartzMap Real Complex
  tsupport_subset : tsupport (symbol : Real → Complex) ⊆ Ioo (1 / 4 : Real) 4
  nontrivial : ∃ r : Real, symbol r ≠ 0

/-- The Euclidean covering number `N(E, delta)` from BRRS (1.4).

This reexports the single canonical additive entropy definition from
`LegendreAssouad`; a closed ball of radius `delta / 2` is an interval of
length `delta`. -/
abbrev brrsEntropyNumber := Auto.Spherical.LegendreAssouad.brrsEntropyNumber

/-- The time scale `2^{-j}` used for a BRRS discretization. -/
def dyadicTimeScale (j : Nat) : Real := ((2 : Real) ^ j)⁻¹

/-- A set of times is `delta`-separated when distinct times have Euclidean
distance at least `delta`. -/
def IsSeparatedSet (S : Set Real) (delta : Real) : Prop :=
  ∀ ⦃s : Real⦄, s ∈ S → ∀ ⦃t : Real⦄, t ∈ S → s ≠ t → delta ≤ |s - t|

/-- The finite-set form of `IsSeparatedSet`. -/
def IsSeparated (T : Finset Real) (delta : Real) : Prop :=
  IsSeparatedSet (↑T : Set Real) delta

/-- A finite separated subset which is maximal under inclusion among the
separated subsets of `E`.  This is the literal meaning of ``maximal
`δ`-separated subset'' in BRRS; it avoids adding a second, redundant
covering datum to the definition of a discretization. -/
def IsMaximalSeparatedSubset (E : Set Real) (delta : Real) (T : Finset Real) : Prop :=
  (↑T : Set Real) ⊆ E ∧ IsSeparated T delta ∧
    ∀ U : Set Real, U ⊆ E → IsSeparatedSet U delta →
      (↑T : Set Real) ⊆ U → U ⊆ (↑T : Set Real)

/-- A `2^{-j}`-discretization of `E`: a maximal `2^{-j}`-separated subset of
`E`. -/
def IsDyadicDiscretization (E : Set Real) (j : Nat) (T : Finset Real) : Prop :=
  IsMaximalSeparatedSubset E (dyadicTimeScale j) T

namespace IsMaximalSeparatedSubset

/-- A maximal separated set is, in particular, a subset of the ambient time
set. -/
theorem subset {E : Set Real} {delta : Real} {T : Finset Real}
    (hT : IsMaximalSeparatedSubset E delta T) : (↑T : Set Real) ⊆ E :=
  hT.1

/-- A maximal separated set retains its separation condition. -/
theorem separated {E : Set Real} {delta : Real} {T : Finset Real}
    (hT : IsMaximalSeparatedSubset E delta T) : IsSeparated T delta :=
  hT.2.1

/-- Maximality converts separation into a strict-radius covering: if the
separation scale is positive, every point of the ambient set is within
distance strictly less than that scale from a point of the finite set. -/
theorem exists_mem_abs_sub_lt {E : Set Real} {delta : Real} {T : Finset Real}
    (hT : IsMaximalSeparatedSubset E delta T) (hdelta : 0 < delta)
    {x : Real} (hx : x ∈ E) :
    ∃ t ∈ T, |x - t| < delta := by
  by_contra hcover
  have hfar : ∀ t : Real, t ∈ T → delta ≤ |x - t| := by
    intro t ht
    exact le_of_not_gt fun hlt => hcover ⟨t, ht, hlt⟩
  by_cases hxT : x ∈ T
  · exact hcover ⟨x, hxT, by simpa using hdelta⟩
  · let U : Set Real := (↑T : Set Real) ∪ {x}
    have hUsubset : U ⊆ E := by
      intro y hy
      simp only [U, mem_union, mem_singleton_iff] at hy
      rcases hy with hyT | rfl
      · exact hT.subset hyT
      · exact hx
    have hUseparated : IsSeparatedSet U delta := by
      intro s hs u hu hsu
      simp only [U, mem_union, mem_singleton_iff] at hs hu
      rcases hs with hsT | rfl
      · rcases hu with huT | rfl
        · exact hT.separated hsT huT hsu
        · simpa only [abs_sub_comm] using hfar s hsT
      · rcases hu with huT | rfl
        · exact hfar u huT
        · exact (hsu rfl).elim
    have hTsubU : (↑T : Set Real) ⊆ U := by
      intro y hy
      exact Or.inl hy
    have hUsubT : U ⊆ (↑T : Set Real) :=
      hT.2.2 U hUsubset hUseparated hTsubU
    exact hxT (hUsubT (by simp [U]))

/-- Inclusion-maximal separation is a genuine net condition.  The strict
covering radius obtained from maximality is enough for the closed-ball
covering convention used by the BRRS entropy. -/
theorem isCover {E : Set Real} {delta : NNReal} {T : Finset Real}
    (hT : IsMaximalSeparatedSubset E (delta : Real) T) (hdelta : 0 < delta) :
    Metric.IsCover delta E (↑T : Set Real) := by
  intro x hx
  have hdeltaReal : 0 < (delta : Real) := by
    exact_mod_cast hdelta
  rcases hT.exists_mem_abs_sub_lt hdeltaReal hx with ⟨t, ht, hxt⟩
  refine ⟨t, by simpa using ht, ?_⟩
  change edist x t ≤ (delta : ENNReal)
  rw [edist_dist, ENNReal.ofReal_le_coe, Real.dist_eq]
  exact hxt.le

/-- A maximal `δ`-separated finite set has at least the BRRS covering number
at diameter `2δ`.  This is the reverse cardinality bridge needed when the
sharpness construction turns local metric entropy into sampled times. -/
theorem brrsEntropyNumber_le_card_at_twice_scale
    {E : Set Real} {delta : NNReal} {T : Finset Real}
    (hT : IsMaximalSeparatedSubset E (delta : Real) T) (hdelta : 0 < delta) :
    brrsEntropyNumber E (2 * delta) ≤ (T.card : ENNReal) := by
  have hhalf : (2 * delta) / 2 = delta := by
    apply NNReal.eq
    ring
  change (Metric.externalCoveringNumber ((2 * delta) / 2) E : ENNReal) ≤ _
  rw [hhalf]
  exact_mod_cast
    ((hT.isCover hdelta).externalCoveringNumber_le_encard.trans_eq (by simp))

end IsMaximalSeparatedSubset

namespace IsDyadicDiscretization

/-- A BRRS dyadic discretization is contained in its time set. -/
theorem subset {E : Set Real} {j : Nat} {T : Finset Real}
    (hT : IsDyadicDiscretization E j T) : (↑T : Set Real) ⊆ E :=
  IsMaximalSeparatedSubset.subset hT

/-- A BRRS dyadic discretization is separated at its dyadic mesh scale. -/
theorem separated {E : Set Real} {j : Nat} {T : Finset Real}
    (hT : IsDyadicDiscretization E j T) : IsSeparated T (dyadicTimeScale j) :=
  IsMaximalSeparatedSubset.separated hT

/-- Every point of a BRRS time set lies strictly within one dyadic mesh scale
of a point of any of its dyadic discretizations. -/
theorem exists_mem_abs_sub_lt {E : Set Real} {j : Nat} {T : Finset Real}
    (hT : IsDyadicDiscretization E j T) {x : Real} (hx : x ∈ E) :
    ∃ t ∈ T, |x - t| < dyadicTimeScale j := by
  apply IsMaximalSeparatedSubset.exists_mem_abs_sub_lt hT
  · unfold dyadicTimeScale
    exact inv_pos.mpr (pow_pos (by norm_num) _)
  · exact hx

end IsDyadicDiscretization

/-- A finite set which is separated at scale `delta` has cardinality bounded
by the BRRS entropy of its ambient set at half that scale.

The half-scale is forced by the use of closed balls in `brrsEntropyNumber`:
weak `delta`-separation becomes strict metric separation at `delta / 2`,
which is exactly the scale to which the packing--covering inequality applies. -/
theorem finset_card_le_brrsEntropyNumber_half_scale_of_isSeparated
    {E : Set Real} {delta : Real} {T : Finset Real}
    (hdelta : 0 < delta) (hTsub : (↑T : Set Real) ⊆ E)
    (hTsep : IsSeparated T delta) :
    (T.card : ENNReal) ≤ brrsEntropyNumber E ⟨delta / 2, by positivity⟩ := by
  let rho : NNReal := ⟨delta / 2, by positivity⟩
  change (T.card : ENNReal) ≤ brrsEntropyNumber E rho
  have hrho : (rho : ENNReal) = ENNReal.ofReal (delta / 2) := by
    calc
      (rho : ENNReal) = ENNReal.ofReal (rho : Real) := ENNReal.coe_nnreal_eq rho
      _ = ENNReal.ofReal (delta / 2) := by
        congr 1
  have hsep : Metric.IsSeparated (rho : ENNReal) (↑T : Set Real) := by
    intro x hx y hy hxy
    rw [edist_dist, hrho]
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
    rw [Real.dist_eq]
    exact lt_of_lt_of_le (by linarith)
      (hTsep (by simpa using hx) (by simpa using hy) hxy)
  have htwo : 2 * (rho / 2) = rho := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_div]
    ring
  have hpack : (↑T : Set Real).encard ≤ Metric.packingNumber (2 * (rho / 2)) E := by
    rw [htwo]
    exact hsep.encard_le_packingNumber hTsub
  have hcover : Metric.packingNumber (2 * (rho / 2)) E ≤
      Metric.externalCoveringNumber (rho / 2) E :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber (rho / 2) E
  calc
    (T.card : ENNReal) = ((↑T : Set Real).encard : ENNReal) := by simp
    _ ≤ (Metric.packingNumber (2 * (rho / 2)) E : ENNReal) := by
      exact_mod_cast hpack
    _ ≤ (Metric.externalCoveringNumber (rho / 2) E : ENNReal) := by
      exact_mod_cast hcover
    _ = brrsEntropyNumber E rho := rfl

/-- The entropy-cardinality bridge for a BRRS dyadic discretization. -/
theorem dyadicDiscretization_card_le_brrsEntropyNumber_half_scale
    {E : Set Real} {j : Nat} {T : Finset Real}
    (hT : IsDyadicDiscretization E j T) :
    (T.card : ENNReal) ≤
      brrsEntropyNumber E ⟨dyadicTimeScale j / 2, by
        unfold dyadicTimeScale
        positivity⟩ := by
  apply finset_card_le_brrsEntropyNumber_half_scale_of_isSeparated
  · unfold dyadicTimeScale
    exact inv_pos.mpr (pow_pos (by norm_num) _)
  · exact hT.subset
  · exact hT.separated

/-- An upper Minkowski covering exponent bounds the Euclidean entropy used
by BRRS, with the same arbitrarily small exponent loss.  This is the exact
bridge from the repository's interval-cover formulation to the entropy in
the BRRS discretization statement. -/
theorem brrsEntropyNumber_le_of_hasUpperMinkowskiExponent
    {E : Set Real} {beta : Real}
    (hM : Auto.FractalDimensions.HasUpperMinkowskiExponent E beta) :
    ∀ epsilon : Real, 0 < epsilon → ∃ C : Real, 0 < C ∧
      ∀ delta : NNReal, 0 < (delta : Real) → (delta : Real) < 1 →
        brrsEntropyNumber E delta ≤
          ENNReal.ofReal (C * (delta : Real) ^ (-(beta + epsilon))) := by
  intro epsilon hepsilon
  obtain ⟨C, hC, hcover⟩ := hM epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro delta hdelta hdelta_one
  obtain ⟨centers, hcenters, hcard⟩ := hcover delta hdelta hdelta_one
  calc
    brrsEntropyNumber E delta ≤ (centers.card : ENNReal) :=
      Auto.Spherical.LegendreAssouad.brrsEntropyNumber_le_of_intervalCover hcenters
    _ = ENNReal.ofReal (centers.card : Real) := by simp
    _ ≤ ENNReal.ofReal (C * (delta : Real) ^ (-(beta + epsilon))) :=
      ENNReal.ofReal_le_ofReal hcard

/-- A dyadic BRRS discretization inherits the cardinality bound supplied by
any upper Minkowski exponent.  The half-mesh is forced by the closed-ball
entropy convention, not by a loss in the sampling argument. -/
theorem dyadicDiscretization_card_le_of_hasUpperMinkowskiExponent
    {E : Set Real} {beta : Real}
    (hM : Auto.FractalDimensions.HasUpperMinkowskiExponent E beta) :
    ∀ epsilon : Real, 0 < epsilon → ∃ C : Real, 0 < C ∧
      ∀ j : Nat, 1 ≤ j → ∀ T : Finset Real,
        IsDyadicDiscretization E j T →
          (T.card : Real) ≤ C *
            (dyadicTimeScale j / 2) ^ (-(beta + epsilon)) := by
  intro epsilon hepsilon
  obtain ⟨C, hC, hEntropy⟩ :=
    brrsEntropyNumber_le_of_hasUpperMinkowskiExponent hM epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro j _hj T hT
  let delta : NNReal := ⟨dyadicTimeScale j / 2, by
    unfold dyadicTimeScale
    exact (div_pos (inv_pos.mpr
      (pow_pos (by norm_num : (0 : Real) < 2) _))
      (by norm_num : (0 : Real) < 2)).le⟩
  have hdelta_pos : 0 < (delta : Real) := by
    change 0 < ((2 : Real) ^ j)⁻¹ / 2
    exact div_pos (inv_pos.mpr (pow_pos (by norm_num) _)) (by norm_num)
  have hdelta_lt_one : (delta : Real) < 1 := by
    have hpow : 1 ≤ (2 : Real) ^ j := one_le_pow₀ (by norm_num)
    have hinv : ((2 : Real) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpow
    change ((2 : Real) ^ j)⁻¹ / 2 < 1
    nlinarith
  have hcardENN : (T.card : ENNReal) ≤ brrsEntropyNumber E delta := by
    simpa only [delta] using
      dyadicDiscretization_card_le_brrsEntropyNumber_half_scale hT
  have hboundENN : (T.card : ENNReal) ≤
      ENNReal.ofReal (C * (delta : Real) ^ (-(beta + epsilon))) :=
    hcardENN.trans (hEntropy delta hdelta_pos hdelta_lt_one)
  have hnonneg : 0 ≤ C * (delta : Real) ^ (-(beta + epsilon)) :=
    mul_nonneg hC.le (Real.rpow_nonneg hdelta_pos.le _)
  have hreal :=
    (ENNReal.toReal_le_toReal (by simp) ENNReal.ofReal_ne_top).mpr hboundENN
  change (T.card : Real) ≤ C * (delta : Real) ^ (-(beta + epsilon))
  simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hnonneg] using hreal

/-- The positive half-wave multiplier in Mathlib's Fourier normalization. -/
def halfWaveMultiplier {d : Nat} (t : Real) : BRRSSpace d → Complex :=
  fun xi =>
    Complex.exp (((2 * Real.pi * t * ‖xi‖ : Real) : Complex) * Complex.I)

/-- The half-wave phase is radial in frequency. -/
theorem halfWaveMultiplier_isRadial {d : Nat} (t : Real) :
    IsRadial (halfWaveMultiplier (d := d) t) := by
  intro xi eta hnorm
  unfold halfWaveMultiplier
  rw [hnorm]

/-- Hence the half-wave phase is invariant under all orthogonal frequency
changes of coordinates. -/
theorem halfWaveMultiplier_orthogonallyInvariant {d : Nat} (t : Real) :
    IsOrthogonallyInvariant (halfWaveMultiplier (d := d) t) :=
  (halfWaveMultiplier_isRadial t).orthogonallyInvariant

/-- Away from frequency zero, the half-wave phase is smooth.  The annular
multiplier below supplies the removable-zero extension needed globally. -/
theorem halfWaveMultiplier_contDiffAt_of_ne_zero {d : Nat} (t : Real)
    {xi : BRRSSpace d} (hxi : xi ≠ 0) :
    ContDiffAt Real (⊤ : ℕ∞) (halfWaveMultiplier (d := d) t) xi := by
  unfold halfWaveMultiplier
  have hnorm : ContDiffAt Real (⊤ : ℕ∞)
      (fun eta : BRRSSpace d => ‖eta‖) xi :=
    contDiffAt_norm Real hxi
  have hreal : ContDiffAt Real (⊤ : ℕ∞)
      (fun eta : BRRSSpace d => 2 * Real.pi * t * ‖eta‖) xi := by
    have hconst : ContDiffAt Real (⊤ : ℕ∞)
        (fun _ : BRRSSpace d => 2 * Real.pi * t) xi :=
      contDiffAt_const
    exact hconst.mul hnorm
  have hcomplex : ContDiffAt Real (⊤ : ℕ∞)
      (fun eta : BRRSSpace d =>
        ((2 * Real.pi * t * ‖eta‖ : Real) : Complex) * Complex.I) xi := by
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp xi hreal).mul contDiffAt_const
  exact hcomplex.cexp

/-- The literal Schwartz half-wave `e^{it sqrt(-Delta)}`. -/
def halfWave {d : Nat} (t : Real) (f : BRRSSchwartz d) : BRRSSpace d → Complex :=
  fun x => 𝓕⁻ (fun xi : BRRSSpace d =>
    halfWaveMultiplier t xi * 𝓕 (f : BRRSSpace d → Complex) xi) x

/-- An auxiliary Littlewood--Paley realization of an annular projection.

When `C.cutoff` is radial, this is obtained by taking the difference of two
adjacent low-pass cutoffs.  The public BRRS statement below instead uses the
literal arbitrary annular bump `BRRSAnnularCutoff`. -/
def dyadicProjection {d : Nat} (C : lpCutoffs d) (j : Nat)
    (f : BRRSSchwartz d) : BRRSSpace d → Complex :=
  Auto.LittlewoodPaley.dyadicProjection C.cutoff j f

/-- The auxiliary Littlewood--Paley frequency-localized half-wave, retained
for comparison with the repository's pre-existing dyadic machinery. -/
def dyadicHalfWave {d : Nat} (C : lpCutoffs d) (j : Nat) (t : Real)
    (f : BRRSSchwartz d) : BRRSSpace d → Complex :=
  fun x => 𝓕⁻ (fun xi : BRRSSpace d =>
    halfWaveMultiplier t xi * dyadicBandpassMultiplier C.cutoff j xi *
      𝓕 (f : BRRSSpace d → Complex) xi) x

/-! ### The existing planar MSS local-smoothing theorem

The BRRS proof uses a substantially sharper fractal-time estimate than the
continuous local-smoothing statement.  Nevertheless, the latter is a real
analytic input to the planar full-time case.  The following identities make
the normalization bridge explicit: no change of Fourier convention, cutoff,
or half-wave sign is hidden when the MSS theorem is invoked below.
-/

/-- The auxiliary positive dyadic half-wave is exactly the positive planar
half-wave used in the MSS development. -/
theorem auxiliaryDyadicHalfWave_eq_mss (C : lpCutoffs 2) (j : Nat) (t : Real)
    (f : BRRSSchwartz 2) :
    dyadicHalfWave C j t f =
      Auto.Spherical.MSSBase.dyadicHalfWave C.cutoff .plus j t f := by
  funext x
  unfold dyadicHalfWave Auto.Spherical.MSSBase.dyadicHalfWave
  apply congrArg (fun g : BRRSSpace 2 → Complex => 𝓕⁻ g x)
  funext xi
  have hphase : halfWaveMultiplier t xi =
      Auto.Spherical.MSSBase.halfWaveMultiplier .plus t xi := by
    unfold halfWaveMultiplier Auto.Spherical.MSSBase.halfWaveMultiplier
    simp only [Auto.Spherical.MSSBase.WaveSign.toReal]
    congr 1
    push_cast
    ring
  rw [hphase]

/-- The BRRS auxiliary half-wave as a planar space--time function on the
MSS time slab `[1, 2]`. -/
def auxiliaryDyadicHalfWaveSpaceTime (C : lpCutoffs 2) (j : Nat)
    (f : BRRSSchwartz 2) : Euclidean 2 × Real → Complex :=
  fun z => dyadicHalfWave C j z.2 f z.1

/-- The space--time BRRS auxiliary half-wave agrees pointwise with the MSS
space--time half-wave. -/
theorem auxiliaryDyadicHalfWaveSpaceTime_eq_mss (C : lpCutoffs 2) (j : Nat)
    (f : BRRSSchwartz 2) :
    auxiliaryDyadicHalfWaveSpaceTime C j f =
      Auto.Spherical.MSSBase.dyadicHalfWaveSpaceTime C.cutoff .plus j f := by
  funext z
  exact congrFun (auxiliaryDyadicHalfWave_eq_mss C j z.2 f) z.1

/-- The fixed-time `L²` endpoint from MSS, transported to the BRRS auxiliary
dyadic half-wave. -/
theorem auxiliaryDyadicHalfWave_l2Endpoint (C : lpCutoffs 2) (j : Nat)
    (t : Real) (f : BRRSSchwartz 2) :
    (∫ x : BRRSSpace 2, ‖dyadicHalfWave C j t f x‖ ^ 2) ≤
      4 * ∫ x : BRRSSpace 2, ‖f x‖ ^ 2 := by
  simpa only [auxiliaryDyadicHalfWave_eq_mss] using
    Auto.Spherical.MSSBase.l2Endpoint C .plus j t f

/-- Summing the fixed-time MSS endpoint over an arbitrary finite collection
of times.  No separation or interval hypothesis is needed for this elementary
energy estimate; such information enters only when bounding `T.card`. -/
theorem auxiliaryDyadicHalfWave_l2Sum_le_card (C : lpCutoffs 2) (j : Nat)
    (T : Finset Real) (f : BRRSSchwartz 2) :
    (∑ t ∈ T, ∫ x : BRRSSpace 2, ‖dyadicHalfWave C j t f x‖ ^ 2) ≤
      4 * (T.card : Real) * ∫ x : BRRSSpace 2, ‖f x‖ ^ 2 := by
  calc
    (∑ t ∈ T, ∫ x : BRRSSpace 2, ‖dyadicHalfWave C j t f x‖ ^ 2) ≤
        ∑ _t ∈ T, 4 * ∫ x : BRRSSpace 2, ‖f x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t _ht
      exact auxiliaryDyadicHalfWave_l2Endpoint C j t f
    _ = 4 * (T.card : Real) * ∫ x : BRRSSpace 2, ‖f x‖ ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- A finite BRRS dyadic discretization has a genuine planar auxiliary
`L²` energy bound at every upper Minkowski covering exponent.  This combines
the fixed-time MSS endpoint with the preceding entropy--cardinality bridge;
it is deliberately stated for the existing Littlewood--Paley cutoff rather
than claiming the arbitrary-cutoff BRRS theorem. -/
theorem auxiliaryDyadicHalfWave_l2Sum_le_of_hasUpperMinkowskiExponent
    (C : lpCutoffs 2) {E : Set Real} {beta : Real}
    (hM : Auto.FractalDimensions.HasUpperMinkowskiExponent E beta) :
    ∀ epsilon : Real, 0 < epsilon → ∃ K : Real, 0 < K ∧
      ∀ j : Nat, 1 ≤ j → ∀ T : Finset Real,
        IsDyadicDiscretization E j T → ∀ f : BRRSSchwartz 2,
          (∑ t ∈ T, ∫ x : BRRSSpace 2,
            ‖dyadicHalfWave C j t f x‖ ^ 2) ≤
              K * (dyadicTimeScale j / 2) ^ (-(beta + epsilon)) *
                ∫ x : BRRSSpace 2, ‖f x‖ ^ 2 := by
  intro epsilon hepsilon
  obtain ⟨A, hA, hcard⟩ :=
    dyadicDiscretization_card_le_of_hasUpperMinkowskiExponent hM epsilon hepsilon
  refine ⟨4 * A, mul_pos (by norm_num) hA, ?_⟩
  intro j hj T hT f
  have hsum := auxiliaryDyadicHalfWave_l2Sum_le_card C j T f
  have hTcard := hcard j hj T hT
  have hinput : 0 ≤ ∫ x : BRRSSpace 2, ‖f x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  calc
    (∑ t ∈ T, ∫ x : BRRSSpace 2, ‖dyadicHalfWave C j t f x‖ ^ 2) ≤
        4 * (T.card : Real) * ∫ x : BRRSSpace 2, ‖f x‖ ^ 2 := hsum
    _ = 4 * ((T.card : Real) * ∫ x : BRRSSpace 2, ‖f x‖ ^ 2) := by ring
    _ ≤ 4 * ((A * (dyadicTimeScale j / 2) ^ (-(beta + epsilon))) *
        ∫ x : BRRSSpace 2, ‖f x‖ ^ 2) := by
      gcongr
    _ = (4 * A) * (dyadicTimeScale j / 2) ^ (-(beta + epsilon)) *
        ∫ x : BRRSSpace 2, ‖f x‖ ^ 2 := by ring

/-- The already-proved planar MSS theorem, stated in the BRRS auxiliary
half-wave notation.  This is a continuous-time estimate on `[1,2]`; it does
not assert the fractal discrete-time estimate of BRRS Theorem 1.1. -/
theorem mssLocalSmoothing_auxiliaryDyadicHalfWave (C : lpCutoffs 2)
    {p eta : Real} (hp : 2 < p) (heta : 0 < eta) :
    2 < p ∧ 0 < eta ∧ ∃ K : Real, 0 < K ∧
      ∀ j : Nat, 1 ≤ j → ∀ f : BRRSSchwartz 2,
        eLpNorm (auxiliaryDyadicHalfWaveSpaceTime C j f) (ENNReal.ofReal p)
            Auto.Spherical.MSSBase.localSmoothingMeasure ≤
          ENNReal.ofReal (K * (2 : Real) ^
            ((j : Real) * (1 / 2 - 1 / p - Auto.Spherical.MSSBase.mssGain p + eta))) *
            eLpNorm (f : BRRSSpace 2 → Complex) (ENNReal.ofReal p) volume := by
  rcases Auto.Spherical.MSS.localSmoothing_of_lpCutoffs C hp heta with
    ⟨hp', heta', K, hK, hbound⟩
  refine ⟨hp', heta', K, hK, ?_⟩
  intro j hj f
  simpa only [auxiliaryDyadicHalfWaveSpaceTime_eq_mss] using
    hbound j hj f Auto.Spherical.MSSBase.WaveSign.plus

/-- The BRRS and MSS notations use the same dyadic temporal mesh. -/
theorem brrsDyadicTimeScale_eq_mss (j : Nat) :
    dyadicTimeScale j = Auto.Spherical.MSSBase.dyadicTimeScale j := by
  unfold dyadicTimeScale Auto.Spherical.MSSBase.dyadicTimeScale
  rw [zpow_neg, zpow_natCast]

/-- For the full interval `[1,2]`, a BRRS maximal discretization has the
finite-cover formulation of maximal separation used by MSS.  This is only a
comparison of discretization conventions; it does not turn continuous local
smoothing into the discrete fractal estimate. -/
theorem mssMaximalSeparated_of_brrsDyadicDiscretization (j : Nat)
    (T : Finset Real)
    (hT : IsDyadicDiscretization (Icc (1 : Real) 2) j T) :
    Auto.Spherical.MSSBase.MaximalSeparated j T := by
  rw [Auto.Spherical.MSSBase.MaximalSeparated, ← brrsDyadicTimeScale_eq_mss]
  rcases hT with ⟨hsubset, hseparated, hmaximal⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact hsubset ht
  · intro s hs u hu hsu
    exact hseparated (by simpa using hs) (by simpa using hu) hsu
  · intro t ht
    by_contra hcover
    have hfar : ∀ s : Real, s ∈ T → dyadicTimeScale j ≤ |t - s| := by
      intro s hs
      apply le_of_not_gt
      intro hlt
      exact hcover ⟨s, hs, hlt⟩
    by_cases htT : t ∈ T
    · apply hcover
      refine ⟨t, htT, ?_⟩
      have hdelta : 0 < dyadicTimeScale j := by
        unfold dyadicTimeScale
        exact inv_pos.mpr (pow_pos (by norm_num) _)
      simpa using hdelta
    · let U : Set Real := (↑T : Set Real) ∪ {t}
      have hUsubset : U ⊆ Icc (1 : Real) 2 := by
        intro x hx
        simp only [U, mem_union, mem_singleton_iff] at hx
        rcases hx with hxT | rfl
        · exact hsubset hxT
        · exact ht
      have hUseparated : IsSeparatedSet U (dyadicTimeScale j) := by
        intro s hs u hu hsu
        simp only [U, mem_union, mem_singleton_iff] at hs hu
        rcases hs with hsT | rfl
        · rcases hu with huT | rfl
          · exact hseparated hsT huT hsu
          · simpa only [abs_sub_comm] using hfar s hsT
        · rcases hu with huT | rfl
          · exact hfar u huT
          · exact (hsu rfl).elim
      have hTsubU : (↑T : Set Real) ⊆ U := by
        intro x hx
        simp only [U, mem_union]
        exact Or.inl hx
      have hUsubT : U ⊆ (↑T : Set Real) :=
        hmaximal U hUsubset hUseparated hTsubU
      apply htT
      apply hUsubT
      simp [U]

/-- The existing separated-time `L²` sampling argument gives a concrete
baseline for the auxiliary planar BRRS half-wave on the full time interval.
Its reciprocal-mesh loss is explicit, so this lemma is not the fractal
local-smoothing gain of BRRS Theorem 1.1. -/
theorem auxiliaryDyadicHalfWave_separatedSamplingL2
    (C : lpCutoffs 2) (j : Nat) (T : Finset Real)
    (hT : IsDyadicDiscretization (Icc (1 : Real) 2) j T)
    (f : BRRSSchwartz 2) :
    (∑ t ∈ T, ∫ x : BRRSSpace 2, ‖dyadicHalfWave C j t f x‖ ^ 2) ≤
      16 * (dyadicTimeScale j)⁻¹ * ∫ x : BRRSSpace 2, ‖f x‖ ^ 2 := by
  have hMSS : Auto.Spherical.MSSBase.MaximalSeparated j T :=
    mssMaximalSeparated_of_brrsDyadicDiscretization j T hT
  have h := Auto.Spherical.Bourgain.aux_dyadicHalfWave_separatedSamplingL2
    C Auto.Spherical.MSSBase.WaveSign.plus j T hMSS f
  simpa only [auxiliaryDyadicHalfWave_eq_mss,
    ← brrsDyadicTimeScale_eq_mss] using h

/-- The literal scaled annular multiplier `φ(2⁻ʲ |η|)` from BRRS.

Mathlib's Fourier variable is `xi = η / (2 π)`, so the source-frequency
argument is `2 π * 2⁻ʲ * ‖xi‖`. -/
def brrsFrequencyScale (j : Nat) : Real :=
  2 * Real.pi * ((2 : Real) ^ j)⁻¹

/-- The literal BRRS frequency scale is positive at every dyadic level. -/
theorem brrsFrequencyScale_pos (j : Nat) : 0 < brrsFrequencyScale j := by
  unfold brrsFrequencyScale
  positivity

def brrsDyadicMultiplier {d : Nat} (Φ : BRRSAnnularCutoff) (j : Nat)
    (xi : BRRSSpace d) : Complex :=
  Φ.symbol (2 * Real.pi * ((2 : Real) ^ j)⁻¹ * ‖xi‖)

/-- The frequency-scale form of the literal BRRS annular multiplier. -/
theorem brrsDyadicMultiplier_apply {d : Nat} (Φ : BRRSAnnularCutoff) (j : Nat)
    (xi : BRRSSpace d) :
    brrsDyadicMultiplier Φ j xi = Φ.symbol (brrsFrequencyScale j * ‖xi‖) :=
  rfl

/-- The literal annular multiplier vanishes whenever its radial argument is
outside the prescribed annular support. -/
theorem brrsDyadicMultiplier_eq_zero_of_not_mem {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (xi : BRRSSpace d)
    (hxi : brrsFrequencyScale j * ‖xi‖ ∉ Ioo (1 / 4 : Real) 4) :
    brrsDyadicMultiplier Φ j xi = 0 := by
  rw [brrsDyadicMultiplier_apply]
  by_contra hnonzero
  apply hxi
  apply Φ.tsupport_subset
  exact subset_tsupport _ (Function.mem_support.mpr hnonzero)

/-- The annular cutoff removes a neighborhood of the frequency origin. -/
theorem brrsDyadicMultiplier_eq_zero_of_norm_lt {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (xi : BRRSSpace d)
    (hxi : ‖xi‖ < (4 * brrsFrequencyScale j)⁻¹) :
    brrsDyadicMultiplier Φ j xi = 0 := by
  apply brrsDyadicMultiplier_eq_zero_of_not_mem
  intro hmem
  have hscale : 0 < brrsFrequencyScale j := brrsFrequencyScale_pos j
  have hscaled : brrsFrequencyScale j * ‖xi‖ < 1 / 4 := by
    calc
      brrsFrequencyScale j * ‖xi‖ <
          brrsFrequencyScale j * (4 * brrsFrequencyScale j)⁻¹ :=
        mul_lt_mul_of_pos_left hxi hscale
      _ = 1 / 4 := by
        field_simp [ne_of_gt hscale]
  exact (not_lt_of_ge hscaled.le) hmem.1

/-- The annular cutoff also vanishes beyond its outer frequency radius. -/
theorem brrsDyadicMultiplier_eq_zero_of_le_norm {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (xi : BRRSSpace d)
    (hxi : 4 * (brrsFrequencyScale j)⁻¹ ≤ ‖xi‖) :
    brrsDyadicMultiplier Φ j xi = 0 := by
  apply brrsDyadicMultiplier_eq_zero_of_not_mem
  intro hmem
  have hscale : 0 < brrsFrequencyScale j := brrsFrequencyScale_pos j
  have hscaled : 4 ≤ brrsFrequencyScale j * ‖xi‖ := by
    calc
      4 = brrsFrequencyScale j * (4 * (brrsFrequencyScale j)⁻¹) := by
        field_simp [ne_of_gt hscale]
      _ ≤ brrsFrequencyScale j * ‖xi‖ :=
        mul_le_mul_of_nonneg_left hxi hscale.le
  exact (not_lt_of_ge hscaled) hmem.2

/-- The literal BRRS annular multiplier is identically zero on a
neighborhood of frequency zero. -/
theorem brrsDyadicMultiplier_eventuallyEq_zero_at_zero {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) :
    brrsDyadicMultiplier (d := d) Φ j =ᶠ[nhds 0] fun _ => 0 := by
  have hscale : 0 < brrsFrequencyScale j := brrsFrequencyScale_pos j
  have hε : 0 < (4 * brrsFrequencyScale j)⁻¹ :=
    inv_pos.mpr (mul_pos (by norm_num) hscale)
  filter_upwards [Metric.ball_mem_nhds (0 : BRRSSpace d) hε] with xi hxi
  have hnorm : ‖xi‖ < (4 * brrsFrequencyScale j)⁻¹ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hxi
  exact brrsDyadicMultiplier_eq_zero_of_norm_lt Φ j xi hnorm

/-- The apparent nonsmoothness of `‖xi‖` at the origin is removable after
the annular cutoff: the literal BRRS multiplier is globally smooth. -/
theorem contDiff_brrsDyadicMultiplier {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) :
    ContDiff Real (⊤ : ℕ∞) (brrsDyadicMultiplier (d := d) Φ j) := by
  rw [contDiff_iff_contDiffAt]
  intro xi
  by_cases hxi : xi = 0
  · subst xi
    exact (contDiffAt_const (c := (0 : Complex))).congr_of_eventuallyEq
      (brrsDyadicMultiplier_eventuallyEq_zero_at_zero Φ j)
  · unfold brrsDyadicMultiplier
    refine (Φ.symbol.smooth (⊤ : ℕ∞)).contDiffAt.comp xi ?_
    have hnorm : ContDiffAt Real (⊤ : ℕ∞)
        (fun eta : BRRSSpace d => ‖eta‖) xi :=
      contDiffAt_norm Real hxi
    have hconst : ContDiffAt Real (⊤ : ℕ∞)
        (fun _ : BRRSSpace d => 2 * Real.pi * ((2 : Real) ^ j)⁻¹) xi :=
      contDiffAt_const
    exact hconst.mul hnorm

/-- The literal annular multiplier is compactly supported in frequency. -/
theorem hasCompactSupport_brrsDyadicMultiplier {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) :
    HasCompactSupport (brrsDyadicMultiplier (d := d) Φ j) := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : BRRSSpace d) (4 * (brrsFrequencyScale j)⁻¹))
  intro xi hxi
  have hnorm : 4 * (brrsFrequencyScale j)⁻¹ ≤ ‖xi‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hxi
    exact le_of_not_ge hxi
  exact brrsDyadicMultiplier_eq_zero_of_le_norm Φ j xi hnorm

/-- The literal BRRS annular multiplier packaged as a Schwartz frequency
symbol.  The preceding smoothness and compact-support lemmas make this a
genuine conversion, rather than an additional hypothesis on the cutoff. -/
noncomputable def brrsDyadicMultiplierSchwartz {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) : BRRSSchwartz d :=
  (hasCompactSupport_brrsDyadicMultiplier Φ j).toSchwartzMap
    (contDiff_brrsDyadicMultiplier Φ j)

/-- Evaluation of the packaged literal annular multiplier. -/
theorem brrsDyadicMultiplierSchwartz_apply {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (xi : BRRSSpace d) :
    brrsDyadicMultiplierSchwartz Φ j xi = brrsDyadicMultiplier Φ j xi :=
  rfl

/-- A uniform pointwise bound for the packaged BRRS multiplier, expressed by
the zeroth Schwartz seminorm of the one-dimensional cutoff. -/
theorem norm_brrsDyadicMultiplierSchwartz_le {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (xi : BRRSSpace d) :
    ‖brrsDyadicMultiplierSchwartz Φ j xi‖ ≤
      SchwartzMap.seminorm Complex 0 0 Φ.symbol := by
  rw [brrsDyadicMultiplierSchwartz_apply, brrsDyadicMultiplier_apply]
  exact SchwartzMap.norm_le_seminorm Complex Φ.symbol _

/-- Every literal BRRS annular multiplier is radial in its frequency
variable. -/
theorem brrsDyadicMultiplier_isRadial {d : Nat} (Φ : BRRSAnnularCutoff)
    (j : Nat) : IsRadial (brrsDyadicMultiplier (d := d) Φ j) := by
  intro xi eta hnorm
  unfold brrsDyadicMultiplier
  rw [hnorm]

/-- The annular BRRS multiplier is consequently invariant under orthogonal
frequency changes of coordinates. -/
theorem brrsDyadicMultiplier_orthogonallyInvariant {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) :
    IsOrthogonallyInvariant (brrsDyadicMultiplier (d := d) Φ j) :=
  (brrsDyadicMultiplier_isRadial Φ j).orthogonallyInvariant

/-- The Fourier-defined annular projection `P_j` used in BRRS Theorem 1.1. -/
def brrsDyadicProjection {d : Nat} (Φ : BRRSAnnularCutoff) (j : Nat)
    (f : BRRSSchwartz d) : BRRSSpace d → Complex :=
  fun x => 𝓕⁻ (fun xi : BRRSSpace d =>
    brrsDyadicMultiplier Φ j xi * 𝓕 (f : BRRSSpace d → Complex) xi) x

/-- The literal Fourier realization of `e^{it√{-Δ}} P_j` for the annular
cutoff fixed in BRRS. -/
def brrsDyadicHalfWave {d : Nat} (Φ : BRRSAnnularCutoff) (j : Nat)
    (t : Real) (f : BRRSSchwartz d) : BRRSSpace d → Complex :=
  fun x => 𝓕⁻ (fun xi : BRRSSpace d =>
    halfWaveMultiplier t xi * brrsDyadicMultiplier Φ j xi *
      𝓕 (f : BRRSSpace d → Complex) xi) x

/-- The frequency symbol of the literal BRRS annular half-wave. -/
def brrsDyadicHalfWaveSymbol {d : Nat} (Φ : BRRSAnnularCutoff) (j : Nat)
    (t : Real) : BRRSSpace d → Complex :=
  fun xi => halfWaveMultiplier t xi * brrsDyadicMultiplier Φ j xi

/-- Annular localization removes the nonsmooth frequency origin from the
literal half-wave symbol. -/
theorem brrsDyadicHalfWaveSymbol_eventuallyEq_zero_at_zero {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) :
    brrsDyadicHalfWaveSymbol (d := d) Φ j t =ᶠ[nhds 0] fun _ => 0 := by
  filter_upwards [brrsDyadicMultiplier_eventuallyEq_zero_at_zero Φ j] with xi hxi
  simp [brrsDyadicHalfWaveSymbol, hxi]

/-- The annular half-wave symbol is globally smooth. -/
theorem contDiff_brrsDyadicHalfWaveSymbol {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) :
    ContDiff Real (⊤ : ℕ∞) (brrsDyadicHalfWaveSymbol (d := d) Φ j t) := by
  rw [contDiff_iff_contDiffAt]
  intro xi
  by_cases hxi : xi = 0
  · subst xi
    exact (contDiffAt_const (c := (0 : Complex))).congr_of_eventuallyEq
      (brrsDyadicHalfWaveSymbol_eventuallyEq_zero_at_zero Φ j t)
  · unfold brrsDyadicHalfWaveSymbol
    exact (halfWaveMultiplier_contDiffAt_of_ne_zero t hxi).mul
      (contDiff_brrsDyadicMultiplier Φ j).contDiffAt

/-- The annular half-wave symbol has the same compact frequency support as
its annular factor. -/
theorem hasCompactSupport_brrsDyadicHalfWaveSymbol {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) :
    HasCompactSupport (brrsDyadicHalfWaveSymbol (d := d) Φ j t) := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : BRRSSpace d) (4 * (brrsFrequencyScale j)⁻¹))
  intro xi hxi
  have hnorm : 4 * (brrsFrequencyScale j)⁻¹ ≤ ‖xi‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hxi
    exact le_of_not_ge hxi
  rw [brrsDyadicHalfWaveSymbol,
    brrsDyadicMultiplier_eq_zero_of_le_norm Φ j xi hnorm, mul_zero]

/-- The literal annular half-wave symbol packaged as a Schwartz multiplier. -/
noncomputable def brrsDyadicHalfWaveSchwartzSymbol {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) : BRRSSchwartz d :=
  (hasCompactSupport_brrsDyadicHalfWaveSymbol Φ j t).toSchwartzMap
    (contDiff_brrsDyadicHalfWaveSymbol Φ j t)

/-- Evaluation of the packaged literal annular half-wave symbol. -/
theorem brrsDyadicHalfWaveSchwartzSymbol_apply {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) (xi : BRRSSpace d) :
    brrsDyadicHalfWaveSchwartzSymbol Φ j t xi =
      brrsDyadicHalfWaveSymbol Φ j t xi :=
  rfl

/-- On Schwartz inputs, the literal BRRS annular half-wave is convolution by
the inverse Fourier transform of its compact smooth frequency symbol.  This
is the concrete core from which an `L^p` realization must be extended. -/
theorem brrsDyadicHalfWave_eq_convolution {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) (f : BRRSSchwartz d)
    (x : BRRSSpace d) :
    brrsDyadicHalfWave Φ j t f x =
      (((𝓕⁻ (brrsDyadicHalfWaveSchwartzSymbol Φ j t) : BRRSSchwartz d) :
          BRRSSpace d → Complex)
        ⋆[ContinuousLinearMap.mul Complex Complex, volume]
          (f : BRRSSpace d → Complex)) x := by
  unfold brrsDyadicHalfWave
  have hsymbol : (fun xi : BRRSSpace d =>
      halfWaveMultiplier t xi * brrsDyadicMultiplier Φ j xi *
        𝓕 (f : BRRSSpace d → Complex) xi) =
      fun xi : BRRSSpace d =>
        brrsDyadicHalfWaveSchwartzSymbol Φ j t xi *
          𝓕 (f : BRRSSpace d → Complex) xi := by
    funext xi
    rw [brrsDyadicHalfWaveSchwartzSymbol_apply,
      brrsDyadicHalfWaveSymbol]
  rw [hsymbol]
  exact Auto.Spherical.Auxiliary.fourierInv_schwartz_multiplier_eq_convolution
    (brrsDyadicHalfWaveSchwartzSymbol Φ j t) f x

/-- If the frequency-side datum propagated by the literal annular BRRS
half-wave is radial, then its inverse Fourier transform has the exact polar
surface-Fourier representation.  This is the Fourier-analytic starting point
for the radial kernel calculation; it deliberately asserts no stationary-phase
decay. -/
theorem brrsDyadicHalfWave_eq_surfaceFourier_integral_of_radialProfile
    {d : Nat} (hd : 0 < d) (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real)
    (f : BRRSSchwartz d) (F : Real → Complex)
    (hprofile : ∀ xi : BRRSSpace d,
      brrsDyadicHalfWaveSymbol Φ j t xi *
        𝓕 (f : BRRSSpace d → Complex) xi = F ‖xi‖)
    (x : BRRSSpace d) :
    brrsDyadicHalfWave Φ j t f x =
      ∫ rho : Ioi (0 : Real),
        surfaceFourier d (-rho.1 • x) * F rho.1
          ∂Measure.volumeIoiPow (d - 1) := by
  let g : BRRSSchwartz d := SchwartzMap.smulLeftCLM Complex
    (brrsDyadicHalfWaveSchwartzSymbol Φ j t : BRRSSpace d → Complex) (𝓕 f)
  have hg : (g : BRRSSpace d → Complex) = fun xi : BRRSSpace d => F ‖xi‖ := by
    funext xi
    simp only [g, SchwartzMap.smulLeftCLM_apply
      (brrsDyadicHalfWaveSchwartzSymbol Φ j t).hasTemperateGrowth,
      smul_eq_mul, brrsDyadicHalfWaveSchwartzSymbol_apply,
      SchwartzMap.fourier_coe]
    exact hprofile xi
  have hint :=
    Auto.RadialFourierTransform.integrable_polar_fourierChar_mul_of_schwartz_radial
      g F (by
        intro xi
        rw [hg]) x
  have hpolar :=
    Auto.Spherical.SurfaceMeasureDecay.fourierInv_radial_eq_surfaceFourier_integral hd F x hint
  change 𝓕⁻ (fun xi : BRRSSpace d =>
    brrsDyadicHalfWaveSymbol Φ j t xi * 𝓕 (f : BRRSSchwartz d) xi) x = _
  rw [show (fun xi : BRRSSpace d =>
      brrsDyadicHalfWaveSymbol Φ j t xi * 𝓕 (f : BRRSSchwartz d) xi) =
      fun xi => F ‖xi‖ by
        funext xi
        exact hprofile xi]
  exact hpolar

/-- The radial Fourier-side profile propagated by the literal BRRS half-wave,
evaluated on an arbitrary unit frequency ray.  For a radial input the choice
of the ray is immaterial; retaining it as data avoids introducing a
noncanonical coordinate direction. -/
def brrsDyadicHalfWaveRadialFourierProfile {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) (f : BRRSSchwartz d)
    (v : BRRSSpace d) (rho : Real) : Complex :=
  brrsDyadicHalfWaveSymbol Φ j t (rho • v) *
    𝓕 (f : BRRSSpace d → Complex) (rho • v)

/-- Exact polar representation of the literal annular half-wave on a radial
Schwartz input.  This is the radial-output bridge for the later `TT*` kernel:
the only frequency datum left in the integral is the one-dimensional radial
Fourier profile above, and the angular factor is the actual `surfaceFourier`.
No stationary-phase estimate is used here. -/
theorem brrsDyadicHalfWave_eq_surfaceFourier_integral_of_isRadial
    {d : Nat} (hd : 0 < d) (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real)
    (f : BRRSSchwartz d) (hf : IsRadial (f : BRRSSpace d → Complex))
    (v : BRRSSpace d) (hv : ‖v‖ = 1) (x : BRRSSpace d) :
    brrsDyadicHalfWave Φ j t f x =
      ∫ rho : Ioi (0 : Real),
        surfaceFourier d (-rho.1 • x) *
          brrsDyadicHalfWaveRadialFourierProfile Φ j t f v rho.1
          ∂Measure.volumeIoiPow (d - 1) := by
  apply brrsDyadicHalfWave_eq_surfaceFourier_integral_of_radialProfile hd Φ j t f
    (brrsDyadicHalfWaveRadialFourierProfile Φ j t f v)
  intro xi
  have hnorm : ‖xi‖ = ‖‖xi‖ • v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hv, mul_one]
  have hsymbol : brrsDyadicHalfWaveSymbol Φ j t xi =
      brrsDyadicHalfWaveSymbol Φ j t (‖xi‖ • v) := by
    unfold brrsDyadicHalfWaveSymbol
    rw [halfWaveMultiplier_isRadial t xi (‖xi‖ • v) hnorm,
      brrsDyadicMultiplier_isRadial Φ j xi (‖xi‖ • v) hnorm]
  have hfourier : IsRadial (𝓕 (f : BRRSSpace d → Complex)) :=
    ((hf.orthogonallyInvariant).fourier).isRadial
  rw [brrsDyadicHalfWaveRadialFourierProfile, hsymbol,
    hfourier xi (‖xi‖ • v) hnorm]

/-- The physical-space Schwartz kernel of the frequency-localized BRRS
half-wave. -/
noncomputable def brrsDyadicHalfWaveKernel {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) : BRRSSchwartz d :=
  𝓕⁻ (brrsDyadicHalfWaveSchwartzSymbol Φ j t)

/-- The Fourier formula is convolution by the named physical kernel. -/
theorem brrsDyadicHalfWave_eq_kernel_convolution {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) (f : BRRSSchwartz d)
    (x : BRRSSpace d) :
    brrsDyadicHalfWave Φ j t f x =
      (((brrsDyadicHalfWaveKernel Φ j t : BRRSSchwartz d) :
          BRRSSpace d → Complex)
        ⋆[ContinuousLinearMap.mul Complex Complex, volume]
          (f : BRRSSpace d → Complex)) x := by
  simpa only [brrsDyadicHalfWaveKernel] using
    brrsDyadicHalfWave_eq_convolution Φ j t f x

/-! ### Exact annular half-wave `TT*` kernel

The radial local-smoothing argument uses the pair operator
`e^{it\sqrt{-\Delta}}P_j (e^{is\sqrt{-\Delta}}P_j)^*`.  This subsection
records its literal Schwartz-core realization before any kernel estimate is
made.  In particular, the time dependence is exactly the relative phase
`t - s`, and the cutoff is `Φ * conj Φ`; no reality condition on `Φ` is
silently imposed.
-/

/-- The Schwartz multiplier of the formal adjoint of one annular half-wave
piece. -/
noncomputable def brrsDyadicHalfWaveSchwartzAdjointSymbol {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s : Real) : BRRSSchwartz d :=
  Auto.MikhlinHormander.conjugateSchwartz
    (brrsDyadicHalfWaveSchwartzSymbol Φ j s)

/-- Pointwise form of the formal adjoint multiplier. -/
theorem brrsDyadicHalfWaveSchwartzAdjointSymbol_apply {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s : Real) (xi : BRRSSpace d) :
    brrsDyadicHalfWaveSchwartzAdjointSymbol Φ j s xi =
      starRingEnd Complex (brrsDyadicHalfWaveSymbol Φ j s xi) := by
  rw [brrsDyadicHalfWaveSchwartzAdjointSymbol,
    Auto.MikhlinHormander.conjugateSchwartz_apply,
    brrsDyadicHalfWaveSchwartzSymbol_apply]

/-- The compact Schwartz multiplier of the pair `T_t T_s^*`. -/
noncomputable def brrsDyadicHalfWaveTTStarSchwartzSymbol {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real) : BRRSSchwartz d :=
  Auto.MikhlinHormander.multiplySchwartz
    (brrsDyadicHalfWaveSchwartzSymbol Φ j t)
    (brrsDyadicHalfWaveSchwartzAdjointSymbol Φ j s)

/-- The `TT*` symbol is the product of the forward symbol and the conjugate
of the earlier-time symbol. -/
theorem brrsDyadicHalfWaveTTStarSchwartzSymbol_apply {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real) (xi : BRRSSpace d) :
    brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t xi =
      brrsDyadicHalfWaveSymbol Φ j t xi *
        starRingEnd Complex (brrsDyadicHalfWaveSymbol Φ j s xi) := by
  rw [brrsDyadicHalfWaveTTStarSchwartzSymbol,
    Auto.MikhlinHormander.multiplySchwartz_apply,
    brrsDyadicHalfWaveSchwartzSymbol_apply,
    brrsDyadicHalfWaveSchwartzAdjointSymbol_apply]

/-- Complex conjugation reverses the half-wave time. -/
theorem star_halfWaveMultiplier {d : Nat} (s : Real) (xi : BRRSSpace d) :
    starRingEnd Complex (halfWaveMultiplier (d := d) s xi) =
      halfWaveMultiplier (-s) xi := by
  unfold halfWaveMultiplier
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  congr 1
  ring

/-- The literal `TT*` multiplier has the relative half-wave phase and the
positive cutoff density `Φ * conj Φ`. -/
theorem brrsDyadicHalfWaveTTStarSchwartzSymbol_eq_relativePhase {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real) (xi : BRRSSpace d) :
    brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t xi =
      halfWaveMultiplier (t - s) xi * brrsDyadicMultiplier Φ j xi *
        starRingEnd Complex (brrsDyadicMultiplier Φ j xi) := by
  rw [brrsDyadicHalfWaveTTStarSchwartzSymbol_apply]
  change
    (halfWaveMultiplier t xi * brrsDyadicMultiplier Φ j xi) *
        starRingEnd Complex
          (halfWaveMultiplier s xi * brrsDyadicMultiplier Φ j xi) = _
  rw [map_mul, star_halfWaveMultiplier]
  have hphase : halfWaveMultiplier t xi * halfWaveMultiplier (-s) xi =
      halfWaveMultiplier (t - s) xi := by
    unfold halfWaveMultiplier
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    (halfWaveMultiplier t xi * brrsDyadicMultiplier Φ j xi) *
        (halfWaveMultiplier (-s) xi *
          starRingEnd Complex (brrsDyadicMultiplier Φ j xi)) =
        (halfWaveMultiplier t xi * halfWaveMultiplier (-s) xi) *
          brrsDyadicMultiplier Φ j xi *
            starRingEnd Complex (brrsDyadicMultiplier Φ j xi) := by ring
    _ = halfWaveMultiplier (t - s) xi * brrsDyadicMultiplier Φ j xi *
          starRingEnd Complex (brrsDyadicMultiplier Φ j xi) := by rw [hphase]

/-- The one-dimensional radial profile of the exact annular `TT*`
multiplier.  This definition is valid in every dimension; all dimension
dependence enters only through the polar measure and surface Fourier factor. -/
def brrsDyadicHalfWaveTTStarRadialProfile
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t rho : Real) : Complex :=
  Complex.exp (((2 * Real.pi * (t - s) * rho : Real) : Complex) * Complex.I) *
    Φ.symbol (brrsFrequencyScale j * rho) *
      starRingEnd Complex (Φ.symbol (brrsFrequencyScale j * rho))

/-- The pair multiplier is exactly the norm-radial profile above. -/
theorem brrsDyadicHalfWaveTTStarSchwartzSymbol_eq_radialProfile {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real) (xi : BRRSSpace d) :
    brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t xi =
      brrsDyadicHalfWaveTTStarRadialProfile Φ j s t ‖xi‖ := by
  rw [brrsDyadicHalfWaveTTStarSchwartzSymbol_eq_relativePhase]
  rfl

/-- The forward annular half-wave as a complex-linear map on the Schwartz
core. -/
noncomputable def brrsDyadicHalfWaveSchwartzPiece {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) :
    BRRSSchwartz d →ₗ[Complex] BRRSSchwartz d :=
  (SchwartzMap.fourierMultiplierCLM Complex
    (brrsDyadicHalfWaveSchwartzSymbol Φ j t : BRRSSpace d → Complex)).toLinearMap

/-- The bundled Schwartz operator has exactly the original literal BRRS
half-wave formula on every Schwartz input. -/
theorem brrsDyadicHalfWaveSchwartzPiece_apply_eq_halfWave {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) (f : BRRSSchwartz d)
    (x : BRRSSpace d) :
    brrsDyadicHalfWaveSchwartzPiece Φ j t f x =
      brrsDyadicHalfWave Φ j t f x := by
  let m : BRRSSchwartz d := brrsDyadicHalfWaveSchwartzSymbol Φ j t
  have hm : (m : BRRSSpace d → Complex).HasTemperateGrowth := m.hasTemperateGrowth
  change ((SchwartzMap.fourierMultiplierCLM Complex
    (m : BRRSSpace d → Complex) f : BRRSSchwartz d) : BRRSSpace d → Complex) x = _
  rw [SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe]
  have hsymbol :
      (SchwartzMap.smulLeftCLM Complex (m : BRRSSpace d → Complex)
        (𝓕 f) : BRRSSpace d → Complex) =
      fun xi : BRRSSpace d => brrsDyadicHalfWaveSchwartzSymbol Φ j t xi *
        𝓕 (f : BRRSSpace d → Complex) xi := by
    funext xi
    simp only [SchwartzMap.smulLeftCLM_apply hm, smul_eq_mul]
    rfl
  rw [hsymbol]
  unfold brrsDyadicHalfWave
  apply congrArg (fun g : BRRSSpace d → Complex => 𝓕⁻ g x)
  funext xi
  rw [brrsDyadicHalfWaveSchwartzSymbol_apply,
    brrsDyadicHalfWaveSymbol]

/-- The formal adjoint annular half-wave on the Schwartz core. -/
noncomputable def brrsDyadicHalfWaveSchwartzAdjointPiece {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s : Real) :
    BRRSSchwartz d →ₗ[Complex] BRRSSchwartz d :=
  (SchwartzMap.fourierMultiplierCLM Complex
    (brrsDyadicHalfWaveSchwartzAdjointSymbol Φ j s : BRRSSpace d → Complex)).toLinearMap

/-- The `TT*` pair multiplier as a complex-linear Schwartz operator. -/
noncomputable def brrsDyadicHalfWaveTTStarSchwartzPiece {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real) :
    BRRSSchwartz d →ₗ[Complex] BRRSSchwartz d :=
  (SchwartzMap.fourierMultiplierCLM Complex
    (brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t : BRRSSpace d → Complex)).toLinearMap

/-- The formal pair factorization is literal on Schwartz data:
`T_t T_s^*` is the multiplier with the product symbol. -/
theorem brrsDyadicHalfWaveSchwartzPiece_comp_adjoint_eq_ttstar {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real) (f : BRRSSchwartz d) :
    brrsDyadicHalfWaveSchwartzPiece Φ j t
      (brrsDyadicHalfWaveSchwartzAdjointPiece Φ j s f) =
        brrsDyadicHalfWaveTTStarSchwartzPiece Φ j s t f := by
  let mt : BRRSSpace d → Complex := brrsDyadicHalfWaveSchwartzSymbol Φ j t
  let ms : BRRSSpace d → Complex := brrsDyadicHalfWaveSchwartzAdjointSymbol Φ j s
  have hmt : mt.HasTemperateGrowth :=
    (brrsDyadicHalfWaveSchwartzSymbol Φ j t).hasTemperateGrowth
  have hms : ms.HasTemperateGrowth :=
    (brrsDyadicHalfWaveSchwartzAdjointSymbol Φ j s).hasTemperateGrowth
  change SchwartzMap.fourierMultiplierCLM Complex mt
      (SchwartzMap.fourierMultiplierCLM Complex ms f) =
        SchwartzMap.fourierMultiplierCLM Complex
          (brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t : BRRSSpace d → Complex) f
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply hmt hms]
  apply congrArg (fun m : BRRSSpace d → Complex =>
    SchwartzMap.fourierMultiplierCLM Complex m f)
  funext xi
  change mt xi * ms xi = _
  rw [show mt xi = brrsDyadicHalfWaveSchwartzSymbol Φ j t xi by rfl,
    show ms xi = brrsDyadicHalfWaveSchwartzAdjointSymbol Φ j s xi by rfl,
    brrsDyadicHalfWaveTTStarSchwartzSymbol_apply,
    brrsDyadicHalfWaveSchwartzSymbol_apply,
    brrsDyadicHalfWaveSchwartzAdjointSymbol_apply]

/-- The physical-space kernel of the exact annular `TT*` pair. -/
noncomputable def brrsDyadicHalfWaveTTStarKernel {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real) : BRRSSchwartz d :=
  𝓕⁻ (brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t)

/-- The pair operator is convolution by its explicitly named physical
kernel. -/
theorem brrsDyadicHalfWaveTTStarSchwartzPiece_eq_kernel_convolution {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real) (f : BRRSSchwartz d)
    (x : BRRSSpace d) :
    brrsDyadicHalfWaveTTStarSchwartzPiece Φ j s t f x =
      (((brrsDyadicHalfWaveTTStarKernel Φ j s t : BRRSSchwartz d) :
          BRRSSpace d → Complex)
        ⋆[ContinuousLinearMap.mul Complex Complex, volume]
          (f : BRRSSpace d → Complex)) x := by
  let m : BRRSSchwartz d := brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t
  have hm : (m : BRRSSpace d → Complex).HasTemperateGrowth := m.hasTemperateGrowth
  change ((SchwartzMap.fourierMultiplierCLM Complex
    (m : BRRSSpace d → Complex) f : BRRSSchwartz d) : BRRSSpace d → Complex) x = _
  rw [SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe]
  have hsymbol :
      (SchwartzMap.smulLeftCLM Complex (m : BRRSSpace d → Complex)
        (𝓕 f) : BRRSSpace d → Complex) =
      fun xi : BRRSSpace d => brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t xi *
        𝓕 (f : BRRSSpace d → Complex) xi := by
    funext xi
    simp only [SchwartzMap.smulLeftCLM_apply hm, smul_eq_mul]
    rfl
  rw [hsymbol]
  simpa only [brrsDyadicHalfWaveTTStarKernel] using
    (Auto.Spherical.Auxiliary.fourierInv_schwartz_multiplier_eq_convolution
      (brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t) f x)

/-- The two-variable physical kernel of the `TT*` pair.  Translation
invariance makes it a function of output minus source. -/
noncomputable def brrsDyadicHalfWaveTTStarSourceKernel {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real)
    (x y : BRRSSpace d) : Complex :=
  brrsDyadicHalfWaveTTStarKernel Φ j s t (x - y)

/-- The exact source-kernel representation of `T_t T_s^*` on the Schwartz
core. -/
theorem brrsDyadicHalfWaveTTStarSchwartzPiece_eq_sourceKernel {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real) (f : BRRSSchwartz d)
    (x : BRRSSpace d) :
    brrsDyadicHalfWaveTTStarSchwartzPiece Φ j s t f x =
      ∫ y : BRRSSpace d,
        brrsDyadicHalfWaveTTStarSourceKernel Φ j s t x y * f y := by
  rw [brrsDyadicHalfWaveTTStarSchwartzPiece_eq_kernel_convolution,
    convolution_mul_swap]
  rfl

/-- Polar representation of the exact annular `TT*` kernel.  This is the
radial Fourier identity to which the later Bessel/stationary-phase argument
must be applied; it makes no decay or lower-bound assertion. -/
theorem brrsDyadicHalfWaveTTStarKernel_eq_surfaceFourier_integral
    {d : Nat} (hd : 0 < d) (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real)
    (x : BRRSSpace d) :
    (brrsDyadicHalfWaveTTStarKernel Φ j s t : BRRSSpace d → Complex) x =
      ∫ rho : Ioi (0 : Real),
        surfaceFourier d (-rho.1 • x) *
          brrsDyadicHalfWaveTTStarRadialProfile Φ j s t rho.1
            ∂Measure.volumeIoiPow (d - 1) := by
  have hrad : ∀ xi : BRRSSpace d,
      brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t xi =
        brrsDyadicHalfWaveTTStarRadialProfile Φ j s t ‖xi‖ := by
    intro xi
    exact brrsDyadicHalfWaveTTStarSchwartzSymbol_eq_radialProfile Φ j s t xi
  have hint := Auto.RadialFourierTransform.integrable_polar_fourierChar_mul_of_schwartz_radial
    (brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t)
    (brrsDyadicHalfWaveTTStarRadialProfile Φ j s t) hrad x
  unfold brrsDyadicHalfWaveTTStarKernel
  rw [SchwartzMap.fourierInv_coe]
  change 𝓕⁻ (brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t :
    BRRSSpace d → Complex) x = _
  rw [show (brrsDyadicHalfWaveTTStarSchwartzSymbol Φ j s t :
      BRRSSpace d → Complex) = fun xi =>
        brrsDyadicHalfWaveTTStarRadialProfile Φ j s t ‖xi‖ by
      funext xi
      exact hrad xi]
  exact fourierInv_radial_eq_surfaceFourier_integral hd
    (brrsDyadicHalfWaveTTStarRadialProfile Φ j s t) x hint

/-- The two-variable `TT*` source kernel has the same polar radial formula,
evaluated at the output-source difference. -/
theorem brrsDyadicHalfWaveTTStarSourceKernel_eq_surfaceFourier_integral
    {d : Nat} (hd : 0 < d) (Φ : BRRSAnnularCutoff) (j : Nat) (s t : Real)
    (x y : BRRSSpace d) :
    brrsDyadicHalfWaveTTStarSourceKernel Φ j s t x y =
      ∫ rho : Ioi (0 : Real),
        surfaceFourier d (-rho.1 • (x - y)) *
          brrsDyadicHalfWaveTTStarRadialProfile Φ j s t rho.1
            ∂Measure.volumeIoiPow (d - 1) := by
  exact brrsDyadicHalfWaveTTStarKernel_eq_surfaceFourier_integral
    hd Φ j s t (x - y)

/-! ### Stationary surface-wave normal forms

The auxiliary fractal-dilations development contains a literal meridian
stationary-phase calculation: the Fourier transform of spherical measure is
an outgoing wave, an incoming wave, and a rapidly decaying middle term.  The
following small BRRS-facing interface records that calculation in precisely
the radial form used by the half-wave and `TT*` kernels above.  These are
equalities for the actual `surfaceFourier` factor; no symbol-class surrogate
is introduced here.
-/

open Auto.Spherical.FractalDilations.Auxiliary

/-- The three pieces of the stationary decomposition of a nonplanar sphere
surface Fourier factor. -/
inductive BRRSSurfaceWavePart where
  | outgoing
  | incoming
  | middle
  deriving DecidableEq

/-- The extracted linear radial phase of a stationary surface-wave piece. -/
def brrsSurfaceWavePhase (part : BRRSSurfaceWavePart) (a : Real) : Real :=
  match part with
  | .outgoing => -(2 * Real.pi * a)
  | .incoming => 2 * Real.pi * a
  | .middle => 0

/-- The radial coefficient after its outgoing or incoming carrier has been
extracted.  For the middle term no carrier is extracted, and its rapid decay
is supplied by the proved meridian integration-by-parts estimates in
`FractalDilations.Auxiliary`. -/
def brrsSurfaceWaveAmplitude
    (d : Nat) (part : BRRSSurfaceWavePart) (a rho : Real) : Complex :=
  (surfaceMass (d - 1) : Complex) *
    match part with
    | .outgoing => smoothEndpointQuadraticIntegral (d - 2) ((2 * Real.pi * a) * rho)
    | .incoming => smoothEndpointQuadraticIntegral (d - 2) ((-(2 * Real.pi * a)) * rho)
    | .middle => coordinateMiddleMeridianLocalizedIntegral (d - 2)
        ((2 * Real.pi * a) * rho)

/-- One concrete stationary surface-wave term on a radial frequency ray. -/
def brrsSurfaceWaveTerm
    (d : Nat) (part : BRRSSurfaceWavePart) (a rho : Real) : Complex :=
  brrsSurfaceWaveAmplitude d part a rho *
    Complex.exp (((brrsSurfaceWavePhase part a * rho : Real) : Complex) * Complex.I)

/-- The exact three-wave form of the nonplanar spherical Fourier factor at a
nonnegative scalar frequency. -/
def brrsSurfaceWaveSum (d : Nat) (u : Real) : Complex :=
  (surfaceMass (d - 1) : Complex) *
    (Complex.exp (((-(2 * Real.pi * u) : Real) : Complex) * Complex.I) *
        smoothEndpointQuadraticIntegral (d - 2) (2 * Real.pi * u) +
      Complex.exp (((2 * Real.pi * u : Real) : Complex) * Complex.I) *
        smoothEndpointQuadraticIntegral (d - 2) (-(2 * Real.pi * u)) +
      coordinateMiddleMeridianLocalizedIntegral (d - 2) (2 * Real.pi * u))

/-- The stationary wave sum exposes the outgoing, incoming, and middle
pieces with their literal linear radial phases. -/
theorem brrsSurfaceWaveSum_eq_three_terms
    (d : Nat) (a rho : Real) :
    brrsSurfaceWaveSum d (a * rho) =
      brrsSurfaceWaveTerm d .outgoing a rho +
        brrsSurfaceWaveTerm d .incoming a rho +
          brrsSurfaceWaveTerm d .middle a rho := by
  unfold brrsSurfaceWaveSum brrsSurfaceWaveTerm brrsSurfaceWaveAmplitude
    brrsSurfaceWavePhase
  have hphaseOut : -(2 * Real.pi * (a * rho)) = (-(2 * Real.pi * a)) * rho := by
    ring
  have hphaseIn : 2 * Real.pi * (a * rho) = (2 * Real.pi * a) * rho := by
    ring
  simp
  rw [hphaseOut, hphaseIn]
  ring

/-- The all-dimensional stationary-phase calculation, expressed directly in
the ambient dimension required by BRRS. -/
theorem brrs_surfaceFourier_eq_stationaryWaveSum
    {d : Nat} (hd : 3 <= d) (xi : BRRSSpace d) :
    surfaceFourier d xi = brrsSurfaceWaveSum d ‖xi‖ := by
  have hd' : 2 <= d - 1 := by omega
  have hdim : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  have hsurface :=
    surfaceFourier_succ_eq_coordinateSmoothWaves (d := d - 1) hd'
  rw [hdim] at hsurface
  simpa only [Nat.sub_sub, Nat.reduceAdd, brrsSurfaceWaveSum] using hsurface xi

/-- The surface factor in the exact polar BRRS kernel has the three-wave
form on every positive radial ray. -/
theorem brrs_surfaceFourier_neg_smul_eq_three_terms
    {d : Nat} (hd : 3 <= d) {rho : Real} (hrho : 0 < rho)
    (x : BRRSSpace d) :
    surfaceFourier d (-rho • x) =
      brrsSurfaceWaveTerm d .outgoing ‖x‖ rho +
        brrsSurfaceWaveTerm d .incoming ‖x‖ rho +
          brrsSurfaceWaveTerm d .middle ‖x‖ rho := by
  rw [brrs_surfaceFourier_eq_stationaryWaveSum hd]
  have hnorm : ‖-rho • x‖ = rho * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hrho]
  rw [hnorm]
  simpa only [mul_comm] using brrsSurfaceWaveSum_eq_three_terms d ‖x‖ rho

/-- The exact stationary wave sum for the planar circle.  The endpoint
symbol is distinct in dimension two, because the meridian density has
vanishing order zero. -/
def brrsPlanarSurfaceWaveSum (u : Real) : Complex :=
  (surfaceMass 1 : Complex) *
    (Complex.exp (((-(2 * Real.pi * u) : Real) : Complex) * Complex.I) *
        planarEndpointQuadraticIntegral (2 * Real.pi * u) +
      Complex.exp (((2 * Real.pi * u : Real) : Complex) * Complex.I) *
        planarEndpointQuadraticIntegral (-(2 * Real.pi * u)) +
      coordinateMiddleMeridianLocalizedIntegral 0 (2 * Real.pi * u))

/-- The planar companion of the nonplanar stationary surface-wave identity. -/
theorem brrs_surfaceFourier_two_eq_stationaryWaveSum (xi : BRRSSpace 2) :
    surfaceFourier 2 xi = brrsPlanarSurfaceWaveSum ‖xi‖ := by
  simpa only [brrsPlanarSurfaceWaveSum] using
    surfaceFourier_two_eq_coordinatePlanarSmoothWaves xi

/-! ### Dimension-generic finite-`Lᵖ` Young inequality

The half-wave multiplier has a Schwartz physical kernel.  The elementary
Young estimate below is deliberately stated on arbitrary Euclidean dimension
and arbitrary measurable complex functions, so it can serve both the
Schwartz Fourier formula above and an eventual `Lᵖ` realization of that
formula.  The proof is kept here rather than imported from the planar
Roos--Seeger development, whose corresponding result is specialized to
`Euclidean 2` and private to that component. -/

/-- Hölder factorization of a product against a positive weight. -/
theorem brrs_ennreal_weighted_factor_of_holder
    {p r : Real} (hpq : r.HolderConjugate p) (a b : ENNReal) :
    a * b = a ^ r⁻¹ * (a * b ^ p) ^ p⁻¹ := by
  have hp0 : 0 < p := hpq.symm.pos
  have hbinv : (b ^ p) ^ p⁻¹ = b := by
    calc
      (b ^ p) ^ p⁻¹ = b ^ (p * p⁻¹) := (ENNReal.rpow_mul _ _ _).symm
      _ = b := by rw [mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.inv_nonneg]
  rw [hbinv]
  calc
    a * b = a ^ (r⁻¹ + p⁻¹) * b := by rw [hpq.inv_add_inv_eq_one, ENNReal.rpow_one]
    _ = (a ^ r⁻¹ * a ^ p⁻¹) * b := by
      rw [ENNReal.rpow_add_of_nonneg _ _ hpq.inv_nonneg hpq.symm.inv_nonneg]
    _ = a ^ r⁻¹ * (a ^ p⁻¹ * b) := by ring

/-- The pointwise Hölder step in Young's inequality, valid in every
Euclidean dimension. -/
theorem brrs_lintegral_spatial_p_pointwise {d : Nat}
    (p r : Real) (hpq : r.HolderConjugate p) (K q : BRRSSpace d → ENNReal)
    (hK : Measurable K) (hq : Measurable q) (x : BRRSSpace d) :
    (∫⁻ y : BRRSSpace d, K y * q (x - y)) ^ p ≤
      (∫⁻ y : BRRSSpace d, K y) ^ (p - 1) *
        ∫⁻ y : BRRSSpace d, K y * q (x - y) ^ p := by
  have hp0 : 0 < p := hpq.symm.pos
  have hr0 : 0 < r := hpq.pos
  let a : BRRSSpace d → ENNReal := fun y => K y ^ r⁻¹
  let b : BRRSSpace d → ENNReal := fun y =>
    (K y * q (x - y) ^ p) ^ p⁻¹
  have ha : AEMeasurable a volume := (hK.pow measurable_const).aemeasurable
  have hqx : Measurable (fun y : BRRSSpace d => q (x - y)) :=
    hq.comp (measurable_const.sub measurable_id)
  have hb : AEMeasurable b volume :=
    ((hK.mul (hqx.pow measurable_const)).pow measurable_const).aemeasurable
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq ha hb
  have hleft : (∫⁻ y : BRRSSpace d, (a * b) y) =
      ∫⁻ y : BRRSSpace d, K y * q (x - y) := by
    apply lintegral_congr
    intro y
    simp only [a, b, Pi.mul_apply]
    exact (brrs_ennreal_weighted_factor_of_holder hpq (K y) (q (x - y))).symm
  have hfirst : (∫⁻ y : BRRSSpace d, a y ^ r) = ∫⁻ y : BRRSSpace d, K y := by
    apply lintegral_congr
    intro y
    simp only [a]
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one]
  have hsecond : (∫⁻ y : BRRSSpace d, b y ^ p) =
      ∫⁻ y : BRRSSpace d, K y * q (x - y) ^ p := by
    apply lintegral_congr
    intro y
    simp only [b]
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  have hholder2 :
      (∫⁻ y : BRRSSpace d, K y * q (x - y)) ≤
        (∫⁻ y : BRRSSpace d, K y) ^ r⁻¹ *
          (∫⁻ y : BRRSSpace d, K y * q (x - y) ^ p) ^ p⁻¹ := by
    rw [hleft, hfirst, hsecond] at hholder
    simpa only [one_div] using hholder
  have hrp : r⁻¹ * p = p - 1 := by
    rw [← hpq.symm.one_sub_inv]
    field_simp [hp0.ne']
  have hpow := ENNReal.rpow_le_rpow hholder2 hp0.le
  calc
    (∫⁻ y : BRRSSpace d, K y * q (x - y)) ^ p ≤
        ((∫⁻ y : BRRSSpace d, K y) ^ r⁻¹ *
          (∫⁻ y : BRRSSpace d, K y * q (x - y) ^ p) ^ p⁻¹) ^ p := hpow
    _ = (∫⁻ y : BRRSSpace d, K y) ^ (p - 1) *
        ∫⁻ y : BRRSSpace d, K y * q (x - y) ^ p := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hrp,
        inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]

/-- Young's inequality for the `p`-moment of convolution with a positive
kernel on Euclidean space. -/
theorem brrs_lintegral_spatial_p_young {d : Nat}
    (p r : Real) (hpq : r.HolderConjugate p) (K q : BRRSSpace d → ENNReal)
    (hK : Measurable K) (hq : Measurable q) :
    ∫⁻ x : BRRSSpace d, (∫⁻ y : BRRSSpace d, K y * q (x - y)) ^ p ≤
      (∫⁻ y : BRRSSpace d, K y) ^ p * ∫⁻ x : BRRSSpace d, q x ^ p := by
  have hp0 : 0 < p := hpq.symm.pos
  have hpone : 1 ≤ p := hpq.symm.lt.le
  let H : BRRSSpace d × BRRSSpace d → ENNReal := fun z =>
    K z.2 * q (z.1 - z.2) ^ p
  have hH : Measurable H :=
    (hK.comp measurable_snd).mul
      ((hq.comp (measurable_fst.sub measurable_snd)).pow measurable_const)
  have hinner : Measurable (fun x : BRRSSpace d =>
      ∫⁻ y : BRRSSpace d, K y * q (x - y) ^ p) :=
    hH.lintegral_prod_right
  have htranslate (y : BRRSSpace d) :
      (∫⁻ x : BRRSSpace d, q (x - y) ^ p) = ∫⁻ x : BRRSSpace d, q x ^ p :=
    (measurePreserving_sub_right (volume : Measure (BRRSSpace d)) y).lintegral_comp
      (hq.pow measurable_const)
  have hdouble :
      (∫⁻ x : BRRSSpace d, ∫⁻ y : BRRSSpace d, K y * q (x - y) ^ p) =
        (∫⁻ y : BRRSSpace d, K y) * ∫⁻ x : BRRSSpace d, q x ^ p := by
    calc
      (∫⁻ x : BRRSSpace d, ∫⁻ y : BRRSSpace d, K y * q (x - y) ^ p) =
          ∫⁻ y : BRRSSpace d, ∫⁻ x : BRRSSpace d, K y * q (x - y) ^ p :=
        lintegral_lintegral_swap hH.aemeasurable
      _ = ∫⁻ y : BRRSSpace d, K y * (∫⁻ x : BRRSSpace d, q (x - y) ^ p) := by
        apply lintegral_congr
        intro y
        simpa only [Function.comp_apply, Pi.sub_apply, id_eq] using
          (lintegral_const_mul (K y)
            ((hq.comp (measurable_id.sub measurable_const)).pow measurable_const))
      _ = ∫⁻ y : BRRSSpace d, K y * (∫⁻ x : BRRSSpace d, q x ^ p) := by
        apply lintegral_congr
        intro y
        rw [htranslate y]
      _ = (∫⁻ y : BRRSSpace d, K y) * ∫⁻ x : BRRSSpace d, q x ^ p :=
        lintegral_mul_const _ hK
  calc
    (∫⁻ x : BRRSSpace d, (∫⁻ y : BRRSSpace d, K y * q (x - y)) ^ p) ≤
        ∫⁻ x : BRRSSpace d, (∫⁻ y : BRRSSpace d, K y) ^ (p - 1) *
          (∫⁻ y : BRRSSpace d, K y * q (x - y) ^ p) := by
      apply lintegral_mono
      intro x
      exact brrs_lintegral_spatial_p_pointwise p r hpq K q hK hq x
    _ = (∫⁻ y : BRRSSpace d, K y) ^ (p - 1) *
        (∫⁻ x : BRRSSpace d, ∫⁻ y : BRRSSpace d, K y * q (x - y) ^ p) := by
      rw [lintegral_const_mul _ hinner]
    _ = (∫⁻ y : BRRSSpace d, K y) ^ (p - 1) *
        ((∫⁻ y : BRRSSpace d, K y) * ∫⁻ x : BRRSSpace d, q x ^ p) := by rw [hdouble]
    _ = (∫⁻ y : BRRSSpace d, K y) ^ p * ∫⁻ x : BRRSSpace d, q x ^ p := by
      calc
        (∫⁻ y : BRRSSpace d, K y) ^ (p - 1) *
            ((∫⁻ y : BRRSSpace d, K y) * ∫⁻ x : BRRSSpace d, q x ^ p) =
            ((∫⁻ y : BRRSSpace d, K y) ^ (p - 1) *
              (∫⁻ y : BRRSSpace d, K y) ^ (1 : Real)) *
              ∫⁻ x : BRRSSpace d, q x ^ p := by
          rw [ENNReal.rpow_one]; ring
        _ = (∫⁻ y : BRRSSpace d, K y) ^ ((p - 1) + 1) *
              ∫⁻ x : BRRSSpace d, q x ^ p := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hpone)
            (by norm_num : (0 : Real) ≤ 1)]
        _ = (∫⁻ y : BRRSSpace d, K y) ^ p * ∫⁻ x : BRRSSpace d, q x ^ p := by
          congr 2
          ring

/-- The dimension-generic finite-`Lᵖ` Young inequality for a convolution
with an `L¹` kernel.  No radiality or Fourier-specific hypothesis is used. -/
theorem brrs_eLpNorm_convolution_le {d : Nat}
    (p : Real) (hp : 1 < p) (K f : BRRSSpace d → Complex)
    (hK : Measurable K) (hf : Measurable f) :
    eLpNorm (K ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) (ENNReal.ofReal p) volume ≤
      (∫⁻ y : BRRSSpace d, ‖K y‖ₑ) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.conjExponent.HolderConjugate p :=
    (Real.HolderConjugate.conjExponent hp).symm
  have hpoint (x : BRRSSpace d) :
      ‖(K ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) x‖ₑ ≤
        ∫⁻ y : BRRSSpace d, ‖K y‖ₑ * ‖f (x - y)‖ₑ := by
    change ‖∫ y : BRRSSpace d, K y * f (x - y)‖ₑ ≤ _
    calc
      ‖∫ y : BRRSSpace d, K y * f (x - y)‖ₑ ≤ ∫⁻ y : BRRSSpace d, ‖K y * f (x - y)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y : BRRSSpace d, ‖K y‖ₑ * ‖f (x - y)‖ₑ := by
        apply lintegral_congr
        intro y
        rw [enorm_mul]
  have hmoment :
      (∫⁻ x : BRRSSpace d,
          ‖(K ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) x‖ₑ ^ p) ≤
        (∫⁻ y : BRRSSpace d, ‖K y‖ₑ) ^ p *
          ∫⁻ x : BRRSSpace d, ‖f x‖ₑ ^ p := by
    calc
      (∫⁻ x : BRRSSpace d,
          ‖(K ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) x‖ₑ ^ p) ≤
          ∫⁻ x : BRRSSpace d,
            (∫⁻ y : BRRSSpace d, ‖K y‖ₑ * ‖f (x - y)‖ₑ) ^ p := by
        apply lintegral_mono
        intro x
        exact ENNReal.rpow_le_rpow (hpoint x) (by positivity)
      _ ≤ (∫⁻ y : BRRSSpace d, ‖K y‖ₑ) ^ p *
          ∫⁻ x : BRRSSpace d, ‖f x‖ₑ ^ p :=
        brrs_lintegral_spatial_p_young p p.conjExponent hpq
          (fun y => ‖K y‖ₑ) (fun x => ‖f x‖ₑ) hK.enorm hf.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp0.le, one_div]
  have hstep := ENNReal.rpow_le_rpow hmoment (by positivity : (0 : Real) ≤ p⁻¹)
  calc
    (∫⁻ x : BRRSSpace d,
        ‖(K ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) x‖ₑ ^ p) ^ p⁻¹ ≤
        ((∫⁻ y : BRRSSpace d, ‖K y‖ₑ) ^ p *
          ∫⁻ x : BRRSSpace d, ‖f x‖ₑ ^ p) ^ p⁻¹ := hstep
    _ = (∫⁻ y : BRRSSpace d, ‖K y‖ₑ) *
        (∫⁻ x : BRRSSpace d, ‖f x‖ₑ ^ p) ^ p⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : Real) ≤ p⁻¹)]
      congr 1
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]

/-- Tonelli's formula for the positive convolution at the `L¹` endpoint. -/
theorem brrs_lintegral_spatial_one_young {d : Nat}
    (K q : BRRSSpace d → ENNReal) (hK : Measurable K) (hq : Measurable q) :
    (∫⁻ x : BRRSSpace d, ∫⁻ y : BRRSSpace d, K y * q (x - y)) =
      (∫⁻ y : BRRSSpace d, K y) * ∫⁻ x : BRRSSpace d, q x := by
  let H : BRRSSpace d × BRRSSpace d → ENNReal := fun z =>
    K z.2 * q (z.1 - z.2)
  have hH : Measurable H :=
    (hK.comp measurable_snd).mul
      (hq.comp (measurable_fst.sub measurable_snd))
  have htranslate (y : BRRSSpace d) :
      (∫⁻ x : BRRSSpace d, q (x - y)) = ∫⁻ x : BRRSSpace d, q x :=
    (measurePreserving_sub_right (volume : Measure (BRRSSpace d)) y).lintegral_comp hq
  calc
    (∫⁻ x : BRRSSpace d, ∫⁻ y : BRRSSpace d, K y * q (x - y)) =
        ∫⁻ y : BRRSSpace d, ∫⁻ x : BRRSSpace d, K y * q (x - y) :=
      lintegral_lintegral_swap hH.aemeasurable
    _ = ∫⁻ y : BRRSSpace d, K y * (∫⁻ x : BRRSSpace d, q (x - y)) := by
      apply lintegral_congr
      intro y
      simpa only [Function.comp_apply, Pi.sub_apply, id_eq] using
        (lintegral_const_mul (K y) (hq.comp (measurable_id.sub measurable_const)))
    _ = ∫⁻ y : BRRSSpace d, K y * (∫⁻ x : BRRSSpace d, q x) := by
      apply lintegral_congr
      intro y
      rw [htranslate y]
    _ = (∫⁻ y : BRRSSpace d, K y) * ∫⁻ x : BRRSSpace d, q x :=
      lintegral_mul_const _ hK

/-- The `L¹` endpoint of the dimension-generic Young inequality. -/
theorem brrs_eLpNorm_convolution_one_le {d : Nat}
    (K f : BRRSSpace d → Complex) (hK : Measurable K) (hf : Measurable f) :
    eLpNorm (K ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) 1 volume ≤
      (∫⁻ y : BRRSSpace d, ‖K y‖ₑ) * eLpNorm f 1 volume := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hpoint (x : BRRSSpace d) :
      ‖(K ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) x‖ₑ ≤
        ∫⁻ y : BRRSSpace d, ‖K y‖ₑ * ‖f (x - y)‖ₑ := by
    change ‖∫ y : BRRSSpace d, K y * f (x - y)‖ₑ ≤ _
    calc
      ‖∫ y : BRRSSpace d, K y * f (x - y)‖ₑ ≤ ∫⁻ y : BRRSSpace d, ‖K y * f (x - y)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y : BRRSSpace d, ‖K y‖ₑ * ‖f (x - y)‖ₑ := by
        apply lintegral_congr
        intro y
        rw [enorm_mul]
  calc
    (∫⁻ x : BRRSSpace d,
        ‖(K ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) x‖ₑ) ≤
        ∫⁻ x : BRRSSpace d,
          ∫⁻ y : BRRSSpace d, ‖K y‖ₑ * ‖f (x - y)‖ₑ := by
      apply lintegral_mono
      intro x
      exact hpoint x
    _ = (∫⁻ y : BRRSSpace d, ‖K y‖ₑ) * ∫⁻ x : BRRSSpace d, ‖f x‖ₑ :=
      brrs_lintegral_spatial_one_young (fun y => ‖K y‖ₑ) (fun x => ‖f x‖ₑ)
        hK.enorm hf.enorm

/-- A Schwartz kernel paired with an `Lᵖ` input has a defined convolution
integral at every spatial point.  The endpoint `p = 1` is included: its
Hölder conjugate is `∞`, and Schwartz kernels lie in every such space. -/
theorem brrs_convolutionExistsAt_of_memLp {d : Nat}
    (K : BRRSSchwartz d) (p : Real) (hp : 1 ≤ p)
    {f : BRRSSpace d → Complex} (hf : MemLp f (ENNReal.ofReal p) volume)
    (x : BRRSSpace d) :
    ConvolutionExistsAt (K : BRRSSpace d → Complex) f x
      (ContinuousLinearMap.mul Complex Complex) volume := by
  have hP : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨hP⟩
  letI : (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal p).conjExponent :=
    ENNReal.HolderConjugate.conjExponent hP
  have hK : MemLp (K : BRRSSpace d → Complex)
      (ENNReal.ofReal p).conjExponent volume :=
    K.memLp _ volume
  have hfshift : MemLp (fun y : BRRSSpace d => f (x - y))
      (ENNReal.ofReal p) volume := by
    simpa only [Function.comp_def] using
      hf.comp_measurePreserving
        ((volume : Measure (BRRSSpace d)).measurePreserving_sub_left x)
  change Integrable (fun y : BRRSSpace d => K y * f (x - y)) volume
  exact hK.integrable_mul hfshift

/-- The preceding pointwise-existence statement in the bundled form used by
the convolution linearity API. -/
theorem brrs_convolutionExists_of_memLp {d : Nat}
    (K : BRRSSchwartz d) (p : Real) (hp : 1 ≤ p)
    {f : BRRSSpace d → Complex} (hf : MemLp f (ENNReal.ofReal p) volume) :
    ConvolutionExists (K : BRRSSpace d → Complex) f
      (ContinuousLinearMap.mul Complex Complex) volume :=
  fun x => brrs_convolutionExistsAt_of_memLp K p hp hf x

/-- Convolution by a Schwartz kernel preserves a.e. strong measurability. -/
theorem brrs_aestronglyMeasurable_schwartz_convolution {d : Nat}
    (K : BRRSSchwartz d) {f : BRRSSpace d → Complex}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable
      ((K : BRRSSpace d → Complex) ⋆[ContinuousLinearMap.mul Complex Complex, volume] f)
      volume := by
  let H : BRRSSpace d × BRRSSpace d → Complex := fun z =>
    K z.2 * f (z.1 - z.2)
  have hH : AEStronglyMeasurable H (volume.prod volume) :=
    K.continuous.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.mul Complex Complex) hf
  change AEStronglyMeasurable (fun x : BRRSSpace d =>
    ∫ y : BRRSSpace d, K y * f (x - y)) volume
  simpa only [H] using hH.integral_prod_right'

/-- Young's inequality with an a.e.-strongly-measurable `Lᵖ` input.  A
strongly measurable representative is used only in the proof; convolution
itself respects a.e. equality. -/
theorem brrs_eLpNorm_schwartz_convolution_le_of_memLp {d : Nat}
    (K : BRRSSchwartz d) (p : Real) (hp : 1 ≤ p)
    {f : BRRSSpace d → Complex} (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm ((K : BRRSSpace d → Complex)
      ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) (ENNReal.ofReal p) volume ≤
      (∫⁻ y : BRRSSpace d, ‖K y‖ₑ) * eLpNorm f (ENNReal.ofReal p) volume := by
  let f0 : BRRSSpace d → Complex := hf.aestronglyMeasurable.mk f
  have hf0meas : Measurable f0 := hf.aestronglyMeasurable.measurable_mk
  have hfeq : f =ᵐ[volume] f0 := hf.aestronglyMeasurable.ae_eq_mk
  have hconv :
      ((K : BRRSSpace d → Complex)
        ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) =
        ((K : BRRSSpace d → Complex)
          ⋆[ContinuousLinearMap.mul Complex Complex, volume] f0) :=
    convolution_congr (ContinuousLinearMap.mul Complex Complex)
      (Eventually.of_forall fun _ => rfl) hfeq
  calc
    eLpNorm ((K : BRRSSpace d → Complex)
        ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) (ENNReal.ofReal p) volume =
        eLpNorm ((K : BRRSSpace d → Complex)
          ⋆[ContinuousLinearMap.mul Complex Complex, volume] f0) (ENNReal.ofReal p) volume := by
      rw [hconv]
    _ ≤ (∫⁻ y : BRRSSpace d, ‖K y‖ₑ) * eLpNorm f0 (ENNReal.ofReal p) volume := by
      rcases lt_or_eq_of_le hp with hpgt | hpone
      · exact brrs_eLpNorm_convolution_le p hpgt (K : BRRSSpace d → Complex) f0
          K.continuous.measurable hf0meas
      · subst p
        simpa using brrs_eLpNorm_convolution_one_le (K : BRRSSpace d → Complex) f0
          K.continuous.measurable hf0meas
    _ = (∫⁻ y : BRRSSpace d, ‖K y‖ₑ) * eLpNorm f (ENNReal.ofReal p) volume := by
      rw [← eLpNorm_congr_ae hfeq]

/-- The raw convolution by a Schwartz kernel is an honest `Lᵖ` map for
every finite real exponent at least one. -/
theorem brrs_memLp_schwartz_convolution_of_memLp {d : Nat}
    (K : BRRSSchwartz d) (p : Real) (hp : 1 ≤ p)
    {f : BRRSSpace d → Complex} (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp ((K : BRRSSpace d → Complex)
      ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) (ENNReal.ofReal p) volume := by
  have hmass : (∫⁻ y : BRRSSpace d, ‖K y‖ₑ) < ∞ := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm K.integrable]
    exact ENNReal.ofReal_lt_top
  refine ⟨brrs_aestronglyMeasurable_schwartz_convolution K hf.aestronglyMeasurable, ?_⟩
  exact (brrs_eLpNorm_schwartz_convolution_le_of_memLp K p hp hf).trans_lt
    (ENNReal.mul_lt_top hmass hf.eLpNorm_lt_top)

/-- The half-wave phase is unimodular, so the annular symbol has the same
pointwise bound as the cutoff alone. -/
theorem norm_brrsDyadicHalfWaveSchwartzSymbol_le {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) (xi : BRRSSpace d) :
    ‖brrsDyadicHalfWaveSchwartzSymbol Φ j t xi‖ ≤
      SchwartzMap.seminorm Complex 0 0 Φ.symbol := by
  rw [brrsDyadicHalfWaveSchwartzSymbol_apply, brrsDyadicHalfWaveSymbol,
    norm_mul, halfWaveMultiplier, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact norm_brrsDyadicMultiplierSchwartz_le Φ j xi

/-- Plancherel gives a literal fixed-scale `L²` estimate for the BRRS
annular projection.  The constant is the zeroth Schwartz seminorm of the
one-dimensional cutoff and is uniform in the dyadic level. -/
theorem integral_norm_sq_brrsDyadicProjection_le {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (f : BRRSSchwartz d) :
    (∫ x : BRRSSpace d, ‖brrsDyadicProjection Φ j f x‖ ^ 2) ≤
      (SchwartzMap.seminorm Complex 0 0 Φ.symbol) ^ 2 *
        ∫ x : BRRSSpace d, ‖f x‖ ^ 2 := by
  have hC : 0 ≤ SchwartzMap.seminorm Complex 0 0 Φ.symbol := by
    exact (norm_nonneg (Φ.symbol 0)).trans
      (SchwartzMap.norm_le_seminorm Complex Φ.symbol 0)
  calc
    (∫ x : BRRSSpace d, ‖brrsDyadicProjection Φ j f x‖ ^ 2) ≤
        (SchwartzMap.seminorm Complex 0 0 Φ.symbol) ^ 2 *
          ∫ xi : BRRSSpace d, ‖𝓕 (f : BRRSSpace d → Complex) xi‖ ^ 2 := by
      simpa only [brrsDyadicProjection,
        brrsDyadicMultiplierSchwartz_apply, SchwartzMap.fourier_coe] using
        (Auto.Spherical.Auxiliary.integral_norm_sq_fourierInv_schwartz_multiplier_le
          (brrsDyadicMultiplierSchwartz Φ j) (𝓕 f) hC
          (norm_brrsDyadicMultiplierSchwartz_le Φ j))
    _ = (SchwartzMap.seminorm Complex 0 0 Φ.symbol) ^ 2 *
          ∫ x : BRRSSpace d, ‖f x‖ ^ 2 := by
      rw [Auto.Spherical.Auxiliary.integral_norm_sq_fourier_schwartz_eq]

/-- Plancherel gives the literal fixed-time `L²` bound for the BRRS annular
half-wave.  Unimodularity of the phase makes the same cutoff constant work
for every time and dyadic level. -/
theorem fixedTimeL2_brrsDyadicHalfWave {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) (f : BRRSSchwartz d) :
    (∫ x : BRRSSpace d, ‖brrsDyadicHalfWave Φ j t f x‖ ^ 2) ≤
      (SchwartzMap.seminorm Complex 0 0 Φ.symbol) ^ 2 *
        ∫ x : BRRSSpace d, ‖f x‖ ^ 2 := by
  have hC : 0 ≤ SchwartzMap.seminorm Complex 0 0 Φ.symbol := by
    exact (norm_nonneg (Φ.symbol 0)).trans
      (SchwartzMap.norm_le_seminorm Complex Φ.symbol 0)
  calc
    (∫ x : BRRSSpace d, ‖brrsDyadicHalfWave Φ j t f x‖ ^ 2) ≤
        (SchwartzMap.seminorm Complex 0 0 Φ.symbol) ^ 2 *
          ∫ xi : BRRSSpace d, ‖𝓕 (f : BRRSSpace d → Complex) xi‖ ^ 2 := by
      simpa only [brrsDyadicHalfWave,
        brrsDyadicHalfWaveSchwartzSymbol_apply, brrsDyadicHalfWaveSymbol,
        SchwartzMap.fourier_coe] using
        (Auto.Spherical.Auxiliary.integral_norm_sq_fourierInv_schwartz_multiplier_le
          (brrsDyadicHalfWaveSchwartzSymbol Φ j t) (𝓕 f) hC
          (norm_brrsDyadicHalfWaveSchwartzSymbol_le Φ j t))
    _ = (SchwartzMap.seminorm Complex 0 0 Φ.symbol) ^ 2 *
          ∫ x : BRRSSpace d, ‖f x‖ ^ 2 := by
      rw [Auto.Spherical.Auxiliary.integral_norm_sq_fourier_schwartz_eq]

/-- A radial Schwartz input remains orthogonally invariant after the literal
BRRS annular projection.  This is an exact Fourier-symmetry reduction, not a
replacement for the analytic maximal estimate. -/
theorem brrsDyadicProjection_orthogonallyInvariant {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (f : BRRSSchwartz d)
    (hf : IsRadial (f : BRRSSpace d → Complex)) :
    IsOrthogonallyInvariant (brrsDyadicProjection Φ j f) := by
  unfold brrsDyadicProjection
  apply IsOrthogonallyInvariant.fourierInv
  have hfourier : IsOrthogonallyInvariant (𝓕 (f : BRRSSpace d → Complex)) :=
    (hf.orthogonallyInvariant).fourier
  intro A
  funext xi
  change brrsDyadicMultiplier Φ j (A xi) *
      𝓕 (f : BRRSSpace d → Complex) (A xi) = _
  have hmult : brrsDyadicMultiplier Φ j (A xi) =
      brrsDyadicMultiplier Φ j xi := by
    simpa only [Function.comp_apply] using
      congrFun (brrsDyadicMultiplier_orthogonallyInvariant Φ j A) xi
  have hF : 𝓕 (f : BRRSSpace d → Complex) (A xi) =
      𝓕 (f : BRRSSpace d → Complex) xi := by
    simpa only [Function.comp_apply] using congrFun (hfourier A) xi
  rw [hmult, hF]

/-- The literal BRRS annular projection preserves radiality of Schwartz
inputs.  This uses the converse symmetry bridge above, so it is a statement
in the norm-based radiality language of the BRRS setup. -/
theorem brrsDyadicProjection_isRadial {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (f : BRRSSchwartz d)
    (hf : IsRadial (f : BRRSSpace d → Complex)) :
    IsRadial (brrsDyadicProjection Φ j f) :=
  (brrsDyadicProjection_orthogonallyInvariant Φ j f hf).isRadial

/-- A radial Schwartz input remains orthogonally invariant after the literal
BRRS frequency-localized half-wave.  The proof combines Fourier equivariance
with the radiality of both the propagation phase and the annular cutoff. -/
theorem brrsDyadicHalfWave_orthogonallyInvariant {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) (f : BRRSSchwartz d)
    (hf : IsRadial (f : BRRSSpace d → Complex)) :
    IsOrthogonallyInvariant (brrsDyadicHalfWave Φ j t f) := by
  unfold brrsDyadicHalfWave
  apply IsOrthogonallyInvariant.fourierInv
  have hfourier : IsOrthogonallyInvariant (𝓕 (f : BRRSSpace d → Complex)) :=
    (hf.orthogonallyInvariant).fourier
  intro A
  funext xi
  change halfWaveMultiplier t (A xi) * brrsDyadicMultiplier Φ j (A xi) *
      𝓕 (f : BRRSSpace d → Complex) (A xi) = _
  have hphase : halfWaveMultiplier t (A xi) = halfWaveMultiplier t xi := by
    simpa only [Function.comp_apply] using
      congrFun (halfWaveMultiplier_orthogonallyInvariant t A) xi
  have hmult : brrsDyadicMultiplier Φ j (A xi) =
      brrsDyadicMultiplier Φ j xi := by
    simpa only [Function.comp_apply] using
      congrFun (brrsDyadicMultiplier_orthogonallyInvariant Φ j A) xi
  have hF : 𝓕 (f : BRRSSpace d → Complex) (A xi) =
      𝓕 (f : BRRSSpace d → Complex) xi := by
    simpa only [Function.comp_apply] using congrFun (hfourier A) xi
  rw [hphase, hmult, hF]

/-- The literal BRRS frequency-localized half-wave preserves radiality of
Schwartz inputs. -/
theorem brrsDyadicHalfWave_isRadial {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) (f : BRRSSchwartz d)
    (hf : IsRadial (f : BRRSSpace d → Complex)) :
    IsRadial (brrsDyadicHalfWave Φ j t f) :=
  (brrsDyadicHalfWave_orthogonallyInvariant Φ j t f hf).isRadial

/-- The a.e. version of radiality appropriate for an `L^p` input. -/
def IsAERadial {d : Nat} (f : BRRSSpace d → Complex) : Prop :=
  ∃ g : BRRSSpace d → Complex, IsRadial g ∧ f =ᵐ[volume] g

/-- The outer `ell^p(L^p)` norm over a finite set of BRRS times. -/
def discreteLpNorm {d : Nat} (p : Real) (T : Finset Real)
    (u : Real → BRRSSpace d → Complex) : ENNReal :=
  (∑ t ∈ T, (eLpNorm (u t) (ENNReal.ofReal p) volume) ^ p) ^ (p⁻¹)

/-- At `p = 2`, squaring the `L²` seminorm recovers the ordinary real
energy integral. -/
theorem eLpNorm_two_rpow_eq_integral_norm_sq {d : Nat}
    (u : BRRSSpace d → Complex) (hmem : MemLp u 2 volume) :
    (eLpNorm u 2 volume) ^ (2 : Real) =
      ENNReal.ofReal (∫ x : BRRSSpace d, ‖u x‖ ^ 2) := by
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num
  rw [← ENNReal.ofReal_pow]
  · congr 1
    let I : Real := ∫ x : BRRSSpace d, ‖u x‖ ^ 2
    have hI : 0 ≤ I := by
      dsimp [I]
      exact integral_nonneg fun _ => sq_nonneg _
    have hpow := Real.rpow_inv_natCast_pow (x := I) (n := 2) hI (by norm_num)
    change (I ^ (1 / 2)) ^ 2 = I
    norm_num at hpow ⊢
    exact hpow
  · exact Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _

/-- The literal BRRS discrete norm at `p = 2` is exactly the square root of
the finite sum of spatial energies, provided its time slices are in `L²`. -/
theorem discreteLpNorm_two_eq_l2Energy {d : Nat} (T : Finset Real)
    (u : Real → BRRSSpace d → Complex)
    (hmem : ∀ t ∈ T, MemLp (u t) 2 volume) :
    discreteLpNorm 2 T u =
      (ENNReal.ofReal (∑ t ∈ T, ∫ x : BRRSSpace d, ‖u t x‖ ^ 2)) ^
        ((2 : Real)⁻¹) := by
  classical
  unfold discreteLpNorm
  simp only [ENNReal.ofReal_ofNat]
  have hsum :
      (∑ t ∈ T, (eLpNorm (u t) 2 volume) ^ (2 : Real)) =
        ENNReal.ofReal (∑ t ∈ T, ∫ x : BRRSSpace d, ‖u t x‖ ^ 2) := by
    calc
      (∑ t ∈ T, (eLpNorm (u t) 2 volume) ^ (2 : Real)) =
          ∑ t ∈ T, ENNReal.ofReal (∫ x : BRRSSpace d, ‖u t x‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact eLpNorm_two_rpow_eq_integral_norm_sq (u t) (hmem t ht)
      _ = ENNReal.ofReal (∑ t ∈ T, ∫ x : BRRSSpace d, ‖u t x‖ ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro t ht
        exact integral_nonneg fun _ => sq_nonneg _
  rw [hsum]

/-- The existing planar auxiliary Littlewood--Paley half-wave has `L²`
time slices, so the literal discrete BRRS norm can be applied to it at the
endpoint. -/
theorem auxiliaryDyadicHalfWave_memLp_two (C : lpCutoffs 2) (j : Nat)
    (t : Real) (f : BRRSSchwartz 2) :
    MemLp (dyadicHalfWave C j t f) 2 volume := by
  rw [auxiliaryDyadicHalfWave_eq_mss]
  refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
  · exact ((Auto.Spherical.MSSBase.continuous_dyadicHalfWaveSpaceTime C .plus j f).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact Auto.Spherical.MSSBase.integrable_norm_sq_dyadicHalfWave C .plus j t f

/-- The finite auxiliary `L²` energy estimates above are therefore a
literal `discreteLpNorm` estimate in squared form. -/
theorem discreteLpNorm_two_auxiliaryDyadicHalfWave_eq_l2Energy
    (C : lpCutoffs 2) (j : Nat) (T : Finset Real) (f : BRRSSchwartz 2) :
    discreteLpNorm 2 T (fun t => dyadicHalfWave C j t f) =
      (ENNReal.ofReal (∑ t ∈ T, ∫ x : BRRSSpace 2,
        ‖dyadicHalfWave C j t f x‖ ^ 2)) ^ ((2 : Real)⁻¹) := by
  apply discreteLpNorm_two_eq_l2Energy
  intro t ht
  exact auxiliaryDyadicHalfWave_memLp_two C j t f

/-- The literal BRRS annular half-wave has an `L²` time slice at every
scale.  This is a genuine Schwartz-multiplier statement: the annular
half-wave symbol is converted above into a Schwartz map before applying the
Fourier inversion facts. -/
theorem brrsDyadicHalfWave_memLp_two {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real) (f : BRRSSchwartz d) :
    MemLp (brrsDyadicHalfWave Φ j t f) 2 volume := by
  let g : BRRSSchwartz d := SchwartzMap.smulLeftCLM Complex
    (brrsDyadicHalfWaveSchwartzSymbol Φ j t : BRRSSpace d → Complex) (𝓕 f)
  have hg : (g : BRRSSpace d → Complex) = fun xi : BRRSSpace d =>
      brrsDyadicHalfWaveSchwartzSymbol Φ j t xi * 𝓕 f xi := by
    funext xi
    simp only [g, SchwartzMap.smulLeftCLM_apply
      (brrsDyadicHalfWaveSchwartzSymbol Φ j t).hasTemperateGrowth, smul_eq_mul]
  have hhalf : brrsDyadicHalfWave Φ j t f = 𝓕⁻ (g : BRRSSpace d → Complex) := by
    funext x
    rw [brrsDyadicHalfWave, hg]
    simp only [brrsDyadicHalfWaveSchwartzSymbol_apply,
      brrsDyadicHalfWaveSymbol, SchwartzMap.fourier_coe]
  refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
  · rw [hhalf]
    exact
      (Auto.Spherical.Auxiliary.continuous_fourierInv_schwartz g).aestronglyMeasurable
  · rw [hhalf, hg]
    exact Auto.Spherical.Auxiliary.integrable_norm_sq_fourierInv_schwartz_multiplier
      (brrsDyadicHalfWaveSchwartzSymbol Φ j t) (𝓕 f)

/-- The literal BRRS discrete `L²` norm is the square root of its finite
sum of spatial energies. -/
theorem discreteLpNorm_two_brrsDyadicHalfWave_eq_l2Energy {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (T : Finset Real) (f : BRRSSchwartz d) :
    discreteLpNorm 2 T (fun t => brrsDyadicHalfWave Φ j t f) =
      (ENNReal.ofReal (∑ t ∈ T, ∫ x : BRRSSpace d,
        ‖brrsDyadicHalfWave Φ j t f x‖ ^ 2)) ^ ((2 : Real)⁻¹) := by
  apply discreteLpNorm_two_eq_l2Energy
  intro t ht
  exact brrsDyadicHalfWave_memLp_two Φ j t f

/-- A finite real `L²` energy bound converts directly into the literal
BRRS discrete norm estimate.  Keeping this elementary square-root step
separate makes it reusable for both entropy and sampling estimates. -/
theorem discreteLpNorm_two_le_of_l2Energy_le {d : Nat} (T : Finset Real)
    (u : Real → BRRSSpace d → Complex) (f : BRRSSpace d → Complex)
    (hmemU : ∀ t ∈ T, MemLp (u t) 2 volume) (hmemF : MemLp f 2 volume)
    {A : Real} (hA : 0 ≤ A)
    (henergy : (∑ t ∈ T, ∫ x : BRRSSpace d, ‖u t x‖ ^ 2) ≤
      A ^ 2 * ∫ x : BRRSSpace d, ‖f x‖ ^ 2) :
    discreteLpNorm 2 T u ≤ ENNReal.ofReal A * eLpNorm f 2 volume := by
  rw [discreteLpNorm_two_eq_l2Energy T u hmemU]
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : Real) < 2)).mp
  calc
    (ENNReal.ofReal (∑ t ∈ T, ∫ x : BRRSSpace d, ‖u t x‖ ^ 2) ^
      ((2 : Real)⁻¹)) ^ (2 : Real) =
        ENNReal.ofReal (∑ t ∈ T, ∫ x : BRRSSpace d, ‖u t x‖ ^ 2) := by
      rw [(ENNReal.rpow_mul _ _ _).symm]
      norm_num
    _ ≤ ENNReal.ofReal (A ^ 2 * ∫ x : BRRSSpace d, ‖f x‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal henergy
    _ = (ENNReal.ofReal A * eLpNorm f 2 volume) ^ (2 : Real) := by
      rw [ENNReal.ofReal_mul (sq_nonneg A)]
      rw [ENNReal.ofReal_pow hA 2]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : Real) ≤ 2)]
      rw [eLpNorm_two_rpow_eq_integral_norm_sq f hmemF]
      exact congrArg (fun z => z * ENNReal.ofReal
        (∫ x : BRRSSpace d, ‖f x‖ ^ 2))
        (ENNReal.rpow_two (ENNReal.ofReal A)).symm

/-- Summing the literal fixed-time Plancherel endpoint over finitely many
times.  Time-set geometry enters only through the cardinality factor. -/
theorem brrsDyadicHalfWave_l2Sum_le_card {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (T : Finset Real) (f : BRRSSchwartz d) :
    (∑ t ∈ T, ∫ x : BRRSSpace d, ‖brrsDyadicHalfWave Φ j t f x‖ ^ 2) ≤
      (SchwartzMap.seminorm Complex 0 0 Φ.symbol) ^ 2 * (T.card : Real) *
        ∫ x : BRRSSpace d, ‖f x‖ ^ 2 := by
  calc
    (∑ t ∈ T, ∫ x : BRRSSpace d, ‖brrsDyadicHalfWave Φ j t f x‖ ^ 2) ≤
        ∑ _t ∈ T, (SchwartzMap.seminorm Complex 0 0 Φ.symbol) ^ 2 *
          ∫ x : BRRSSpace d, ‖f x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t _ht
      exact fixedTimeL2_brrsDyadicHalfWave Φ j t f
    _ = (SchwartzMap.seminorm Complex 0 0 Φ.symbol) ^ 2 * (T.card : Real) *
        ∫ x : BRRSSpace d, ‖f x‖ ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The fixed-time Sobolev exponent `s_p` in BRRS. -/
def sobolevExponent (d : Nat) (p : Real) : Real :=
  ((d : Real) - 1) * (1 / 2 - 1 / p)

/-- The critical exponent in BRRS Theorem 1.1, once the Legendre--Assouad
function is supplied. -/
def criticalExponent (nu : Set Real → Real → Real) (E : Set Real)
    (d : Nat) (p : Real) : Real :=
  nu E (p * sobolevExponent d p) / p

/-- An a.e. bounded linear `L^p` realization of the Fourier-defined operator
`e^{it√{-Δ}} P_j`.

Mathlib represents `L^p` elements by functions modulo a.e. equality, while
the Fourier integral below starts on Schwartz functions.  This interface
records a chosen representative of the standard `L^p` extension, rather than
silently treating the Schwartz formula as defined pointwise on every `L^p`
function.  The main BRRS target existentially chooses this interface, rather
than silently treating the Schwartz formula as defined pointwise on every
`L^p` function. -/
structure BRRSLpHalfWaveExtension (d : Nat) (Φ : BRRSAnnularCutoff) where
  apply : Nat → Real → (BRRSSpace d → Complex) → BRRSSpace d → Complex
  congr_ae : ∀ (j : Nat) (t : Real) {f g : BRRSSpace d → Complex},
    f =ᵐ[volume] g → apply j t f =ᵐ[volume] apply j t g
  extends_schwartz : ∀ (j : Nat) (t : Real) (f : BRRSSchwartz d),
    apply j t (f : BRRSSpace d → Complex) =ᵐ[volume] brrsDyadicHalfWave Φ j t f
  maps_memLp : ∀ (j : Nat) (t p : Real), 1 ≤ p →
    ∀ {f : BRRSSpace d → Complex}, MemLp f (ENNReal.ofReal p) volume →
      MemLp (apply j t f) (ENNReal.ofReal p) volume
  map_add_ae : ∀ (j : Nat) (t p : Real), 1 ≤ p →
    ∀ {f g : BRRSSpace d → Complex}, MemLp f (ENNReal.ofReal p) volume →
      MemLp g (ENNReal.ofReal p) volume →
      apply j t (f + g) =ᵐ[volume] (apply j t f + apply j t g)
  map_smul_ae : ∀ (j : Nat) (t p : Real), 1 ≤ p →
    ∀ (c : Complex) {f : BRRSSpace d → Complex},
      MemLp f (ENNReal.ofReal p) volume →
      apply j t (c • f) =ᵐ[volume] (c • apply j t f)
  bounded_on_Lp : ∀ (j : Nat) (t p : Real), 1 ≤ p →
    ∃ K : Real, 0 ≤ K ∧ ∀ f : BRRSSpace d → Complex,
      MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (apply j t f) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) volume

/-- The canonical `Lᵖ` realization of the BRRS annular half-wave: convolution
by its inverse-Fourier Schwartz kernel.  All fields are proved directly from
the dimension-generic Young development above, so this is not an abstract
choice of representatives. -/
noncomputable def brrsLpHalfWaveExtension {d : Nat}
    (Φ : BRRSAnnularCutoff) : BRRSLpHalfWaveExtension d Φ where
  apply j t f :=
    (brrsDyadicHalfWaveKernel Φ j t : BRRSSpace d → Complex)
      ⋆[ContinuousLinearMap.mul Complex Complex, volume] f
  congr_ae := by
    intro j t f g hfg
    apply Eventually.of_forall
    intro x
    exact congrFun
      (convolution_congr (ContinuousLinearMap.mul Complex Complex)
        (Eventually.of_forall fun _ => rfl) hfg) x
  extends_schwartz := by
    intro j t f
    apply Eventually.of_forall
    intro x
    exact (brrsDyadicHalfWave_eq_kernel_convolution Φ j t f x).symm
  maps_memLp := by
    intro j t p hp f hf
    exact brrs_memLp_schwartz_convolution_of_memLp
      (brrsDyadicHalfWaveKernel Φ j t) p hp hf
  map_add_ae := by
    intro j t p hp f g hf hg
    apply Eventually.of_forall
    intro x
    exact congrFun
      ((brrs_convolutionExists_of_memLp (brrsDyadicHalfWaveKernel Φ j t) p hp hf).distrib_add
        (brrs_convolutionExists_of_memLp (brrsDyadicHalfWaveKernel Φ j t) p hp hg)) x
  map_smul_ae := by
    intro j t _p _hp c f _hf
    apply Eventually.of_forall
    intro x
    exact congrFun
      (convolution_smul
        (f := (brrsDyadicHalfWaveKernel Φ j t : BRRSSpace d → Complex))
        (g := f) (y := c)) x
  bounded_on_Lp := by
    intro j t p hp
    refine ⟨∫ y : BRRSSpace d, ‖brrsDyadicHalfWaveKernel Φ j t y‖,
      integral_nonneg fun _ => norm_nonneg _, ?_⟩
    intro f hf
    calc
      eLpNorm
          ((brrsDyadicHalfWaveKernel Φ j t : BRRSSpace d → Complex)
            ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) (ENNReal.ofReal p) volume ≤
          (∫⁻ y : BRRSSpace d, ‖brrsDyadicHalfWaveKernel Φ j t y‖ₑ) *
            eLpNorm f (ENNReal.ofReal p) volume :=
        brrs_eLpNorm_schwartz_convolution_le_of_memLp
          (brrsDyadicHalfWaveKernel Φ j t) p hp hf
      _ = ENNReal.ofReal (∫ y : BRRSSpace d, ‖brrsDyadicHalfWaveKernel Φ j t y‖) *
            eLpNorm f (ENNReal.ofReal p) volume := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm
          (brrsDyadicHalfWaveKernel Φ j t).integrable]

/-- The canonical BRRS extension has the literal fixed-time `L∞` endpoint
given by its physical Schwartz kernel.  The displayed constant is deliberately
the actual kernel mass at `(j,t)`: no dyadic growth estimate for that mass is
claimed here.  Establishing its sharp rate is the remaining oscillatory-kernel
part of the BRRS argument. -/
theorem norm_brrsLpHalfWaveExtension_apply_le_kernelMass_mul_bound {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (t : Real)
    (f : BRRSSpace d → Complex) (hf : Continuous f)
    {C : Real} (hbound : ∀ y, ‖f y‖ ≤ C) (x : BRRSSpace d) :
    ‖(brrsLpHalfWaveExtension Φ).apply j t f x‖ ≤
      (∫ y : BRRSSpace d, ‖brrsDyadicHalfWaveKernel Φ j t y‖) * C := by
  change ‖(((brrsDyadicHalfWaveKernel Φ j t : BRRSSchwartz d) :
      BRRSSpace d → Complex)
        ⋆[ContinuousLinearMap.mul Complex Complex, volume] f) x‖ ≤ _
  exact Auto.Spherical.SurfaceMeasureDecay.norm_convolution_mul_le_integral_norm_mul_bound
    ((brrsDyadicHalfWaveKernel Φ j t : BRRSSchwartz d) : BRRSSpace d → Complex) f
    (brrsDyadicHalfWaveKernel Φ j t).integrable hf hbound x

/-- A uniform BRRS estimate with a prescribed exponent `s`, formulated on
the full radial `L^p` domain through a specified realization of the Schwartz
Fourier multiplier. -/
def UniformEstimateAtExponent {d : Nat} (Φ : BRRSAnnularCutoff)
    (W : BRRSLpHalfWaveExtension d Φ) (E : Set Real) (p s : Real) : Prop :=
  ∃ K : Real, 0 < K ∧
    ∀ j : Nat, 1 ≤ j → ∀ T : Finset Real, IsDyadicDiscretization E j T →
      ∀ f : BRRSSpace d → Complex, MemLp f (ENNReal.ofReal p) volume →
        IsAERadial f →
          discreteLpNorm p T (fun t => W.apply j t f) ≤
            ENNReal.ofReal (K * (2 : Real) ^ ((j : Real) * s)) *
              eLpNorm f (ENNReal.ofReal p) volume

/-- The same prescribed-exponent estimate on radial Schwartz inputs.  This
is the literal Fourier-calculus core of the paper's estimate. -/
def SchwartzCoreUniformEstimateAtExponent {d : Nat} (Φ : BRRSAnnularCutoff)
    (E : Set Real) (p s : Real) : Prop :=
  ∃ K : Real, 0 < K ∧
    ∀ j : Nat, 1 ≤ j → ∀ T : Finset Real, IsDyadicDiscretization E j T →
      ∀ f : BRRSSchwartz d, IsRadial (f : BRRSSpace d → Complex) →
        discreteLpNorm p T (fun t => brrsDyadicHalfWave Φ j t f) ≤
          ENNReal.ofReal (K * (2 : Real) ^ ((j : Real) * s)) *
            eLpNorm (f : BRRSSpace d → Complex) (ENNReal.ofReal p) volume

/-- The dense-Schwartz-core form of BRRS Theorem 1.1.

It has the exact exponent and all discretizations from (1.5), but deliberately
quantifies over radial Schwartz functions because `brrsDyadicHalfWave` is the
literal Fourier integral.  The paper's all-radial-`L^p` statement is recorded
separately by `BRRSTheoremOneStatementFor`. -/
def BRRSTheoremOneSchwartzCoreStatementFor (nu : Set Real → Real → Real)
    (d : Nat) (Φ : BRRSAnnularCutoff) (E : Set Real) (p : Real) : Prop :=
  2 ≤ d ∧ E ⊆ Icc (1 : Real) 2 ∧ 2 ≤ p ∧
    ∀ epsilon : Real, 0 < epsilon →
      SchwartzCoreUniformEstimateAtExponent (d := d) Φ E p
        (criticalExponent nu E d p + epsilon)

/-- The all-radial-`L^p` statement of BRRS Theorem 1.1, with the required
bounded linear `L^p` realization of its literal Fourier multiplier made
explicit.  The existential quantifier is the formal counterpart of applying
the canonical multiplier to arbitrary `L^p` functions.  Since `p` is a real
number, `2 ≤ p` represents the paper's finite range `2 ≤ p < ∞`.  This is a
statement package only; it is not a claimed theorem in this file. -/
def BRRSTheoremOneStatementFor (nu : Set Real → Real → Real)
    (d : Nat) (Φ : BRRSAnnularCutoff) (E : Set Real) (p : Real) : Prop :=
  2 ≤ d ∧ E ⊆ Icc (1 : Real) 2 ∧ 2 ≤ p ∧
    ∃ W : BRRSLpHalfWaveExtension d Φ,
      ∀ epsilon : Real, 0 < epsilon →
        UniformEstimateAtExponent Φ W E p
          (criticalExponent nu E d p + epsilon)

/-- Sharpness in the sense asserted after BRRS (1.5): for a nonempty time
set, no exponent strictly smaller than the critical one has a uniform estimate
for the same propagator.  The nonemptiness qualification excludes the
vacuous empty-discretization case. -/
def BRRSTheoremOneSharpnessStatementFor (nu : Set Real → Real → Real)
    {d : Nat} {Φ : BRRSAnnularCutoff} (W : BRRSLpHalfWaveExtension d Φ)
    (E : Set Real) (p : Real) : Prop :=
  E.Nonempty → ∀ s : Real, s < criticalExponent nu E d p →
    ¬ UniformEstimateAtExponent Φ W E p s

/-- The joint upper-bound-and-sharpness package corresponding to the complete
assertion of BRRS Theorem 1.1.  Both clauses use the same specified
annular multiplier and every a.e.-bounded linear `L^p` realization of its
frequency-localized half-wave. -/
def BRRSTheoremOneWithSharpnessStatementFor (nu : Set Real → Real → Real)
    (d : Nat) (Φ : BRRSAnnularCutoff) (E : Set Real) (p : Real) : Prop :=
  2 ≤ d ∧ E ⊆ Icc (1 : Real) 2 ∧ 2 ≤ p ∧
    ∃ W : BRRSLpHalfWaveExtension d Φ,
      (∀ epsilon : Real, 0 < epsilon →
        UniformEstimateAtExponent Φ W E p
          (criticalExponent nu E d p + epsilon)) ∧
        BRRSTheoremOneSharpnessStatementFor nu W E p

/-- The literal BRRS Legendre--Assouad function, imported from the dedicated
Euclidean dimension module. -/
abbrev brrsLegendreAssouadFunction :=
  Auto.Spherical.LegendreAssouad.brrsLegendreAssouadFunction

/-- The dense Schwartz-core target of BRRS Theorem 1.1 with the literal
additive-Euclidean `ν_E^♯` from BRRS (1.4). -/
def BRRSTheoremOneSchwartzCoreStatement (d : Nat) (Φ : BRRSAnnularCutoff)
    (E : Set Real) (p : Real) : Prop :=
  BRRSTheoremOneSchwartzCoreStatementFor brrsLegendreAssouadFunction d Φ E p

/-- The all-radial-`L^p` target of BRRS Theorem 1.1 with the literal
additive-Euclidean `ν_E^♯` from BRRS (1.4). -/
def BRRSTheoremOneStatement (d : Nat) (Φ : BRRSAnnularCutoff) (E : Set Real)
    (p : Real) : Prop :=
  BRRSTheoremOneStatementFor brrsLegendreAssouadFunction d Φ E p

/-- The sharpness target in BRRS Theorem 1.1 with the literal
additive-Euclidean `ν_E^♯` from BRRS (1.4). -/
def BRRSTheoremOneSharpnessStatement {d : Nat} {Φ : BRRSAnnularCutoff}
    (W : BRRSLpHalfWaveExtension d Φ) (E : Set Real) (p : Real) : Prop :=
  BRRSTheoremOneSharpnessStatementFor brrsLegendreAssouadFunction W E p

/-- The combined upper-bound and sharpness target of BRRS Theorem 1.1 with
the literal additive-Euclidean `ν_E^♯` from BRRS (1.4). -/
def BRRSTheoremOneWithSharpnessStatement (d : Nat) (Φ : BRRSAnnularCutoff)
    (E : Set Real) (p : Real) : Prop :=
  BRRSTheoremOneWithSharpnessStatementFor brrsLegendreAssouadFunction d Φ E p

/-- On a BRRS time set contained in `[1,2]`, the global entropy is one of
the interval tests in the zero-penalty profile (take the interval `[1,2]`). -/
theorem brrsEntropyNumber_le_brrsLegendreAssouadProfile_zero_of_subset_Icc
    {E : Set Real} (hE : E ⊆ Icc (1 : Real) 2) {δ : NNReal} (hδ : δ ≤ 1) :
    brrsEntropyNumber E δ ≤
      Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E 0 δ := by
  have hsub : E ⊆ E ∩ Auto.Spherical.LegendreAssouad.brrsInterval 1 1 := by
    intro x hx
    refine ⟨hx, ?_⟩
    change 1 ≤ x ∧ x ≤ 1 + 1
    norm_num
    exact hE hx
  calc
    brrsEntropyNumber E δ ≤
        brrsEntropyNumber (E ∩ Auto.Spherical.LegendreAssouad.brrsInterval 1 1) δ :=
      Auto.Spherical.LegendreAssouad.brrsEntropyNumber_mono hsub δ
    _ = (1 : ENNReal) ^ (-(0 : Real)) *
        brrsEntropyNumber (E ∩ Auto.Spherical.LegendreAssouad.brrsInterval 1 1) δ := by
      simp
    _ ≤ Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E 0 δ := by
      unfold Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile
      exact le_iSup_of_le (1 : Real)
        (le_iSup_of_le ⟨1, hδ, le_rfl⟩ (le_refl _))

/-- The entropy scale forced by a BRRS time discretization is exactly the
next standard dyadic scale. -/
theorem brrsDyadicEntropyScale_eq_dyadicMultiplicativeScale_succ (j : Nat) :
    (⟨dyadicTimeScale j / 2, by
      unfold dyadicTimeScale
      exact (div_pos (inv_pos.mpr
        (pow_pos (by norm_num : (0 : Real) < 2) _))
        (by norm_num : (0 : Real) < 2)).le⟩ : NNReal) =
      Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1) := by
  apply NNReal.eq
  change ((2 : Real) ^ j)⁻¹ / 2 =
    (((2 : NNReal)⁻¹ ^ (j + 1) : NNReal) : Real)
  norm_cast
  push_cast
  rw [pow_succ, ← inv_pow]
  ring

/-- Strictly above the literal BRRS value `ν_E^♯(0)`, its finite-scale
entropy profile obeys the corresponding power bound at all sufficiently
small scales.  This is the additive-Euclidean counterpart of the analogous
multiplicative entropy-tail extraction. -/
theorem eventually_brrsLegendreAssouadProfile_zero_le_inv_rpow_of_lt
    {E : Set Real} {q : Real}
    (hνq : brrsLegendreAssouadFunction E 0 < q) :
    ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E 0 δ ≤
        ((δ : ENNReal)⁻¹) ^ q := by
  have htop : Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent E 0 ≠ ⊤ :=
    Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent_ne_top_of_nonneg E
      (by norm_num)
  have hexponent :
      Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent E 0 < (q : EReal) := by
    apply lt_of_not_ge
    intro hq
    have hreal := EReal.toReal_le_toReal hq (EReal.coe_ne_bot q) htop
    rw [← Auto.Spherical.LegendreAssouad.brrsLegendreAssouadFunction_eq_exponent_toReal]
      at hreal
    exact (not_le_of_gt hνq) hreal
  have hquotient : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      Auto.Spherical.LegendreAssouad.entropyLogQuotient
        (Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E 0 δ) δ <
        (q : EReal) :=
    Filter.eventually_lt_of_limsup_lt hexponent
  have hsmall : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), δ ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [hquotient, hsmall] with δ hδ hδsmall
  exact Auto.Spherical.LegendreAssouad.le_inv_rpow_of_entropyLogQuotient_lt
    hδsmall.1 hδsmall.2 hδ

/-- Strictly above the literal BRRS value at any nonnegative penalty, the
finite-scale local entropy profile has the corresponding eventual inverse
power bound.  This is the scale-uniform entropy input used by the
`κ_{j,m}` decomposition in the proof of BRRS Proposition 5.1. -/
theorem eventually_brrsLegendreAssouadProfile_le_inv_rpow_of_lt
    {E : Set Real} {alpha q : Real} (halpha : 0 ≤ alpha)
    (hνq : brrsLegendreAssouadFunction E alpha < q) :
    ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E alpha δ ≤
        ((δ : ENNReal)⁻¹) ^ q := by
  have htop : Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent E alpha ≠ ⊤ :=
    Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent_ne_top_of_nonneg E
      halpha
  have hexponent :
      Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent E alpha <
        (q : EReal) := by
    apply lt_of_not_ge
    intro hq
    have hreal := EReal.toReal_le_toReal hq (EReal.coe_ne_bot q) htop
    rw [← Auto.Spherical.LegendreAssouad.brrsLegendreAssouadFunction_eq_exponent_toReal]
      at hreal
    exact (not_le_of_gt hνq) hreal
  have hquotient : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      Auto.Spherical.LegendreAssouad.entropyLogQuotient
        (Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E alpha δ) δ <
        (q : EReal) :=
    Filter.eventually_lt_of_limsup_lt hexponent
  have hsmall : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), δ ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [hquotient, hsmall] with δ hδ hδsmall
  exact Auto.Spherical.LegendreAssouad.le_inv_rpow_of_entropyLogQuotient_lt
    hδsmall.1 hδsmall.2 hδ

/-- Each individual interval-scale entropy test is bounded by the literal
BRRS finite-scale profile.  This is exactly the estimate defining the
quantities `κ_{j,m}` in the radial upper-bound argument. -/
theorem brrsWeightedEntropy_inter_interval_le_profile
    (E : Set Real) (alpha : Real) (delta : NNReal) (a : Real)
    (R : Icc delta 1) :
    (R.1 : ENNReal) ^ (-alpha) *
        brrsEntropyNumber (E ∩ Auto.Spherical.LegendreAssouad.brrsInterval a R.1) delta ≤
      Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E alpha delta := by
  unfold Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile
  exact le_iSup_of_le a (le_iSup_of_le R (le_refl _))

/-- A dyadic discretization inherits the local weighted entropy control at
every interval scale between its mesh and one.  The half-mesh is the precise
packing-to-covering adjustment forced by the closed-ball convention in
`brrsEntropyNumber`. -/
theorem dyadicDiscretization_weighted_local_card_le_profile
    {E : Set Real} {alpha : Real} {j : Nat} {T : Finset Real}
    (hT : IsDyadicDiscretization E j T) (a : Real)
    (R : NNReal) (hRlo : dyadicTimeScale j ≤ (R : Real)) (hRhi : R ≤ 1)
    (U : Finset Real) (hUT : (↑U : Set Real) ⊆ (↑T : Set Real))
    (hUI : (↑U : Set Real) ⊆
      Auto.Spherical.LegendreAssouad.brrsInterval a (R : Real)) :
    (R : ENNReal) ^ (-alpha) * (U.card : ENNReal) ≤
      Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E alpha
        ⟨dyadicTimeScale j / 2, by
          unfold dyadicTimeScale
          positivity⟩ := by
  let delta : Real := dyadicTimeScale j
  have hdelta : 0 < delta := by
    dsimp [delta, dyadicTimeScale]
    positivity
  have hUsub : (↑U : Set Real) ⊆
      E ∩ Auto.Spherical.LegendreAssouad.brrsInterval a (R : Real) := by
    intro x hx
    exact ⟨hT.subset (hUT hx), hUI hx⟩
  have hUsep : IsSeparated U delta := by
    intro s hs t ht hst
    exact hT.separated (hUT hs) (hUT ht) hst
  have hcard : (U.card : ENNReal) ≤
      brrsEntropyNumber (E ∩ Auto.Spherical.LegendreAssouad.brrsInterval a (R : Real))
        ⟨delta / 2, by positivity⟩ :=
    finset_card_le_brrsEntropyNumber_half_scale_of_isSeparated hdelta hUsub hUsep
  have hR : R ∈ Icc ⟨delta / 2, by positivity⟩ 1 := by
    constructor
    · change delta / 2 ≤ (R : Real)
      have hhalf : delta / 2 ≤ delta := by linarith
      exact hhalf.trans (by simpa [delta] using hRlo)
    · exact hRhi
  have hprofile := brrsWeightedEntropy_inter_interval_le_profile E alpha
    ⟨delta / 2, by positivity⟩ a ⟨R, hR⟩
  calc
    (R : ENNReal) ^ (-alpha) * (U.card : ENNReal) ≤
        (R : ENNReal) ^ (-alpha) *
          brrsEntropyNumber (E ∩ Auto.Spherical.LegendreAssouad.brrsInterval a (R : Real))
            ⟨delta / 2, by positivity⟩ :=
      mul_le_mul' le_rfl hcard
    _ ≤ Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E alpha
          ⟨delta / 2, by positivity⟩ := by
      simpa using hprofile
  

/-- A strict BRRS Legendre--Assouad exponent uniformly controls every local
time-grid count in the tail.  This is the precise entropy statement needed
for the `κ_{j,m}` factors of BRRS Proposition 5.1; the analytic radial-kernel
estimate can consume it without replacing `ν_E^♯` by a coarser dimension. -/
theorem exists_tail_dyadicDiscretization_weighted_local_card_le_inv_rpow_of_lt
    {E : Set Real} {alpha q : Real} (halpha : 0 ≤ alpha)
    (hνq : brrsLegendreAssouadFunction E alpha < q) :
    ∃ J : Nat, ∀ j ≥ J, ∀ T : Finset Real, IsDyadicDiscretization E j T →
      ∀ (a : Real) (R : NNReal), dyadicTimeScale j ≤ (R : Real) → R ≤ 1 →
        ∀ U : Finset Real, (↑U : Set Real) ⊆ (↑T : Set Real) →
           (↑U : Set Real) ⊆
             Auto.Spherical.LegendreAssouad.brrsInterval a (R : Real) →
           (R : ENNReal) ^ (-alpha) * (U.card : ENNReal) ≤
            ((Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1) :
              ENNReal)⁻¹) ^ q := by
  have hprofile :=
    eventually_brrsLegendreAssouadProfile_le_inv_rpow_of_lt halpha hνq
  have htail : ∀ᶠ n : Nat in Filter.atTop,
      Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E alpha
          (Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale n) ≤
        ((Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale n : ENNReal)⁻¹) ^ q :=
    Auto.Spherical.LegendreAssouad.tendsto_dyadicMultiplicativeScale_atTop_nhdsWithin_zero
      |>.eventually hprofile
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 htail
  refine ⟨J, ?_⟩
  intro j hj T hT a R hRlo hRhi U hUT hUI
  have hlocal := dyadicDiscretization_weighted_local_card_le_profile (alpha := alpha) hT a R
    hRlo hRhi U hUT hUI
  have hscale :
      (⟨dyadicTimeScale j / 2, by
        unfold dyadicTimeScale
        positivity⟩ : NNReal) =
        Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1) :=
    brrsDyadicEntropyScale_eq_dyadicMultiplicativeScale_succ j
  calc
    (R : ENNReal) ^ (-alpha) * (U.card : ENNReal) ≤
        Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E alpha
          ⟨dyadicTimeScale j / 2, by
            unfold dyadicTimeScale
            positivity⟩ := hlocal
    _ = Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E alpha
          (Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1)) := by
      rw [hscale]
    _ ≤ ((Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1) : ENNReal)⁻¹) ^ q :=
      hJ (j + 1) (hj.trans (Nat.le_succ _))

/-- A strict literal BRRS entropy exponent controls the cardinality of every
sufficiently fine dyadic time discretization.  The successor in the scale is
the closed-ball half-scale from `brrsEntropyNumber`. -/
theorem exists_tail_dyadicDiscretization_card_le_inv_rpow_of_brrsLegendreAssouad_lt
    {E : Set Real} {q : Real} (hE : E ⊆ Icc (1 : Real) 2)
    (hνq : brrsLegendreAssouadFunction E 0 < q) :
    ∃ J : Nat, ∀ j ≥ J, ∀ T : Finset Real, IsDyadicDiscretization E j T →
      (T.card : ENNReal) ≤
        ((Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1) : ENNReal)⁻¹) ^ q := by
  have hprofile :=
    eventually_brrsLegendreAssouadProfile_zero_le_inv_rpow_of_lt (E := E) hνq
  have hsmall : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), δ ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  have hentropy : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      brrsEntropyNumber E δ ≤ ((δ : ENNReal)⁻¹) ^ q := by
    filter_upwards [hprofile, hsmall] with δ hδ hδsmall
    exact (brrsEntropyNumber_le_brrsLegendreAssouadProfile_zero_of_subset_Icc
      hE hδsmall.2.le).trans hδ
  have htail : ∀ᶠ n : Nat in Filter.atTop,
      brrsEntropyNumber E
          (Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale n) ≤
        ((Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale n : ENNReal)⁻¹) ^ q :=
    Auto.Spherical.LegendreAssouad.tendsto_dyadicMultiplicativeScale_atTop_nhdsWithin_zero
      |>.eventually hentropy
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 htail
  refine ⟨J, ?_⟩
  intro j hj T hT
  let δ : NNReal := ⟨dyadicTimeScale j / 2, by
    unfold dyadicTimeScale
    exact (div_pos (inv_pos.mpr
      (pow_pos (by norm_num : (0 : Real) < 2) _))
      (by norm_num : (0 : Real) < 2)).le⟩
  have hδ : δ = Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1) := by
    dsimp [δ]
    exact brrsDyadicEntropyScale_eq_dyadicMultiplicativeScale_succ j
  have hcard : (T.card : ENNReal) ≤ brrsEntropyNumber E δ := by
    simpa only [δ] using dyadicDiscretization_card_le_brrsEntropyNumber_half_scale hT
  calc
    (T.card : ENNReal) ≤ brrsEntropyNumber E δ := hcard
    _ = brrsEntropyNumber E
        (Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1)) := by rw [hδ]
    _ ≤ ((Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1) : ENNReal)⁻¹) ^ q :=
      hJ (j + 1) (hj.trans (Nat.le_succ _))

/-- The elementary interval-grid bound gives a uniform cardinality estimate
for every BRRS discretization inside `[1,2]`.  This controls the finitely
many scales preceding an entropy tail. -/
theorem dyadicDiscretization_card_le_eight_mul_two_pow_of_subset_Icc
    {E : Set Real} (hE : E ⊆ Icc (1 : Real) 2) (j : Nat) (T : Finset Real)
    (hT : IsDyadicDiscretization E j T) :
    (T.card : ENNReal) ≤ 8 * (2 : ENNReal) ^ j := by
  let δ : NNReal := Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1)
  have hδpos : 0 < (δ : Real) := by
    exact_mod_cast Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale_pos (j + 1)
  have hδle : (δ : Real) ≤ 1 := by
    exact_mod_cast Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale_le_one (j + 1)
  have hentropy : brrsEntropyNumber E δ ≤ 4 * (δ : ENNReal)⁻¹ := by
    calc
      brrsEntropyNumber E δ ≤
          brrsEntropyNumber (E ∩ Auto.Spherical.LegendreAssouad.brrsInterval 1 1) δ := by
        apply Auto.Spherical.LegendreAssouad.brrsEntropyNumber_mono
        intro x hx
        refine ⟨hx, ?_⟩
        change 1 ≤ x ∧ x ≤ 1 + 1
        norm_num
        exact hE hx
      _ ≤ 4 * (δ : ENNReal)⁻¹ :=
        Auto.Spherical.LegendreAssouad.brrsEntropyNumber_inter_interval_le_four_mul_inv E
          hδpos hδle (le_refl _)
  let δ' : NNReal := ⟨dyadicTimeScale j / 2, by
    unfold dyadicTimeScale
    exact (div_pos (inv_pos.mpr
      (pow_pos (by norm_num : (0 : Real) < 2) _))
      (by norm_num : (0 : Real) < 2)).le⟩
  have hδeq : δ' = δ := by
    dsimp [δ, δ']
    exact brrsDyadicEntropyScale_eq_dyadicMultiplicativeScale_succ j
  have hcard : (T.card : ENNReal) ≤ brrsEntropyNumber E δ' := by
    simpa only [δ'] using dyadicDiscretization_card_le_brrsEntropyNumber_half_scale hT
  calc
    (T.card : ENNReal) ≤ brrsEntropyNumber E δ' := hcard
    _ = brrsEntropyNumber E δ := by rw [hδeq]
    _ ≤ 4 * (δ : ENNReal)⁻¹ := hentropy
    _ = 8 * (2 : ENNReal) ^ j := by
      dsimp [δ, Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale]
      rw [ENNReal.inv_pow, ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0),
        inv_inv, pow_succ]
      norm_num
      ring

/-- The inverse of the standard dyadic entropy scale has precisely the
expected real power after taking an `ENNReal` exponent. -/
theorem toReal_inv_rpow_dyadicMultiplicativeScale (n : Nat) (q : Real) :
    (((Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale n : ENNReal)⁻¹) ^ q).toReal =
      (2 : Real) ^ ((n : Real) * q) := by
  rw [← ENNReal.toReal_rpow]
  dsimp [Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale]
  rw [ENNReal.inv_pow, ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0), inv_inv]
  rw [ENNReal.toReal_pow]
  norm_num
  rw [Real.rpow_natCast_mul (by norm_num : (0 : Real) ≤ 2)]

/-- Real-valued form of the preceding uniform dyadic cardinality bound. -/
theorem dyadicDiscretization_card_le_eight_mul_two_rpow_of_subset_Icc
    {E : Set Real} (hE : E ⊆ Icc (1 : Real) 2) (j : Nat) (T : Finset Real)
    (hT : IsDyadicDiscretization E j T) :
    (T.card : Real) ≤ 8 * (2 : Real) ^ (j : Real) := by
  have h := dyadicDiscretization_card_le_eight_mul_two_pow_of_subset_Icc hE j T hT
  have htop : 8 * (2 : ENNReal) ^ j ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num))
  have hreal := (ENNReal.toReal_le_toReal (by simp) htop).mpr h
  simpa only [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, Real.rpow_natCast] using hreal

/-- The literal zero-penalty BRRS entropy value controls every dyadic
discretization with the expected power, after one fixed constant absorbs the
finitely many pre-asymptotic scales. -/
theorem exists_dyadicDiscretization_card_le_square_mul_two_rpow_of_brrsLegendreAssouad_lt
    {E : Set Real} {q : Real} (hE : E ⊆ Icc (1 : Real) 2)
    (hνq : brrsLegendreAssouadFunction E 0 < q) (hq : 0 ≤ q) :
    ∃ L : Real, 0 < L ∧ ∀ j : Nat, 1 ≤ j → ∀ T : Finset Real,
      IsDyadicDiscretization E j T →
        (T.card : Real) ≤ L ^ 2 * (2 : Real) ^ ((j : Real) * q) := by
  obtain ⟨J, hJ⟩ :=
    exists_tail_dyadicDiscretization_card_le_inv_rpow_of_brrsLegendreAssouad_lt
      hE hνq
  let L : Real := 1 + 8 * (2 : Real) ^ (J : Real) + (2 : Real) ^ q
  have hLone : 1 ≤ L := by
    dsimp [L]
    have hpowJ : 0 ≤ (2 : Real) ^ (J : Real) := Real.rpow_nonneg (by norm_num) _
    have hpowq : 0 ≤ (2 : Real) ^ q := Real.rpow_nonneg (by norm_num) _
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hLq : (2 : Real) ^ q ≤ L ^ 2 := by
    have : (2 : Real) ^ q ≤ L := by
      dsimp [L]
      have hpowJ : 0 ≤ (2 : Real) ^ (J : Real) := Real.rpow_nonneg (by norm_num) _
      linarith
    exact this.trans hLsq
  have hLgrid : 8 * (2 : Real) ^ (J : Real) ≤ L ^ 2 := by
    have : 8 * (2 : Real) ^ (J : Real) ≤ L := by
      dsimp [L]
      have hpowq : 0 ≤ (2 : Real) ^ q := Real.rpow_nonneg (by norm_num) _
      linarith
    exact this.trans hLsq
  refine ⟨L, hLpos, ?_⟩
  intro j _hj T hT
  by_cases hlarge : J ≤ j
  · have htail := hJ j hlarge T hT
    have hscale_pos :
        0 < Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1) :=
      Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale_pos (j + 1)
    have htop :
        ((Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1) : ENNReal)⁻¹) ^ q ≠ ⊤ := by
      apply ENNReal.rpow_ne_top_of_ne_zero
      · exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
      · exact ENNReal.inv_ne_top.mpr
          (ENNReal.coe_ne_zero.mpr (by exact_mod_cast hscale_pos.ne'))
    have htailReal : (T.card : Real) ≤
        (((Auto.Spherical.LegendreAssouad.dyadicMultiplicativeScale (j + 1) : ENNReal)⁻¹) ^ q).toReal := by
      have := (ENNReal.toReal_le_toReal (by simp) htop).mpr htail
      simpa only [ENNReal.toReal_natCast] using this
    rw [toReal_inv_rpow_dyadicMultiplicativeScale] at htailReal
    have hsplit : ((j + 1 : Nat) : Real) * q = q + (j : Real) * q := by
      push_cast
      ring
    calc
      (T.card : Real) ≤ (2 : Real) ^ (((j + 1 : Nat) : Real) * q) := htailReal
      _ = (2 : Real) ^ q * (2 : Real) ^ ((j : Real) * q) := by
        rw [hsplit, Real.rpow_add (by norm_num : (0 : Real) < 2)]
      _ ≤ L ^ 2 * (2 : Real) ^ ((j : Real) * q) :=
        mul_le_mul_of_nonneg_right hLq (Real.rpow_nonneg (by norm_num) _)
  · have hjJ : j ≤ J := Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hgrid := dyadicDiscretization_card_le_eight_mul_two_rpow_of_subset_Icc hE j T hT
    have hpow : (2 : Real) ^ (j : Real) ≤ (2 : Real) ^ (J : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hjJ)
    have hpre : (T.card : Real) ≤ 8 * (2 : Real) ^ (J : Real) := by
      calc
        (T.card : Real) ≤ 8 * (2 : Real) ^ (j : Real) := hgrid
        _ ≤ 8 * (2 : Real) ^ (J : Real) :=
          mul_le_mul_of_nonneg_left hpow (by norm_num)
    have hqj : 0 ≤ (j : Real) * q :=
      mul_nonneg (Nat.cast_nonneg _) hq
    have hfactor : 1 ≤ (2 : Real) ^ ((j : Real) * q) :=
      Real.one_le_rpow (by norm_num) hqj
    calc
      (T.card : Real) ≤ 8 * (2 : Real) ^ (J : Real) := hpre
      _ ≤ L ^ 2 := hLgrid
      _ ≤ L ^ 2 * (2 : Real) ^ ((j : Real) * q) :=
        le_mul_of_one_le_right (sq_nonneg L) hfactor

/-- The literal BRRS Schwartz-core upper bound at the fixed-time endpoint
`p = 2`.  Its exponent is exactly `ν_E^♯(0) / 2`, with the required
arbitrarily small loss.  This uses only Plancherel, finite summation, and the
literal entropy definition; it deliberately makes no claim for `p > 2`. -/
theorem brrsTheoremOneSchwartzCoreStatement_p_two
    (d : Nat) (Φ : BRRSAnnularCutoff) (E : Set Real)
    (hd : 2 ≤ d) (hE : E ⊆ Icc (1 : Real) 2) :
    BRRSTheoremOneSchwartzCoreStatement d Φ E 2 := by
  unfold BRRSTheoremOneSchwartzCoreStatement BRRSTheoremOneSchwartzCoreStatementFor
  refine ⟨hd, hE, by norm_num, ?_⟩
  intro ε hε
  let s : Real := brrsLegendreAssouadFunction E 0 / 2 + ε
  have hs : criticalExponent brrsLegendreAssouadFunction E d 2 + ε = s := by
    dsimp [s, criticalExponent, sobolevExponent]
    ring
  rw [hs]
  by_cases hEnonempty : E.Nonempty
  · have hνnonneg : 0 ≤ brrsLegendreAssouadFunction E 0 :=
      Auto.Spherical.LegendreAssouad.brrsLegendreAssouadFunction_nonneg_of_nonempty
        hEnonempty (by norm_num)
    have hνlt : brrsLegendreAssouadFunction E 0 < 2 * s := by
      dsimp [s]
      linarith
    have hq : 0 ≤ 2 * s := by
      dsimp [s]
      linarith
    obtain ⟨L, hLpos, hcard⟩ :=
      exists_dyadicDiscretization_card_le_square_mul_two_rpow_of_brrsLegendreAssouad_lt
        hE hνlt hq
    let M : Real := SchwartzMap.seminorm Complex 0 0 Φ.symbol
    have hM : 0 ≤ M := by
      dsimp [M]
      exact (norm_nonneg (Φ.symbol 0)).trans
        (SchwartzMap.norm_le_seminorm Complex Φ.symbol 0)
    let K : Real := (M + 1) * L
    have hKpos : 0 < K := by
      dsimp [K]
      exact mul_pos (by linarith) hLpos
    refine ⟨K, hKpos, ?_⟩
    intro j hj T hT f _hf
    have hcardj : (T.card : Real) ≤
        L ^ 2 * (2 : Real) ^ ((j : Real) * (2 * s)) :=
      hcard j hj T hT
    have hpow : (2 : Real) ^ ((j : Real) * (2 * s)) =
        ((2 : Real) ^ ((j : Real) * s)) ^ 2 := by
      rw [show (j : Real) * (2 * s) = ((j : Real) * s) * 2 by ring,
        Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
      exact Real.rpow_two _
    have hcardj' : (T.card : Real) ≤
        L ^ 2 * ((2 : Real) ^ ((j : Real) * s)) ^ 2 := by
      rw [← hpow]
      exact hcardj
    have hRnonneg : 0 ≤ (2 : Real) ^ ((j : Real) * s) :=
      Real.rpow_nonneg (by norm_num) _
    have hcoef : M ^ 2 * (T.card : Real) ≤
        (K * (2 : Real) ^ ((j : Real) * s)) ^ 2 := by
      have hbase_nonneg : 0 ≤ M * L * (2 : Real) ^ ((j : Real) * s) :=
        mul_nonneg (mul_nonneg hM hLpos.le) hRnonneg
      have hbase_le : M * L * (2 : Real) ^ ((j : Real) * s) ≤
          (M + 1) * L * (2 : Real) ^ ((j : Real) * s) := by
        gcongr
        linarith
      have hsq : (M * L * (2 : Real) ^ ((j : Real) * s)) ^ 2 ≤
          ((M + 1) * L * (2 : Real) ^ ((j : Real) * s)) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self hbase_nonneg hbase_le
      calc
        M ^ 2 * (T.card : Real) ≤
            M ^ 2 * (L ^ 2 * ((2 : Real) ^ ((j : Real) * s)) ^ 2) :=
          mul_le_mul_of_nonneg_left hcardj' (sq_nonneg M)
        _ = (M * L * (2 : Real) ^ ((j : Real) * s)) ^ 2 := by ring
        _ ≤ ((M + 1) * L * (2 : Real) ^ ((j : Real) * s)) ^ 2 := hsq
        _ = (K * (2 : Real) ^ ((j : Real) * s)) ^ 2 := by
          dsimp [K]
    have hinput : 0 ≤ ∫ x : BRRSSpace d, ‖f x‖ ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    simp only [ENNReal.ofReal_ofNat]
    change discreteLpNorm 2 T (fun t => brrsDyadicHalfWave Φ j t f) ≤
      ENNReal.ofReal (K * (2 : Real) ^ ((j : Real) * s)) *
        eLpNorm (f : BRRSSpace d → Complex) 2 volume
    apply discreteLpNorm_two_le_of_l2Energy_le
      T (fun t => brrsDyadicHalfWave Φ j t f) (f : BRRSSpace d → Complex)
    · intro t ht
      exact brrsDyadicHalfWave_memLp_two Φ j t f
    · exact f.memLp 2 volume
    · exact mul_nonneg hKpos.le hRnonneg
    · calc
        (∑ t ∈ T, ∫ x : BRRSSpace d, ‖brrsDyadicHalfWave Φ j t f x‖ ^ 2) ≤
            M ^ 2 * (T.card : Real) * ∫ x : BRRSSpace d, ‖f x‖ ^ 2 := by
          simpa only [M] using brrsDyadicHalfWave_l2Sum_le_card Φ j T f
        _ = (M ^ 2 * (T.card : Real)) * ∫ x : BRRSSpace d, ‖f x‖ ^ 2 := by ring
        _ ≤ (K * (2 : Real) ^ ((j : Real) * s)) ^ 2 *
            ∫ x : BRRSSpace d, ‖f x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef hinput
  · have hEempty : E = ∅ := not_nonempty_iff_eq_empty.mp hEnonempty
    refine ⟨1, by norm_num, ?_⟩
    intro j _hj T hT f _hf
    have hTempty : T = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨t, ht⟩
      have htE : t ∈ E := hT.subset (by simpa using ht)
      rw [hEempty] at htE
      exact (Set.mem_empty_iff_false t).mp htE
    subst T
    simp [discreteLpNorm]

/-- A strict subcritical exponent is realized by the literal BRRS
finite-scale entropy profile at arbitrarily small scales.

This is the metric starting point for the sharpness direction of Theorem
1.1: it converts the limsup definition of `ν_E^♯` into actual scales
on which a lower entropy witness must occur.  No maximal-operator estimate is
used here. -/
theorem frequently_inv_rpow_le_brrsLegendreAssouadProfile_of_lt
    {E : Set Real} (hE : E.Nonempty) {alpha q : Real} (halpha : 0 ≤ alpha)
    (hq : q < brrsLegendreAssouadFunction E alpha) :
    ∃ᶠ delta : NNReal in nhdsWithin (0 : NNReal) (Ioi 0),
      delta ∈ Ioo 0 1 ∧
        ((delta : ENNReal)⁻¹) ^ q ≤
          Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E alpha delta := by
  have htop : Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent E alpha ≠ ⊤ :=
    Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent_ne_top_of_nonneg E halpha
  have hbot : Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent E alpha ≠ ⊥ :=
    Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent_ne_bot_of_nonempty hE alpha
  have hqE : (q : EReal) <
      Auto.Spherical.LegendreAssouad.brrsLegendreAssouadExponent E alpha := by
    rw [← EReal.coe_toReal htop hbot]
    simpa only [Auto.Spherical.LegendreAssouad.brrsLegendreAssouadFunction_eq_exponent_toReal]
      using (show (q : EReal) <
        (Auto.Spherical.LegendreAssouad.brrsLegendreAssouadFunction E alpha : EReal) by
          exact_mod_cast hq)
  have hquot : ∃ᶠ delta : NNReal in nhdsWithin (0 : NNReal) (Ioi 0),
      (q : EReal) < Auto.Spherical.LegendreAssouad.entropyLogQuotient
        (Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E alpha delta) delta := by
    exact Filter.frequently_lt_of_lt_limsup (h := hqE)
  have hsmall : ∀ᶠ delta : NNReal in nhdsWithin (0 : NNReal) (Ioi 0), delta ∈ Ioo 0 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  exact (hquot.and_eventually hsmall).mono fun delta hdelta => by
    refine ⟨hdelta.2, ?_⟩
    exact le_of_lt (lt_of_not_ge fun hle =>
      (not_le_of_gt hdelta.1)
        (Auto.Spherical.LegendreAssouad.entropyLogQuotient_le_of_le_inv_rpow
          hdelta.2.1 hdelta.2.2 hle))

/-- A lower BRRS entropy witness on a bounded time interval can be replaced
by an actual finite separated family of sample times.  The factor two is the
closed-ball convention in `brrsEntropyNumber`: a separation mesh `delta`
controls entropy at covering scale `2 * delta`. -/
theorem exists_isSeparated_finset_card_ge_brrsEntropyNumber_at_twice_scale
    {F : Set Real} (hF : F ⊆ Icc (1 : Real) 2) {delta : NNReal}
    (hdelta : 0 < delta) :
    ∃ T : Finset Real, (↑T : Set Real) ⊆ F ∧ IsSeparated T (delta : Real) ∧
      brrsEntropyNumber F (2 * delta) ≤ (T.card : ENNReal) := by
  obtain ⟨T, hTF, hTsep, hTcard⟩ :=
    Auto.FractalDimensions.exists_strictlySeparated_finset_card_ge_intervalCoveringNumber
      (E := F) (δ := (delta : Real)) hF (by exact_mod_cast hdelta)
  refine ⟨T, hTF, ?_, ?_⟩
  · intro s hs t ht hst
    exact (hTsep hs ht hst).le
  · obtain ⟨centers, hcenters, hcenters_card⟩ :=
      Auto.FractalDimensions.exists_intervalCover_card_eq_intervalCoveringNumber hF
        (show 0 < ((2 * delta : NNReal) : Real) by positivity)
    have hentropy : brrsEntropyNumber F (2 * delta) ≤ (centers.card : ENNReal) :=
      Auto.Spherical.LegendreAssouad.brrsEntropyNumber_le_of_intervalCover hcenters
    calc
      brrsEntropyNumber F (2 * delta) ≤ (centers.card : ENNReal) := hentropy
      _ = ENNReal.ofReal (centers.card : Real) := by simp
      _ = ENNReal.ofReal
          (Auto.FractalDimensions.intervalCoveringNumber F (2 * (delta : Real)) : Real) := by
        rw [hcenters_card]
        norm_cast
      _ ≤ ENNReal.ofReal (T.card : Real) := ENNReal.ofReal_le_ofReal hTcard
      _ = (T.card : ENNReal) := by simp

/-- Every exponent strictly below `ν_E^♯(0)` produces actual local
separated time packets at arbitrarily small scales.

More precisely, the finite family has mesh `delta / 2` and cardinality
strictly larger than `delta⁻¹ ^ q`.  This is the complete metric/entropy
input for the lower-bound construction in BRRS Theorem 1.1; the remaining
sharpness work is analytic, namely constructing a radial input whose
half-wave values see these packets. -/
theorem frequently_exists_local_isSeparated_finset_card_lower_of_lt
    {E : Set Real} (hE : E.Nonempty) (hEIcc : E ⊆ Icc (1 : Real) 2) {q : Real}
    (hq : q < brrsLegendreAssouadFunction E 0) :
    ∃ᶠ delta : NNReal in nhdsWithin (0 : NNReal) (Ioi 0),
      delta ∈ Ioo 0 1 ∧ ∃ a : Real, ∃ R : Icc delta 1, ∃ T : Finset Real,
        (↑T : Set Real) ⊆ E ∩ Auto.Spherical.LegendreAssouad.brrsInterval a (R.1 : Real) ∧
          IsSeparated T ((delta : Real) / 2) ∧
            ((delta : ENNReal)⁻¹) ^ q < (T.card : ENNReal) := by
  let nu : Real := brrsLegendreAssouadFunction E 0
  let q' : Real := (q + nu) / 2
  have hqq' : q < q' := by
    dsimp [q', nu]
    linarith
  have hq'nu : q' < brrsLegendreAssouadFunction E 0 := by
    dsimp [q', nu]
    linarith
  have hprofile := frequently_inv_rpow_le_brrsLegendreAssouadProfile_of_lt
    hE (alpha := 0) (q := q') (by norm_num) hq'nu
  exact hprofile.mono fun delta hdelta => by
    have hinv_one : (1 : ENNReal) < (delta : ENNReal)⁻¹ :=
      ENNReal.one_lt_inv.mpr (by exact_mod_cast hdelta.1.2)
    have hinv_top : (delta : ENNReal)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr
        (ENNReal.coe_ne_zero.mpr (by exact_mod_cast hdelta.1.1.ne'))
    have hpow : ((delta : ENNReal)⁻¹) ^ q < ((delta : ENNReal)⁻¹) ^ q' :=
      ENNReal.rpow_lt_rpow_of_exponent_lt hinv_one hinv_top hqq'
    have hprofile_strict : ((delta : ENNReal)⁻¹) ^ q <
        Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile E 0 delta :=
      hpow.trans_le hdelta.2
    unfold Auto.Spherical.LegendreAssouad.brrsLegendreAssouadProfile at hprofile_strict
    rcases lt_iSup_iff.mp hprofile_strict with ⟨a, ha⟩
    rcases lt_iSup_iff.mp ha with ⟨R, hR⟩
    have hentropy : ((delta : ENNReal)⁻¹) ^ q <
        brrsEntropyNumber (E ∩ Auto.Spherical.LegendreAssouad.brrsInterval a (R.1 : Real))
          delta := by
      simpa using hR
    have hFIcc : E ∩ Auto.Spherical.LegendreAssouad.brrsInterval a (R.1 : Real) ⊆
        Icc (1 : Real) 2 :=
      inter_subset_left.trans hEIcc
    obtain ⟨T, hTsub, hTsep, hTcard⟩ :=
      exists_isSeparated_finset_card_ge_brrsEntropyNumber_at_twice_scale hFIcc
        (delta := delta / 2) (div_pos hdelta.1.1 (by norm_num))
    have hscale : 2 * (delta / 2) = delta := by
      apply NNReal.eq
      ring
    have hTcard' : brrsEntropyNumber
        (E ∩ Auto.Spherical.LegendreAssouad.brrsInterval a (R.1 : Real)) delta ≤
          (T.card : ENNReal) := by
      simpa only [hscale] using hTcard
    refine ⟨hdelta.1, a, R, T, hTsub, ?_, hentropy.trans_le hTcard'⟩
    simpa using hTsep

/-! ### Radial shells for the sharpness packet

Section 3 of BRRS first retains a large half of a separated time packet and
then assigns a thin radial shell to each retained time.  The following
elementary geometry is kept here, next to the entropy witnesses which supply
the packets.  It is independent of the stationary-phase lower bound needed
to put mass on those shells. -/

/-- The open physical-space shell of radii within `width` of `radius`. -/
def brrsRadialShell (d : Nat) (radius width : Real) : Set (BRRSSpace d) :=
  {x | |‖x‖ - radius| < width}

/-- The shell associated with a time `t` and a remote reference time. -/
def brrsTimeRadialShell (d : Nat) (referenceTime t width : Real) :
    Set (BRRSSpace d) :=
  brrsRadialShell d |t - referenceTime| width

/-- Shells with sufficiently separated centre radii are disjoint. -/
theorem disjoint_brrsRadialShell_of_two_mul_le_abs_sub
    {d : Nat} {r s width : Real} (hsep : 2 * width ≤ |r - s|) :
    Disjoint (brrsRadialShell d r width) (brrsRadialShell d s width) := by
  rw [Set.disjoint_left]
  intro x hx hs
  change |‖x‖ - r| < width at hx
  change |‖x‖ - s| < width at hs
  have hxr : |r - ‖x‖| < width := by
    simpa only [abs_sub_comm] using hx
  have hbound : |r - s| ≤ |r - ‖x‖| + |‖x‖ - s| := by
    calc
      |r - s| = |(r - ‖x‖) + (‖x‖ - s)| := by
        congr 1
        ring
      _ ≤ |r - ‖x‖| + |‖x‖ - s| := abs_add_le _ _
  have hlt : |r - s| < 2 * width := by linarith
  exact (not_lt_of_ge hsep) hlt

/-- Once all selected times lie on the same side of the reference time, their
absolute time distances retain their original separation.  Consequently their
thin radial shells are pairwise disjoint. -/
theorem pairwiseDisjoint_brrsTimeRadialShell_of_isSeparated
    {d : Nat} {U : Finset Real} {referenceTime delta width : Real}
    (hsep : IsSeparated U delta)
    (hcentres : ∀ t ∈ U, ∀ u ∈ U,
      |(|t - referenceTime|) - (|u - referenceTime|)| = |t - u|)
    (hwidth : 2 * width ≤ delta) :
    (↑U : Set Real).PairwiseDisjoint
      (fun t => brrsTimeRadialShell d referenceTime t width) := by
  intro t ht u hu htu
  apply disjoint_brrsRadialShell_of_two_mul_le_abs_sub
  calc
    2 * width ≤ delta := hwidth
    _ ≤ |t - u| := hsep ht hu htu
    _ = |(|t - referenceTime|) - (|u - referenceTime|)| :=
      (hcentres t ht u hu).symm

/-- A finite packet in an interval has a half-packet containing at least half
of its points.  The endpoint opposite that half is a remote reference time:
absolute distances from it preserve separation and are at least half the
interval length.  This is the finite geometric selection in BRRS, Section 3. -/
theorem exists_half_brrs_packet_with_remote_reference
    {a R : Real} {T : Finset Real} (hR : 0 ≤ R)
    (hT : (↑T : Set Real) ⊆
      Auto.Spherical.LegendreAssouad.brrsInterval a R) :
    ∃ U : Finset Real, ∃ referenceTime : Real,
      U ⊆ T ∧ T.card ≤ 2 * U.card ∧
        (∀ t ∈ U, R / 2 ≤ |t - referenceTime|) ∧
          (∀ t ∈ U, ∀ u ∈ U,
            |(|t - referenceTime|) - (|u - referenceTime|)| = |t - u|) := by
  classical
  let midpoint : Real := a + R / 2
  let L : Finset Real := T.filter (fun t => t < midpoint)
  let U : Finset Real := T.filter (fun t => midpoint ≤ t)
  have hpartition : T = L ∪ U := by
    apply Finset.ext
    intro t
    simp only [L, U, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ht
      rcases lt_or_ge t midpoint with hlt | hge
      · exact Or.inl ⟨ht, hlt⟩
      · exact Or.inr ⟨ht, hge⟩
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩)
      · exact ht
      · exact ht
  have hdisjoint : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro t htL htU
    have hlt : t < midpoint := (Finset.mem_filter.mp htL).2
    have hge : midpoint ≤ t := (Finset.mem_filter.mp htU).2
    exact (not_le_of_gt hlt) hge
  have hcard : T.card = L.card + U.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisjoint]
  by_cases hLU : L.card ≤ U.card
  · refine ⟨U, a, Finset.filter_subset _ _, ?_, ?_, ?_⟩
    · rw [hcard]
      omega
    · intro t ht
      have hmid : midpoint ≤ t := (Finset.mem_filter.mp ht).2
      have hnonneg : 0 ≤ t - a := by
        dsimp [midpoint] at hmid
        linarith
      rw [abs_of_nonneg hnonneg]
      dsimp [midpoint] at hmid
      linarith
    · intro t ht u hu
      have htmid : midpoint ≤ t := (Finset.mem_filter.mp ht).2
      have humid : midpoint ≤ u := (Finset.mem_filter.mp hu).2
      have ht : 0 ≤ t - a := by
        dsimp [midpoint] at htmid
        linarith
      have hu : 0 ≤ u - a := by
        dsimp [midpoint] at humid
        linarith
      rw [abs_of_nonneg ht, abs_of_nonneg hu]
      congr 1
      ring
  · have hUL : U.card ≤ L.card := Nat.le_of_lt (Nat.lt_of_not_ge hLU)
    refine ⟨L, a + R, Finset.filter_subset _ _, ?_, ?_, ?_⟩
    · rw [hcard]
      omega
    · intro t ht
      change t ∈ T.filter (fun t => t < midpoint) at ht
      have htT : t ∈ T := (Finset.mem_filter.mp ht).1
      have htI : t ∈ Icc a (a + R) := by
        simpa only [Auto.Spherical.LegendreAssouad.brrsInterval] using
          hT (by simpa using htT)
      have hlt : t < midpoint := (Finset.mem_filter.mp ht).2
      have hnonpos : t - (a + R) ≤ 0 := by linarith [htI.2]
      rw [abs_of_nonpos hnonpos]
      dsimp [midpoint] at hlt
      linarith
    · intro t ht u hu
      change t ∈ T.filter (fun t => t < midpoint) at ht
      change u ∈ T.filter (fun u => u < midpoint) at hu
      have htT : t ∈ T := (Finset.mem_filter.mp ht).1
      have huT : u ∈ T := (Finset.mem_filter.mp hu).1
      have htI : t ∈ Icc a (a + R) := by
        simpa only [Auto.Spherical.LegendreAssouad.brrsInterval] using
          hT (by simpa using htT)
      have huI : u ∈ Icc a (a + R) := by
        simpa only [Auto.Spherical.LegendreAssouad.brrsInterval] using
          hT (by simpa using huT)
      have ht : t - (a + R) ≤ 0 := by linarith [htI.2]
      have hu : u - (a + R) ≤ 0 := by linarith [huI.2]
      rw [abs_of_nonpos ht, abs_of_nonpos hu]
      calc
        |-(t - (a + R)) - -(u - (a + R))| = |u - t| := by
          congr 1
          ring
        _ = |t - u| := abs_sub_comm _ _

/-- The preceding half-packet selection converts any separated time packet
into pairwise disjoint physical radial shells.  The width hypothesis is the
sole numerical condition needed for disjointness. -/
theorem exists_half_brrs_packet_with_pairwiseDisjoint_shells
    {d : Nat} {a R delta width : Real} {T : Finset Real} (hR : 0 ≤ R)
    (hT : (↑T : Set Real) ⊆
      Auto.Spherical.LegendreAssouad.brrsInterval a R)
    (hsep : IsSeparated T delta) (hwidth : 2 * width ≤ delta) :
    ∃ U : Finset Real, ∃ referenceTime : Real,
      U ⊆ T ∧ T.card ≤ 2 * U.card ∧
        (∀ t ∈ U, R / 2 ≤ |t - referenceTime|) ∧
          (↑U : Set Real).PairwiseDisjoint
            (fun t => brrsTimeRadialShell d referenceTime t width) := by
  rcases exists_half_brrs_packet_with_remote_reference hR hT with
    ⟨U, referenceTime, hUT, hcard, hremote, hcentres⟩
  refine ⟨U, referenceTime, hUT, hcard, hremote, ?_⟩
  exact pairwiseDisjoint_brrsTimeRadialShell_of_isSeparated
    (fun t ht u hu htu => hsep (hUT ht) (hUT hu) htu)
    hcentres hwidth

/-- The entropy lower witnesses for `ν_E^♯(0)` therefore yield, at
arbitrarily fine scales, a half-packet of comparable cardinality whose
BRRS radial shells are pairwise disjoint.  This is precisely the geometric
input used by the radial test function in BRRS, Section 3; the remaining
analytic issue is the stationary-phase lower bound on each displayed shell. -/
theorem frequently_exists_local_half_packet_with_pairwiseDisjoint_shells_of_lt
    {d : Nat} {E : Set Real} (hE : E.Nonempty) (hEIcc : E ⊆ Icc (1 : Real) 2)
    {q : Real} (hq : q < brrsLegendreAssouadFunction E 0) :
    ∃ᶠ delta : NNReal in nhdsWithin (0 : NNReal) (Ioi 0),
      delta ∈ Ioo 0 1 ∧ ∃ a : Real, ∃ R : Icc delta 1, ∃ U : Finset Real,
        ∃ referenceTime : Real,
          (↑U : Set Real) ⊆
              E ∩ Auto.Spherical.LegendreAssouad.brrsInterval a (R.1 : Real) ∧
            ((delta : ENNReal)⁻¹) ^ q < (2 : ENNReal) * (U.card : ENNReal) ∧
              (∀ t ∈ U, (R.1 : Real) / 2 ≤ |t - referenceTime|) ∧
                (↑U : Set Real).PairwiseDisjoint
                  (fun t => brrsTimeRadialShell d referenceTime t ((delta : Real) / 16)) := by
  exact (frequently_exists_local_isSeparated_finset_card_lower_of_lt hE hEIcc hq).mono
    fun delta hdelta => by
      rcases hdelta with ⟨hdeltaIoo, a, R, T, hTsub, hTsep, hTcard⟩
      have hRnonneg : 0 ≤ (R.1 : Real) := by
        have hRnonnegNN : (0 : NNReal) ≤ R.1 :=
          (le_of_lt hdeltaIoo.1).trans R.2.1
        exact_mod_cast hRnonnegNN
      have hdeltanonneg : 0 ≤ (delta : Real) := by
        exact_mod_cast (le_of_lt hdeltaIoo.1)
      have hwidth : 2 * ((delta : Real) / 16) ≤ (delta : Real) / 2 := by
        linarith
      obtain ⟨U, referenceTime, hUT, hcard, hremote, hshells⟩ :=
        exists_half_brrs_packet_with_pairwiseDisjoint_shells
          (d := d) hRnonneg (hTsub.trans inter_subset_right) hTsep hwidth
      have hUsub : (↑U : Set Real) ⊆
          E ∩ Auto.Spherical.LegendreAssouad.brrsInterval a (R.1 : Real) := by
        intro t ht
        exact hTsub (by simpa using hUT ht)
      have hcardENN : (T.card : ENNReal) ≤
          (2 : ENNReal) * (U.card : ENNReal) := by
        exact_mod_cast hcard
      exact ⟨hdeltaIoo, a, R, U, referenceTime, hUsub,
        hTcard.trans_le hcardENN, hremote, hshells⟩

/-! ### Exact radial Fourier test packet

The next construction is the literal phase-shifted radial input used before
the Bessel/stationary-phase calculation in BRRS, Section 3.  It records only
the exact Fourier identity.  In particular, it makes no lower-bound claim on
the shells constructed above. -/

/-- Half-wave phases form the expected one-parameter multiplicative group. -/
theorem halfWaveMultiplier_add {d : Nat} (s t : Real) (xi : BRRSSpace d) :
    halfWaveMultiplier (d := d) (s + t) xi =
      halfWaveMultiplier s xi * halfWaveMultiplier t xi := by
  unfold halfWaveMultiplier
  rw [show (2 * Real.pi * (s + t) * ‖xi‖ : Real) =
      2 * Real.pi * s * ‖xi‖ + 2 * Real.pi * t * ‖xi‖ by ring,
    Complex.ofReal_add, add_mul, Complex.exp_add]

/-- The radial Schwartz datum whose Fourier transform is the annular symbol
back-propagated from `referenceTime`. -/
noncomputable def brrsRadialHalfWaveTestPacket {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (referenceTime : Real) : BRRSSchwartz d :=
  𝓕⁻ (brrsDyadicHalfWaveSchwartzSymbol Φ j (-referenceTime))

/-- The Fourier transform of the test packet is exactly its prescribed
back-propagated annular symbol. -/
theorem brrsRadialHalfWaveTestPacket_fourier_apply {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (referenceTime : Real) (xi : BRRSSpace d) :
    𝓕 (brrsRadialHalfWaveTestPacket Φ j referenceTime : BRRSSpace d → Complex) xi =
      brrsDyadicHalfWaveSymbol Φ j (-referenceTime) xi := by
  unfold brrsRadialHalfWaveTestPacket
  rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq,
    brrsDyadicHalfWaveSchwartzSymbol_apply]

/-- The back-propagated Fourier packet remains radial in physical space. -/
theorem brrsRadialHalfWaveTestPacket_isRadial {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (referenceTime : Real) :
    IsRadial (brrsRadialHalfWaveTestPacket Φ j referenceTime : BRRSSpace d → Complex) := by
  apply IsOrthogonallyInvariant.isRadial
  unfold brrsRadialHalfWaveTestPacket
  rw [SchwartzMap.fourierInv_coe]
  apply IsOrthogonallyInvariant.fourierInv
  intro A
  funext xi
  change brrsDyadicHalfWaveSchwartzSymbol Φ j (-referenceTime) (A xi) =
    brrsDyadicHalfWaveSchwartzSymbol Φ j (-referenceTime) xi
  simp only [brrsDyadicHalfWaveSchwartzSymbol_apply, brrsDyadicHalfWaveSymbol]
  have hphase : halfWaveMultiplier (-referenceTime) (A xi) =
      halfWaveMultiplier (-referenceTime) xi := by
    simpa only [Function.comp_apply] using
      congrFun (halfWaveMultiplier_orthogonallyInvariant (-referenceTime) A) xi
  have hmult : brrsDyadicMultiplier Φ j (A xi) = brrsDyadicMultiplier Φ j xi := by
    simpa only [Function.comp_apply] using
      congrFun (brrsDyadicMultiplier_orthogonallyInvariant Φ j A) xi
  rw [hphase, hmult]

/-- Exact propagated-packet identity.  The output is the inverse Fourier
transform of the radial phase at the relative time `t - referenceTime` times
the square of the fixed annular multiplier.  Establishing a quantitative
lower bound for this integral on the radial shells is the separate
stationary-phase step not asserted here. -/
theorem brrsDyadicHalfWave_radialTestPacket_eq_fourierInv {d : Nat}
    (Φ : BRRSAnnularCutoff) (j : Nat) (referenceTime t : Real) :
    brrsDyadicHalfWave Φ j t (brrsRadialHalfWaveTestPacket Φ j referenceTime) =
      𝓕⁻ (fun xi : BRRSSpace d =>
        halfWaveMultiplier (t - referenceTime) xi *
          brrsDyadicMultiplier Φ j xi * brrsDyadicMultiplier Φ j xi) := by
  funext x
  unfold brrsDyadicHalfWave
  apply congrArg (fun g : BRRSSpace d → Complex => 𝓕⁻ g x)
  funext xi
  rw [brrsRadialHalfWaveTestPacket_fourier_apply,
    brrsDyadicHalfWaveSymbol]
  have hphase : halfWaveMultiplier t xi * halfWaveMultiplier (-referenceTime) xi =
      halfWaveMultiplier (t - referenceTime) xi := by
    simpa only [sub_eq_add_neg] using
      (halfWaveMultiplier_add t (-referenceTime) xi).symm
  calc
    halfWaveMultiplier t xi * brrsDyadicMultiplier Φ j xi *
        (halfWaveMultiplier (-referenceTime) xi * brrsDyadicMultiplier Φ j xi) =
        (halfWaveMultiplier t xi * halfWaveMultiplier (-referenceTime) xi) *
          brrsDyadicMultiplier Φ j xi * brrsDyadicMultiplier Φ j xi := by ring
    _ = _ := by rw [hphase]

end

/-! ### Interpolation of discrete-output estimates

The output space in the next theorem is intentionally arbitrary.  In the
BRRS application it is the product of a finite time set (with counting
measure) and Euclidean space, whose `L^p` norm is exactly the required
`\ell^p(L^p)` norm.  Thus a lower-exponent discrete estimate and a uniform
fixed-time `L^\infty` estimate can be fed directly into this theorem.

This is only a Riesz--Thorin *transport* theorem: it does not assert either
endpoint estimate for the BRRS half-wave.  The radial kernel estimates needed
to supply the sharp lower endpoint remain a separate analytic task. -/

/-- Interpolate a lower-exponent discrete-output estimate with an `L^∞`
endpoint.  If the two endpoint rates are `2^(j * s₀)` and `2^(j * s∞)`, the
output rate is the convex combination
`2^(j * ((1 - θ) * s₀ + θ * s∞))`, where `θ = 1 - p₀ / p`.

The theorem is formulated for simple-function input because this is the
precise domain of the repository's proved Riesz--Thorin theorem.  An eventual
BRRS application must additionally provide the usual density/extension step
from this core to the intended radial `L^p` input class. -/
theorem highExponent_discreteLpEstimate_of_lower_and_top
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    {p₀ p : Real} (hp₀ : 1 ≤ p₀) (hp₀p : p₀ < p)
    (T : SimpleFunc X Complex → Y → Complex)
    (hT_add : ∀ (f g : SimpleFunc X Complex),
      Integrable f μ → Integrable g μ → T (f + g) = T f + T g)
    (hT_smul : ∀ (c : Complex) (f : SimpleFunc X Complex),
      Integrable f μ → T (c • f) = c • T f)
    (hT_measurable : ∀ (f : SimpleFunc X Complex),
      Integrable f μ → Measurable (T f))
    {A₀ A_top s₀ s_top : Real} (hA₀ : 0 < A₀) (hA_top : 0 < A_top) (j : Nat)
    (hlower : ∀ (f : SimpleFunc X Complex), Integrable f μ →
      eLpNorm (T f) (ENNReal.ofReal p₀) ν ≤
        ENNReal.ofReal (A₀ * (2 : Real) ^ ((j : Real) * s₀)) *
          eLpNorm (f : X → Complex) (ENNReal.ofReal p₀) μ)
    (htop : ∀ (f : SimpleFunc X Complex), Integrable f μ →
      eLpNorm (T f) ⊤ ν ≤
        ENNReal.ofReal (A_top * (2 : Real) ^ ((j : Real) * s_top)) *
          eLpNorm (f : X → Complex) ⊤ μ) :
    ∀ f : SimpleFunc X Complex, Integrable f μ →
      MemLp (T f) (ENNReal.ofReal p) ν ∧
      eLpNorm (T f) (ENNReal.ofReal p) ν ≤
        ENNReal.ofReal
          ((Real.rpow A₀ (1 - (1 - p₀ / p)) * Real.rpow A_top (1 - p₀ / p)) *
            (2 : Real) ^ ((j : Real) * ((1 - (1 - p₀ / p)) * s₀ +
              (1 - p₀ / p) * s_top))) *
          eLpNorm (f : X → Complex) (ENNReal.ofReal p) μ := by
  let θ : Real := 1 - p₀ / p
  have hp₀pos : 0 < p₀ := lt_of_lt_of_le zero_lt_one hp₀
  have hppos : 0 < p := lt_trans hp₀pos hp₀p
  have hθ0 : 0 < θ := by
    rw [show θ = 1 - p₀ / p by rfl]
    have hdiv : p₀ / p < 1 := (div_lt_one hppos).mpr hp₀p
    linarith
  have hθ1 : θ < 1 := by
    rw [show θ = 1 - p₀ / p by rfl]
    have hdiv : 0 < p₀ / p := div_pos hp₀pos hppos
    linarith
  have hkey : (ENNReal.ofReal p)⁻¹ =
      ENNReal.ofReal (1 - θ) * (ENNReal.ofReal p₀)⁻¹ +
        ENNReal.ofReal θ * (⊤ : ENNReal)⁻¹ := by
    rw [ENNReal.inv_top, mul_zero, add_zero]
    rw [← ENNReal.ofReal_inv_of_pos hppos]
    rw [← ENNReal.ofReal_inv_of_pos hp₀pos]
    have hθ : 1 - θ = p₀ / p := by
      rw [show θ = 1 - p₀ / p by rfl]
      ring
    rw [hθ]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ p₀ / p)]
    congr 1
    field_simp
  have hpow₀ : 0 < (2 : Real) ^ ((j : Real) * s₀) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hpow_top : 0 < (2 : Real) ^ ((j : Real) * s_top) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hM₀ : 0 < A₀ * (2 : Real) ^ ((j : Real) * s₀) := mul_pos hA₀ hpow₀
  have hM_top : 0 < A_top * (2 : Real) ^ ((j : Real) * s_top) :=
    mul_pos hA_top hpow_top
  have hres := Auto.SteinInterpolation.riesz_thorin T
    (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hp₀)
    le_top
    (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hp₀)
    le_top
    (by constructor <;> assumption)
    hkey hkey hT_add hT_smul hT_measurable hM₀ hM_top hlower htop
  have hrate :
      Real.rpow (A₀ * (2 : Real) ^ ((j : Real) * s₀)) (1 - θ) *
          Real.rpow (A_top * (2 : Real) ^ ((j : Real) * s_top)) θ =
        (Real.rpow A₀ (1 - θ) * Real.rpow A_top θ) *
          (2 : Real) ^ ((j : Real) * ((1 - θ) * s₀ + θ * s_top)) := by
    simp only [Real.rpow_eq_pow]
    have htwo : (0 : Real) < 2 := by norm_num
    have htwo_nonneg : (0 : Real) ≤ 2 := htwo.le
    have hpow₀nonneg : 0 ≤ (2 : Real) ^ ((j : Real) * s₀) :=
      (Real.rpow_pos_of_pos htwo _).le
    have hpow_top_nonneg : 0 ≤ (2 : Real) ^ ((j : Real) * s_top) :=
      (Real.rpow_pos_of_pos htwo _).le
    rw [Real.mul_rpow hA₀.le hpow₀nonneg,
      Real.mul_rpow hA_top.le hpow_top_nonneg]
    rw [← Real.rpow_mul htwo_nonneg, ← Real.rpow_mul htwo_nonneg]
    calc
      A₀ ^ (1 - θ) * 2 ^ ((j : Real) * s₀ * (1 - θ)) *
          (A_top ^ θ * 2 ^ ((j : Real) * s_top * θ)) =
        (A₀ ^ (1 - θ) * A_top ^ θ) *
          (2 ^ ((j : Real) * s₀ * (1 - θ)) *
            2 ^ ((j : Real) * s_top * θ)) := by ring
      _ = (A₀ ^ (1 - θ) * A_top ^ θ) *
          2 ^ ((j : Real) * s₀ * (1 - θ) + (j : Real) * s_top * θ) := by
        rw [Real.rpow_add htwo]
      _ = _ := by
        congr 2
        ring
  intro f hf
  have hresf := hres f hf
  rw [hrate] at hresf
  simpa [θ] using hresf

end Auto.Spherical.FractalDilations.BRRS
