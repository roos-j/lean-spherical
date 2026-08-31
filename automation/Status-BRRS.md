# BRRS formalization status

Last updated: 2026-08-31

This file tracks the formalization of Beltran--Roos--Rutar--Seeger,
[*A fractal local smoothing problem for the wave equation*](https://arxiv.org/abs/2501.12805).

**BRRS Theorem 1.2 is complete.**  The combined unconditional Lean theorem is
`Auto.Spherical.LegendreAssouad.brrsTheoremOnePointTwo`.

**BRRS Theorem 1.1 is not yet complete.**  Its literal full statement is
represented in Lean, and several genuine analytic and geometric components
are now proved, but the all-`L^p` radial estimate and the sharpness
construction remain open.  Declarations whose names end in `Statement` are
`Prop` definitions, not theorem proofs.

Status values:

* `Proof completed` -- an unconditional Lean proof exists.
* `Partial proof` -- a mathematically relevant component is proved, but not
  the full paper theorem.
* `Statement completed` -- the target is represented in Lean but unproved.
* `ToDo` -- necessary infrastructure or a proof is still absent.

## Public targets

| Paper result | Lean target | Status |
| --- | --- | --- |
| Theorem 1.1: radial fractal local smoothing, including sharpness | `Auto.Spherical.FractalDilations.BRRS.BRRSTheoremOneWithSharpnessStatement` | Statement completed |
| Theorem 1.1: concrete all-`L^p` realization of the localized half-wave | `Auto.Spherical.FractalDilations.BRRS.brrsLpHalfWaveExtension` | Proof completed |
| Theorem 1.1: fixed-time convolution endpoint | `Auto.Spherical.FractalDilations.BRRS.norm_brrsLpHalfWaveExtension_apply_le_kernelMass_mul_bound` | Partial proof |
| Theorem 1.1, `p = 2` Schwartz-core upper bound | `Auto.Spherical.FractalDilations.BRRS.brrsTheoremOneSchwartzCoreStatement_p_two` | Partial proof |
| Theorem 1.1: radial-polar half-wave representation | `Auto.Spherical.FractalDilations.BRRS.brrsDyadicHalfWave_eq_surfaceFourier_integral_of_radialProfile` | Partial proof |
| Theorem 1.1: radial-input polar half-wave identity | `Auto.Spherical.FractalDilations.BRRS.brrsDyadicHalfWave_eq_surfaceFourier_integral_of_isRadial` | Partial proof |
| Theorem 1.1: stationary surface-wave normal forms | `Auto.Spherical.FractalDilations.BRRS.brrs_surfaceFourier_eq_stationaryWaveSum`, `Auto.Spherical.FractalDilations.BRRS.brrs_surfaceFourier_two_eq_stationaryWaveSum` | Partial proof |
| Theorem 1.1: metric lower witnesses for sharpness | `Auto.Spherical.FractalDilations.BRRS.frequently_exists_local_isSeparated_finset_card_lower_of_lt` | Partial proof |
| Theorem 1.2(i): `nu_E^sharp = nu_E^*` | `Auto.Spherical.LegendreAssouad.brrsTheoremOnePointTwoPartOne` | Proof completed |
| Theorem 1.2(ii): characterization of restricted Legendre--Assouad profiles | `Auto.Spherical.LegendreAssouad.brrsTheoremOnePointTwoPartTwo` | Proof completed |
| Theorem 1.2, both clauses | `Auto.Spherical.LegendreAssouad.brrsTheoremOnePointTwo` | Proof completed |

## What is now formalized

* `LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean` gives a literal
  additive-time model of inclusion-maximal `2^-j` discretizations, radiality,
  the half-wave Fourier multiplier, and the paper's nonzero radial smooth
  annular cutoff supported in `(1/4,4)`.  The multiplier includes the required
  `2π` conversion from Mathlib's Fourier variable to the paper's source
  frequency.  It records the finite `ell^p(L^p)` norm, the exponent `s_p`,
  and the full upper-bound/sharpness target of Theorem 1.1.
* `LeanSpherical/Auto/Spherical/LegendreAssouad.lean` now contains the
  historical logarithmic Legendre--Assouad API and all of its operator-free
  entropy geometry previously embedded in the power-weight, Bourgain, and
  AHRS files, together with separate additive-Euclidean BRRS definitions of
  the covering number, `nu_E^sharp`, equality-scale Assouad spectrum, and
  Legendre transform.
  The Theorem 1.2(i) target explicitly requires a nonempty bounded set: with
  the formalized `ENNReal.log` convention, the empty set is degenerate and
  does not satisfy the displayed transform identity.
* `LeanSpherical/Definitions.lean` retains compatibility abbreviations for
  the old project-level names; it does not identify the legacy logarithmic
  model with the literal BRRS additive model.
* Theorem 1.2(i) is proved as the exact identity between the literal BRRS
  entropy profile and the Assouad-spectrum Legendre transform, for nonempty
  bounded time sets.  Theorem 1.2(ii) is also proved in both directions: the
  Rutar realization input is discharged by an exact-hit Moran construction,
  including the zero/nonzero cases and endpoint bookkeeping.
* `LeanSpherical/Auto/ConvexDuality.lean` supplies reusable restricted real
  Fenchel-conjugate tools used by the proof: affine bounds, monotonicity,
  convexity, and endpoint/Lipschitz control under explicit boundedness
  hypotheses.
* `BRRS.lean` proves the literal `p = 2` Schwartz-core upper bound with the
  exact `nu_E^sharp(0) / 2` exponent and arbitrary positive loss.  It also
  packages the compact smooth annular half-wave symbol and proves
  `brrsDyadicHalfWave_eq_convolution`, identifying the literal Schwartz
  half-wave with convolution by the inverse Fourier transform of that symbol.
* The convolution model is now extended to every real `p >= 1` by the
  concrete `brrsLpHalfWaveExtension`.  Its a.e. congruence, Schwartz
  agreement, `L^p` mapping, a.e. linearity, and `L^p` boundedness fields are
  all proved.  The supporting dimension-generic Young inequality includes
  the `p = 1` endpoint.
* The canonical extension has an honest fixed-time `L∞` convolution bound:
  its value is bounded by the `L¹` mass of the actual dyadic kernel times a
  pointwise bound for the input. This is deliberately only a preliminary
  endpoint: no dyadic rate for that kernel mass has been proved.
* `brrsDyadicHalfWave_eq_surfaceFourier_integral_of_radialProfile` rewrites
  the radial Fourier-side half-wave exactly as a polar integral of the
  surface Fourier transform.  This is an exact representation, not a decay
  estimate.
* `BRRS.lean` directly reuses the stationary-phase work in
  `FractalDilations.Auxiliary` to give exact outgoing/incoming/middle
  surface-wave normal forms: `brrs_surfaceFourier_eq_stationaryWaveSum` in
  dimensions at least three, its positive-ray specialization, and
  `brrs_surfaceFourier_two_eq_stationaryWaveSum` for the circle.  These are
  exact identities, not the missing radial kernel estimates.
* The time-set geometry needed for the BRRS upper-bound decomposition is
  formalized: maximal separated sets cover at twice their separation scale,
  entropy bounds their cardinality, and a strict `nu_E^sharp(alpha)` bound
  gives eventual weighted local-cardinality bounds for every dyadic
  discretization, with the half-mesh packing-to-covering shift explicit.
* The sharpness-side metric extraction is also proved: a subcritical
  `nu_E^sharp(0)` exponent yields arbitrarily fine local separated time
  packets with the corresponding cardinality lower bound.  What remains is
  to turn these packets into radial half-wave lower-bound test functions.

## Outstanding proof work

| Required component | Status | Reason |
| --- | --- | --- |
| Theorem 1.1 radial upper bound | ToDo | The all-`L^p` realization and the exact stationary surface-wave reduction are complete, but the dimension-generic Bessel/radial kernel estimate and the weighted one-dimensional argument from the paper's Section 5 are absent. |
| Theorem 1.1 sharpness | ToDo | The metric packet extraction is complete, but the scale-by-scale radial half-wave test-function construction and analytic lower-bound argument are absent. |
| Theorem 1.1 higher-`p` step | ToDo | A fixed-time convolution endpoint is proved, but its kernel mass has no sharp dyadic estimate; the required endpoint rate and interpolation argument remain to be proved. |

The MSS and AHRS developments were audited for reuse.  They provide useful
planar local-smoothing and spherical-maximal estimates, respectively, but do
not yield a sound direct estimate for the raw all-dimensional BRRS half-wave
with the required sharp `nu_E^sharp` dependence.

## Verification status

On 2026-08-31, `LegendreAssouad.lean` and `BRRS.lean` typechecked directly,
`lake build LeanSpherical.Auto.Spherical.FractalDilations.BRRS` succeeded,
and the repository-wide `lake build` succeeded (3,336 jobs).  `#print axioms`
reports only `[propext, Classical.choice,
Quot.sound]` for `brrsTheoremOnePointTwo`, `brrsLpHalfWaveExtension`, the
radial-polar representation, and the sharpness-side metric lower witness.
A source audit finds no literal
`sorry`, `admit`, or `axiom` declaration in `ConvexDuality.lean`,
`LegendreAssouad.lean`, or `BRRS.lean`.
