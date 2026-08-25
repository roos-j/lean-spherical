# Continuation instructions: Duoandikoetxea--Vega planar formalization

This file records the user's instructions and the current handoff state for a
follow-up agent.  It is a working specification, not a replacement for the
blueprint.

The previous project (Bourgain's circular maximal theorem via
Mockenhaupt--Seeger--Sogge) is finished.  Its public results
`Spherical.eLpNorm_sphericalMaximal_le`,
`Spherical.RestrictedDilations.eLpNorm_restrictedSphericalMaximal_le` and
`Codex.Spherical.Bourgain.bourgainCircularMaximal` are proved and depend only
on the standard axioms.  Do not reopen it.

## Primary objective

Formalize the planar negative-power circular maximal theorem following
`blueprints/duoandikoetxea_vega_planar_blueprint.tex`, and finish only when

* the blueprint's Theorem `thm:direct-missing` is genuinely proved, i.e.
  boundedness of the full circular maximal operator on `L^p(R^2, |x|^a dx)`
  for every real `p > 2` and every `-1 < a < 0`; and
* `Spherical.PowerWeights.closure_typeSet_eq` holds under `2 <= d` with no
  placeholder in its dependency graph.

**Both objectives are met as of 2026-08-25 16:56:40 -0400.**  Both public
statements are in place in `LeanSpherical/Theorems.lean`, the whole chain is
proved, and `#print axioms` reports only `[propext, Classical.choice,
Quot.sound]` for

```
Spherical.PowerWeights.eLpNorm_circularMaximal_powerWeight_le_of_neg
Spherical.PowerWeights.closure_typeSet_eq
```

There is no placeholder left in this project: the former
`Codex.PowerWeights.DuoandikoetxeaVega.hasCriticalWeightBandBound` gap
(the blueprint's `prop:critical-loss` composed with Phase E) is now an
unconditional theorem, proved through `dvCriticalWeightBandBound`.

A follow-up agent should treat the project as **finished** and in maintenance
mode: keep it compiling against Mathlib updates, keep `Status.md` accurate,
and do not add public API.  The only genuinely unformalized item left in the
blueprint ledger is the full source range `-1 < a < p - 2` of
`thm:dv-general`, which the two public targets do not need; formalize it only
if the user asks.

## Required files and namespaces

The whole formalization lives in **one** source file:

* `LeanSpherical/Codex/PowerWeights/DuoandikoetxeaVega.lean`, in namespace
  `Codex.PowerWeights.DuoandikoetxeaVega`.

Do not create companion files for this project.  The blueprint's suggested
`DuoVega/*.lean` split in its "Recommended file structure" section is
explicitly superseded by this single-file requirement; record that deviation
in `ErrorReport.md` rather than acting on it.

`LeanSpherical/Theorems.lean` may contain only the two statement-level entries
already present:

* `Spherical.PowerWeights.eLpNorm_circularMaximal_powerWeight_le_of_neg`
* `Spherical.PowerWeights.closure_typeSet_eq` under `2 <= d`

Both must remain one-line references to declarations in the `Codex` tree.  No
proof text belongs in `Theorems.lean`, and no other change to that file is
authorized.

Documentation files are also required and permitted:

* `Status.md`
* `ErrorReport.md`
* this handoff file, `Instructions.md`.

All new Lean declarations must live under a `Codex` namespace matching their
file path.  Auxiliary declarations that are not blueprint items should use the
`aux_` prefix; the elementary reusable facts (set monotonicity, the dense
radius reduction, the `MemLp` lift) need not.

## Blueprint-order execution (mandatory)

`blueprints/duoandikoetxea_vega_planar_blueprint.tex` is the source of truth
for the proof plan.  Work through its items in their written order.

1. Select one labeled theorem, proposition, or `blueprint` item as the active
   item.  Do not begin work on a later item while that item remains
   unfinished.
2. Finish the active item completely before advancing: give the actual Lean
   proof, compile the source, run the module build, audit its axioms and
   placeholders, check the diff, update the documentation, and remove owned
   scratch material.
3. Foundational work is allowed only when it is demonstrably necessary to the
   active item.  Treat that foundation as part of the same item, finish it,
   then return directly to the active item.
4. Do not add speculative wrappers, consumers, convenience corollaries, or
   side bridges merely because they are easy to formalize.  A declaration is
   in scope only if it is required to finish the active item.
5. `Status.md` is the ledger of blueprint items in blueprint section order.
   It must not track assistant-invented helper theorems or scratch work.

At the start of a work session, identify the earliest unfinished item in
`Status.md`; do not bypass it.  A row listed as `Statement completed` is still
unfinished until an actual unconditional proof of the stated result is in
place.  As of the completion date above no ledger row is unfinished for the two
public targets, so these rules only apply to future extensions.

## Mathematical requirements

* The blueprint's Phase D--E chain, packaged in source as the predicate
  `HasCriticalWeightBandBound`, is proved (see the final-state section below).
  Phase F needs no interpolation theorem: `hasPlanarNegativeRawBandRate_of_criticalWeight`
  combines the critical-weight bound with the unweighted Bourgain gain by a
  single Hoelder inequality with exponents `1/θ` and `1/(1-θ)`, where
  `θ = -a`.  Because that step absorbs any polynomial-in-`j` loss, the open
  predicate is allowed a factor `(j+1)^N` and needs no `2^(eps*j)`
  bookkeeping.
* The route that was used for that predicate, sharper than the blueprint's
  sketch, is recorded in the doc-string of `hasCriticalWeightBandBound` and was
  followed as written:
  1. Sobolev in `r` on an interval of length `2^{-j}` (so no geometric-mean
     Sobolev inequality is needed) reduces the maximal function to the two
     space-time integrals with weights `2^{j}` and `2^{-j}`;
  2. the `r`-integral of `m_j(r,xi) * conj (m_j(r,eta))` against a polynomial
     weight vanishing at the endpoints of `[1/4, 5]` is estimated by ONE
     integration by parts, using the exact planar outgoing/incoming/middle
     normal form `PlanarTripleWaveNormalForm.planarCoordinateSurfaceWaveSum_eq_three_radialTerms`
     and the all-order amplitude bounds in
     `CoordinateWaveSymbolBounds`; the resulting kernel bound is
     `C (s^-1 + t^-1) / (1 + |s - t|)` for comparable `s, t >= 1`;
  3. Schur's test (symmetric form, elementary) turns that into the space-time
     `L^2` bounds, with the output localized at each dyadic distance `2^{-k}`
     from the origin by a bump whose Fourier transform is compactly supported;
     the geometric input is the elementary estimate
     `vol(annulus(a,h) cap ball(xi,R)) <= C R h` for `R <= a/2`, proved by
     Fubini in the frame adapted to `xi`;
  4. summing the shells produces the logarithmic loss, exactly as in the
     source;
  5. Phase E is real interpolation between the resulting `L^2(|x|^{-1})` bound
     and the trivial `L^inf` bound.  Use `Codex.riesz_thorin` from
     `LeanSpherical/Codex/SteinInterpolation.lean` on the operator linearized
     by a measurable radius selector (its endpoints may be `infinity`), or
     Marcinkiewicz for the sublinear operator; in the latter case the operator
     must first be presented as convolution with the Schwartz kernel of the
     multiplier, via
     `SmoothDyadicPhysicalCore.fourierInv_schwartz_multiplier_eq_convolution`
     and
     `GlobalUnweightedEndpoint.exists_schwartz_compactSupport_mul_surfaceFourier`.
     Stein--Weiss interpolation with change of measure is NOT needed anywhere;
     see `ErrorReport.md` entry 13.

### Final state of the Phase D--E chain (2026-08-25 16:56:40 -0400)

Phase D (the weighted `L^2` core) is packaged as `dvWeightedL2Core`:

```
int_{B(0,1/32)} |x|^{-1} (M_{E,j} f)^2 dx <= C (j+1)^2 int |f|^2 dx
```

for every `E` contained in `[1,2]`, every `j >= 3`, and every Schwartz `f`.
Its proof follows the route above: radial Sobolev at scale `2^{-j}` against the
doubly vanishing weight `dvWeight`, `TT*` and Plancherel to a frequency
quadratic form, Schur's test with the polar row estimate (`exists_dvRow_bound`),
the dyadic spatial shells `dvGk` built from the compactly-Fourier-supported
profile `dvGb`, and an `L^2 -> L^inf` bound (`dvSupBound`) for the remaining
small ball.  The three small indices `j <= 2` are covered separately by the
crude bound `dvCrudeL2Core`, whose constant grows like `2^j`.

Phase E is Riesz--Thorin interpolation, `dvCriticalWeightBandBound`.  The
operator is linearized as `dvT` -- a finite sum of indicator-localized band
averages `dvOp` -- with the tie-broken maximizing selection sets `dvSel`, and
`Codex.riesz_thorin` is applied with Lebesgue measure on the input side and
`dvNu = (|x|^{-1} dx)|_{B(0,1/32)}` on the output side, `p_0 = q_0 = 2`,
`p_1 = q_1 = infinity`.  The `L^inf` endpoint is elementary
(`dvT_eLpNorm_top`, from the uniform kernel `L^1` size `dvPsiL1`); the `L^2`
endpoint is Phase D, transported from the Schwartz core to integrable simple
functions by density (`dvT_l2_general`) and back again after interpolation
(`dvT_lp_schwartz`).  An arbitrary radius set is reduced to the dyadic finite
sets `dvR n` by continuity in the radius (`continuousAt_dvSlice`) plus monotone
convergence (`dvMaximal_set_lp`).

* The unweighted endpoint of that interpolation (blueprint
  `bp:bourgain-piece`) is already available and is exposed in source as
  `exists_relativeCircularBandGeometricDecay`.  It is the radius-relative
  Littlewood--Paley band form, which is what the repository's all-radius
  reassembly consumes; do not re-derive an absolute-frequency variant.
* Phases G (frequency summation), H (extension from the Schwartz core) and I
  (globalization over all radii) are already proved in the repository.  They
  are consumed through
  `StrictNegativeEndpoint.hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_uniform_buffered_raw_band_rate_and_unweighted`.
  Do not reformalize them.
* Generalize foundational facts that are not intrinsically planar to ambient
  dimension `d`.  Treat `d = 2` as the downstream specialization.
* Reuse the repository's definitions of spherical averages and maximal
  functions instead of duplicating them.  The convention is `x + t * omega`
  for spherical averages, the sphere measure is normalized, and Mathlib
  Fourier conventions carry the `2 * pi`.
* The power weight is `powerWeight d a = volume.withDensity (norm x ^ a)`.  For
  `a < 0` the density is infinite at the origin, so every density identity
  must be stated almost everywhere; pointwise rewrites at `0` are the wrong
  interface.
* The final theorem must use only standard Lean/Mathlib axioms.  Never add a
  new `sorry`, `admit` or `axiom`, and never introduce a second placeholder.
  Do not use
  `LeanSpherical/Codex/Spherical/FractalDilations/ProofSkeleton.lean`, which
  contains an admitted theorem and is not imported by `LeanSpherical.Theorems`.
* Do not merely state a desired theorem as a `Prop` and mark it proved.

## Documentation requirements

`Status.md` is organized by the blueprint's sections and contains one row per
blueprint item.  Each row records the exact Lean target when one exists, its
status, and a review timestamp.  Use exactly one of:

* `Proof completed` -- an unconditional Lean proof exists;
* `Statement completed` -- the target is correctly formulated but unproved;
* `ToDo` -- not formalized.

The `Reduction completed` value has been retired: the placeholder it referred
to is proved, so every row that used it is now `Proof completed`.  Update the
relevant rows whenever the implementation changes.

Every discrepancy found in the blueprint or while adapting it to Lean must be
recorded in `ErrorReport.md` as a concise but thorough timestamped entry.
Blueprint errors are not a reason to stop; correct them where possible.
`ErrorReport.md` retains the previous project's entries; append new ones under
the Duoandikoetxea--Vega heading.

## Source verification commands

Always compile source files, rather than relying on old `.olean` artifacts.
On this Windows workspace the normal commands are:

```powershell
lake env lean -o .lake\build\lib\lean\LeanSpherical\Codex\PowerWeights\DuoandikoetxeaVega.olean LeanSpherical\Codex\PowerWeights\DuoandikoetxeaVega.lean
lake env lean LeanSpherical\Theorems.lean
lake build LeanSpherical
```

The last command also prints the axiom audit for the public theorems through
`LeanSpherical.lean`.  Every public theorem, `closure_typeSet_eq` included,
must now report only `propext`, `Classical.choice` and `Quot.sound`; a
`sorryAx` anywhere is a regression.  Also run `git diff --check` and scan the
repository for `sorry`, `admit` and `axiom`: the expected count outside
`ProofSkeleton.lean` is zero.

## Formalization discipline

* Complete one source transaction at a time; the project file will grow, so
  land edits in small UTF-8 chunks and direct-compile after each.
* State reusable foundations in arbitrary Euclidean dimension and for the
  natural exponent range whenever the proof does not genuinely use a planar or
  endpoint-specific feature.
* Keep the blueprint ledger current.  Do not add a "progress notes" section
  and do not track declarations that are not blueprint items.
* Edit Lean and Markdown source only through `apply_patch`; use PowerShell for
  read-only inspection and compilation.  This preserves the project's UTF-8
  mathematical notation during long proof transfers.
* Never run a git history command.  Leave the work uncommitted and hand the
  user the exact commands.

## Current verified state

`LeanSpherical/Codex/PowerWeights/DuoandikoetxeaVega.lean` compiles and its
module build passes.  It contains, in blueprint order:

* the radius-set monotonicity layer for the public `ENNReal`-valued maximal
  function `Spherical.M` (`restrictedSphericalMaximal_mono`,
  `eLpNorm_restrictedSphericalMaximal_mono`,
  `memLp_restrictedSphericalMaximal_of_le`);
* Phase A: the local operator `localCircularMaximal`, the dense-radius
  reduction `restrictedSphericalMaximal_eq_of_subset_closure` (which converts
  the continuum supremum over `[1,2]` into a supremum over any dense subset,
  in particular the rationals, for continuous inputs), and the countable
  exhaustion `restrictedSphericalMaximal_iUnion`;
* the arithmetic bridge of blueprint section 3:
  `neg_one_lt_alpha_of_planar_strict` and `alpha_lt_p_sub_two`, together with
  the Phase F exponent choice `exists_pos_interpolated_gain`;
* Phase C: `exists_relativeCircularBandGeometricDecay`, the unconditional
  unweighted relative-band gain inherited from `Codex.Spherical.Bourgain`;
* the packaged Phase D--F predicate `HasPlanarNegativeRawBandRate`, now proved
  through `hasPlanarNegativeRawBandRate_of_criticalWeight`;
* the Schwartz-core estimate
  `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_negative_of_gt_two`
  for an arbitrary radius set, obtained from the critical-weight band bound,
  the unweighted planar Bourgain bound and the repository's buffered raw-band
  reassembly;
* Phase H: `exists_powerWeight_bound_of_strongType`, the lift of a
  Schwartz-core weighted bound to every `MemLp` input;
* the public planar theorems
  `eLpNorm_circularMaximal_powerWeight_le_of_neg` (`thm:direct-missing`),
  `eLpNorm_restrictedCircularMaximal_powerWeight_le_of_neg` (blueprint
  Appendix B) and `eLpNorm_localCircularMaximal_powerWeight_le_of_neg`
  (`thm:minimal-local`);
* the planar unweighted input
  `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_zero_planar_of_sww`,
  which replaces the `d >= 3` Stein input by the repository's
  Seeger--Wainger--Wright theorem and is valid at every exponent above the
  critical one;
* `prop:high-p-branch` and the planar strict-upper case split
  `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_of_strict_implicit`;
* the planar main theorem `power_weight_spherical_maximal_main_planar` and the
  `2 <= d` closure theorem `closure_typeSet_eq`.

## Key reusable interfaces

* `Spherical.sphericalAverage`, `Spherical.M`,
  `Spherical.PowerWeights.powerWeight` and `Spherical.PowerWeights.typeSet`
  are the public objects.
* `Codex.Spherical.PowerWeights.PowerWeightTheorem.restrictedSphericalMaximal_eq_restrictedNormalizedSphericalMaximal`
  bridges the public and internal maximal functions.
* `Codex.Spherical.PowerWeights.RawLpLift.memLp_restrictedSphericalMaximal_of_memLp_of_schwartz_bound`
  lifts a finite-exponent Schwartz core to arbitrary `MemLp` input.
* `Codex.Spherical.PowerWeights.LocalizedUpper.restrictedRelativeBandpassSphericalMaximal`
  is the literal radius-relative Littlewood--Paley band of the circular means;
  the blueprint's `M_j` should always be read as this operator.
* `Codex.Spherical.PowerWeights.LocalBlocks.normalizedRadiusBlock E R` is the
  blueprint's normalized slice contained in `[1,2]`.
* `Codex.Spherical.PowerWeights.AnnularWeight.euclideanAnnulus` and
  `Codex.Spherical.PowerWeights.Entropy.dyadicMultiplicativeScale` supply the
  spatial annuli and the factor `2^-j` of the raw band rate.
* `Codex.Spherical.Bourgain.HasRelativeCircularBandGeometricDecay` is the
  frequency-localized unweighted gain; `Codex.Spherical.MSS` supplies the
  underlying `p = 4` local smoothing.
* `Codex.Spherical.RieszThorin` and `Codex.Spherical.InterpolationCore` are
  the available interpolation machinery.  There is **no** Stein--Weiss
  change-of-measure theorem in the repository yet; it must be proved as part
  of Phase F, and it should be stated as a reusable result rather than inlined.

## Known blockers and pitfalls

* The planar range genuinely needs a new analytic estimate.  For `d = 2` the
  parameter reduction
  `HigherPParameters.exists_strict_powerWeightEntropyImplicitCondition_subtwo_of_neg`
  needs `d - 1 >= 2` and therefore fails; and for a radius set of full
  Minkowski exponent there are no admissible subquadratic points at all, so no
  amount of interpolation between existing results reaches `p > 2`, `a < 0`.
  Do not try to obtain it by convexity of the type set.
* Only `p = 2` of the negative planar branch was previously reachable, through
  `StrictNegativeHigher.hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_of_strict_negative_two_of_subquadratic`.
  That route does not extend above `p = 2`.
* A naive Hoelder argument on dyadic spatial annuli reduces the weighted band
  estimate to an `L^p -> L^q` improving bound with `q` just below `2p`.  The
  radial focusing example (a thin annulus of width `rho` centred on the
  origin) shows `q <= 2p` is sharp, and for `p` near `2` Schlag's local
  circular improving region does not reach the required exponent.  The
  critical-weight estimate cannot be avoided this way.
* Bernstein's inequality gives only the lossy bound
  `norm(M_j f, L^inf) <= C * 2^(2j/p) * norm(f, L^p)`, which after
  interpolation with the unweighted gain covers only `a` close to `0`.  It is
  not a proof of the full range.
* The maximal operator is sublinear, so complex interpolation must be applied
  to the linear finite-grid vector-valued maps `f -> (A_t P_j f)` indexed by a
  finite `F` contained in the rationals of `[1,2]`, uniformly in `F`, and only
  then passed to the supremum.  The dense-radius reduction and the countable
  exhaustion needed for that limit are already in source.
* `ENNReal` negative real powers can produce `top` at the origin.  Keep every
  power-weight almost-everywhere lemma inside the project file's weight
  section.
* `2 < p` for `p : ENNReal` does not imply `p` finite; the public API
  therefore carries `hp_top` explicitly.
* The endpoint `a = -1` is not needed as an analytic theorem.  Where it lies
  on the admissible boundary it is recovered by the closure argument.  Do not
  attempt Lee's endpoint theory.

## Completed proof route (for the record)

The route actually taken, in the order it was landed:

1. Phase D, the blueprint's annular decomposition and `prop:critical-loss` in
   the form of the weighted `L^2` estimate `dvWeightedL2Core`, uniformly in the
   radius set and with a polynomial loss `(j+1)^2` rather than `2^(eps j)`:
   radial Sobolev at scale `2^{-j}` against the doubly vanishing weight,
   `TT*` and Plancherel, the oscillatory kernel bound
   `C (s^-1 + t^-1)/(1 + |s - t|)`, Schur's test with the polar row estimate,
   dyadic spatial shells, and the small-ball `L^2 -> L^inf` term.
2. Phase E, the fixed-exponent interpolation `dvCriticalWeightBandBound`:
   linearize by a measurable radius selection (`dvT`, `dvSel`), present the
   band average as a convolution (`dvOp`, `dvKerS`), interpolate with
   `Codex.riesz_thorin` between `L^2(dx) -> L^2(|x|^{-1} dx|_{B(0,1/32)})` and
   `L^inf -> L^inf`, transport across the two density steps, and pass from the
   dyadic finite radius sets to an arbitrary radius set by monotone
   convergence.  The small indices `j <= 2` use `dvCrudeL2Core`.
3. Phase F was already available: `hasPlanarNegativeRawBandRate_of_criticalWeight`
   combines the critical-weight bound with the unweighted Bourgain gain by one
   Hoelder inequality, and absorbs the polynomial loss.
4. Phases G--I are the repository's buffered raw-band reassembly, consumed
   through
   `StrictNegativeEndpoint.hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_uniform_buffered_raw_band_rate_and_unweighted`.
5. Final verification (2026-08-25 16:56:40 -0400): full `lake build`,
   `git diff --check`, a repository-wide `sorry`/`admit`/`axiom` scan, and the
   axiom audit of both public theorems.

Optional future work, only if the user asks: the blueprint's `thm:dv-general`
in its full planar weight range `-1 < a < p - 2` requires, in addition, the
nonnegative branch for the full radius set, i.e. the computation of the
Minkowski exponent of `(0, inf)` together with the corresponding
Legendre--Assouad values.  It is not needed for either public target.
