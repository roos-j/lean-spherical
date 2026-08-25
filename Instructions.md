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

Both public statements are already in place in `LeanSpherical/Theorems.lean`
and the entire reduction is proved.  Exactly one declaration is unproved:

```
Codex.PowerWeights.DuoandikoetxeaVega.exists_planarNegativeRawBandRate
```

Closing that declaration finishes the project.  Nothing else has to be added
to the public API.

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
`Status.md`; do not bypass it.  A row listed as `Statement completed` or
`Reduction completed` is still unfinished until an actual unconditional proof
of the stated result is in place.

## Mathematical requirements

* The one open item is the blueprint's Phase D--F chain, packaged in source as
  the predicate `HasPlanarNegativeRawBandRate`.  Its content is:
  1. `prop:critical-loss`: the critical-weight dyadic estimate
     `norm(M_j f, L^2(|x|^-1)) <= C_eps * 2^(eps*j) * norm(f, L^2(|x|^-1))`
     for every `eps > 0`, uniformly in the radius grid;
  2. Phase E: interpolation with the trivial `L^inf` bound over the fixed
     measure `|x|^-1 dx`, moving that estimate from `p = 2` to every `p > 2`;
  3. Phase F: Stein--Weiss interpolation with change of measure against the
     unweighted frequency gain, which yields the required power gain
     `2^(-eta*j)` at the weight `|x|^a`.
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
* `Reduction completed` -- the Lean proof is complete except that it invokes
  the single unproved placeholder `exists_planarNegativeRawBandRate`;
* `Statement completed` -- the target is correctly formulated but unproved;
* `ToDo` -- not formalized.

Update the relevant rows whenever the implementation changes.  When the
placeholder is finally discharged, every `Reduction completed` row becomes
`Proof completed` and that status value must be removed from the legend.

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
`LeanSpherical.lean`.  While the placeholder is open,
`Spherical.PowerWeights.closure_typeSet_eq` legitimately reports `sorryAx`;
every other public theorem must report only `propext`, `Classical.choice` and
`Quot.sound`.  Also run `git diff --check` and scan the target source file for
`sorry`, `admit` and `axiom`: the expected count of `sorry` in the repository
outside `ProofSkeleton.lean` is exactly one, at
`exists_planarNegativeRawBandRate`.

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
* the packaged Phase D--F predicate `HasPlanarNegativeRawBandRate` and the one
  unproved placeholder `exists_planarNegativeRawBandRate`;
* the Schwartz-core estimate
  `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_negative_of_gt_two`
  for an arbitrary radius set, obtained from the placeholder, the unweighted
  planar Bourgain bound and the repository's buffered raw-band reassembly;
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

## Immediate remaining proof route

1. Prove the blueprint's Phase D annular decomposition and
   `prop:critical-loss` in the form of a weighted `L^2` estimate for
   `restrictedRelativeBandpassSphericalMaximal 2 (normalizedRadiusBlock E R) phi j`
   against `powerWeightedVolume 2 (-1)`, uniformly in `R`, with an arbitrarily
   small `2^(eps*j)` loss.  Use the blueprint's one-dimensional Sobolev
   estimate in `t` on `[1,2]`, keeping the averaging estimate and the
   `t`-derivative estimate as separate lemmas: that is where the powers of
   `2^j` are generated.
2. Prove the fixed-measure `2 -> p` interpolation of Phase E for the finite
   grid operators, then pass to the supremum by monotone convergence.
3. Prove the Stein--Weiss change-of-measure theorem of Phase F and combine
   with `exists_relativeCircularBandGeometricDecay`, choosing `eps` by
   `exists_pos_interpolated_gain`.
4. Convert the resulting `2^(-eta*j)` weighted bound into the localized form
   of `HasPlanarNegativeRawBandRate` -- the output ball is
   `closedBall 0 (1/32)` and the input support is `euclideanAnnulus 2 (1/4) 8`
   -- and discharge `exists_planarNegativeRawBandRate`.
5. Re-run the source compile, the module build, `git diff --check`, the
   placeholder scan and the axiom audit.  At that point
   `Spherical.PowerWeights.closure_typeSet_eq` becomes unconditional under
   `2 <= d` and the project is finished.

Optional, only after step 5: the blueprint's `thm:dv-general` in its full
planar weight range `-1 < a < p - 2` requires, in addition, the nonnegative
branch for the full radius set, i.e. the computation of the Minkowski exponent
of `(0, inf)` together with the corresponding Legendre--Assouad values.  That
is not needed for the closure theorem and must not be started before step 5.
