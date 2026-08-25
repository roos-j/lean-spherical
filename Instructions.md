# Continuation instructions: Bourgain circular maximal formalization

This file records the user's instructions and the current handoff state for a
follow-up agent.  It is a working specification, not a replacement for the
blueprint.

## Primary objective

Formalize Bourgain's circular maximal theorem following
`blueprints/bourgain_circular_maximal_blueprint.tex`, and finish only when
the existing public theorem
`Codex.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_sphericalMaximal_le`
has genuinely been strengthened from the hypothesis `3 <= d` to `2 <= d`.
The resulting theorem must cover the planar full-radius case (in particular
the radius-set/Minkowski-exponent-one situation) under exactly the old
hypotheses except for this dimension change.

The requested theorem in `Bourgain.lean` only needs the Schwartz-function
version; do not add the blueprint's extension-to-`Lp` conclusion there.  The
separate diagonal theorem is allowed and required to extend the Schwartz
core through the repository's existing lift machinery.

## Required files and namespaces

Put Lean code primarily and, unless a genuinely necessary supporting change
is made, exclusively in these files:

* `LeanSpherical/Codex/Spherical/MSS.lean` in
  `Codex.Spherical.MSS`
* `LeanSpherical/Codex/Spherical/MSSPhaseCalculus.lean` in
  `Codex.Spherical.MSSPhaseCalculus`, for the intrinsically planar radial
  phase calculus used only by the sharp MSS kernel endpoint
* `LeanSpherical/Codex/Spherical/SmoothDyadicPhysicalCore.lean` in
  `Codex.Spherical.SmoothDyadicPhysicalCore`, for dimension-generic literal
  physical Fourier-cube kernels
* `LeanSpherical/Codex/Spherical/Bourgain.lean` in
  `Codex.Spherical.Bourgain`
* `LeanSpherical/Codex/Spherical/MikhlinHormander.lean` in
  `Codex.Spherical.MikhlinHormander`
* `LeanSpherical/Codex/Spherical/LittlewoodPaley.lean` in
  `Codex.Spherical.LittlewoodPaley`
* `LeanSpherical/Codex/Spherical/OneDimStationaryPhase.lean` in
  `Codex.Spherical.OneDimStationaryPhase`
* `LeanSpherical/Codex/Spherical/RieszThorin.lean` in
  `Codex.Spherical.RieszThorin`
* `LeanSpherical/Codex/Spherical/LpSpaceFacts.lean` in
  `Codex.Spherical.LpSpaceFacts`
* `LeanSpherical/Codex/Spherical/FractalDilations/DiagonalTheorem.lean`,
  solely for the requested final `d = 2` integration.

Documentation files are also required and permitted:

* `Status.md`
* `ErrorReport.md`
* this handoff file, `Instructions.md`.

All new Lean declarations must live under a `Codex` namespace matching their
file path.  The user later explicitly authorized additional foundational
work needed to complete the proof.  Auxiliary names outside the foundations
should still use the `aux_` prefix.  Foundational names (C-Z theory,
Mikhlin, stationary phase, Riesz--Thorin, etc.) need not use that prefix.

## Blueprint-order execution (mandatory)

`blueprints/bourgain_circular_maximal_blueprint.tex` is the source of truth
for the proof plan.  Work through its labeled results in their written order.

1. Select one labeled theorem, proposition, lemma, or corollary as the active
   item.  Do not begin work on a later labeled result while that item remains
   unfinished.
2. Finish the active item completely before advancing: give the actual Lean
   proof, compile the source, run the appropriate module build, audit its
   axioms and placeholders, check the diff, update the documentation, and
   remove owned scratch material.
3. Foundational work is allowed only when it is demonstrably necessary to the
   active item.  Treat that foundation as part of the same item, finish it,
   then return directly to the active theorem; do not use it to open a
   parallel later-blueprint task.
4. Do not add speculative wrappers, consumers, convenience corollaries, or
   side bridges merely because they are easy to formalize.  A declaration is
   in scope only if it is required to finish the active labeled result.
5. `Status.md` is a ledger of the blueprint's labeled results, in blueprint
   section order.  Apart from its preserved foundations section, it must not
   track assistant-invented helper theorems, scratch work, or status-only
   wrappers.

At the start of a work session, identify the earliest unfinished labeled
result in the current blueprint chain from `Status.md`; do not bypass it.
A target predicate listed as `Statement completed` is still unfinished until
an actual proof of the stated result is in place.

## Mathematical requirements

* Generalize foundational facts that are not intrinsically planar to ambient
  dimension `d`.
* Reuse the repository's definitions of spherical averages and maximal
  functions, its Hardy--Littlewood maximal function, dyadic resolutions, and
  other existing infrastructure instead of duplicating them.
* The repository convention is `x + t • omega` for spherical averages and
  Mathlib Fourier conventions have `2*pi`; respect those exact conventions.
* The final theorem must use only standard Lean/mathlib axioms.  Never use
  `sorry`, `admit`, `axiom`, or an unproved wrapper.  Do not use
  `ProofSkeleton.lean`, which contains an admitted theorem.
* Do not merely state a desired theorem as a `Prop` and mark it proved.  A
  `Statement completed` row is appropriate only for a correctly formulated
  target predicate; its theorem remains unfinished until a proof exists.

## Documentation requirements

Keep the existing foundations section of `Status.md` unchanged.  Outside
that section, organize the ledger by the blueprint's sections and include
only the blueprint's labeled theorems, propositions, lemmas, and corollaries.
Use one row per blueprint label; do not add rows for definitions, public
helpers, `aux_` declarations, scratch results, convenience corollaries, or
working-file completion.  Each row records the exact Lean target when one
exists, its status, and a review timestamp.  Use exactly one of:

* `Proof completed`
* `Statement completed`
* `ToDo`

Update the relevant rows whenever the implementation changes.

Every discrepancy found in the blueprint or while adapting it to Lean must
be recorded in `ErrorReport.md` as a concise but thorough timestamped entry.
Blueprint errors are not a reason to stop; correct them where possible.

## Source verification commands

Always compile source files, rather than relying on old `.olean` artifacts.
On this Windows workspace the normal command is:

```powershell
lake env lean -o .lake\build\lib\lean\LeanSpherical\Codex\Spherical\Bourgain.olean LeanSpherical\Codex\Spherical\Bourgain.lean
```

Replace `Bourgain` for each target.  For the final integration use:

```powershell
lake env lean -o .lake\build\lib\lean\LeanSpherical\Codex\Spherical\FractalDilations\DiagonalTheorem.olean LeanSpherical\Codex\Spherical\FractalDilations\DiagonalTheorem.lean
```

Also run `git diff --check` and scan the target source files for
`sorry`, `admit`, and `axiom`.  Check the axioms of substantive final results;
acceptable ones are the ordinary `propext`, `Classical.choice`, and
`Quot.sound` family.

## Formalization discipline

* Complete one source-file transaction at a time.  When it finishes, update
  only the row for the active blueprint result; do not create helper or
  completed-file rows in `Status.md`.
* State reusable foundations in arbitrary Euclidean dimension and for the
  natural full range `1 < p < ∞` whenever their proof does not genuinely use
  a planar or endpoint-specific feature.  Treat `d = 2` and `p = 4` as
  downstream circular-maximal/MSS specializations, not as default foundation
  targets.
* Keep the blueprint ledger current.  Do not use a "progress notes" section
  or track public declarations that are not themselves blueprint labels.
* Edit Lean and Markdown source only through `apply_patch`; use PowerShell
  for read-only inspection and compilation.  This preserves the project's
  UTF-8 mathematical notation during long proof transfers.

## Current verified state

The following work is source-compiled and uses only standard axioms:

* `LittlewoodPaley.lean`: completed.  Besides the existing finite `L2` and
  MSS-specific `L4` reductions, it now has a dimension-free finite
  Khintchine/Paley--Zygmund lower-moment argument and
  `littlewoodPaley_of_uniform_signed`.  Combined downstream with the uniform
  all-`p` signed Mikhlin bound, `MikhlinHormander.littlewoodPaley_of_mikhlin`
  proves the main square-function theorem for every positive ambient
  dimension and every `1 < p < ∞`.  The `L4` reduction remains only the
  downstream MSS specialization.
* `OneDimStationaryPhase.lean`: quadratic stationary-phase estimates with
  explicit `C1` amplitude bounds and arbitrary-order nonstationary repeated
  integration by parts.  It now has automatic nonstationary quotient-chain
  synthesis under an explicitly smooth nonvanishing derivative extension,
  a two-branch quadratic Morse-chart interface, and the proved transport from
  that chart to `HasQuadraticNormalForm` and then to the half-order symbol
  estimate.  A bare smooth nondegenerate point now gives a positive local
  Morse-coordinate radius, and the radius-scaled chart/normal-form layer
  transports it at the exact `radius^2 * lambda` frequency.  It deliberately
  requires globally smooth branch extensions as explicit data: the current
  pointwise `ContDiffAt ... ∞` inverse API does not certify a global smooth
  extension.  The remaining honest gap in the unrestricted theorem is that
  extension/localization bookkeeping, not a fictitious unit-radius chart.
* `RieszThorin.lean`: completed.  The main theorem `rieszThorin` is a direct,
  sharp diagonal Riesz--Thorin theorem from literal endpoint `eLpNorm`
  hypotheses.  For finite interior `p > 1`, it accepts the ENNReal reciprocal
  relation (including an `L∞` endpoint), works for an arbitrary complex normed
  source `E` such as an `ℓ²` fibre, and constructs the bounded interpolated
  `Lp E p μ → Lp ℂ p ν` extension with a.e. agreement on the raw
  simple-function core.  `rieszThorin_one_one`, `rieszThorin_top_top`, and
  `rieszThorin_top_top_of_eLpNorm` cover the degenerate endpoint cases.
  `RieszThorinAnalyticDatum` remains a reusable conditional three-lines core,
  but is not the main theorem.  The source compiles without placeholders.
* `LpSpaceFacts.lean`: completed reusable measure/Lp facts extracted from the
  interpolation work: Hölder/log-convexity estimates, finite-exponent
  membership consequences, counting-measure comparison, and real-power
  lower-integral/eLpNorm conversions.  It intentionally contains no
  analytic-power, simple-function, or interpolation-operator argument.
* `MikhlinHormander.lean`: completed.  `mikhlin` proves the parameter-uniform
  literal punctured-symbol multiplier estimate in every positive dimension,
  for every derivative order `N > d` and every `1 < p < ∞`.  Its proof now
  includes raw finite dyadic localization, uniform C--Z good-`L2`, weak
  `(1,1)`, formal-adjoint duality, and symmetric-truncation Fatou reassembly.
  `mikhlin_two` is the planar third-order specialization.  The bridge from
  the usual planar coordinate C3 seminorms is also formalized through ordered
  standard-basis derivative values, with the explicit factor `8`.  The
  dimension-generic bridge
  `relativeSchwartzMultiplierKernelSize_le_compactFourierIBP` reduces the two
  physical Schwartz-kernel seminorms to Fourier `L1` and a finite order-`d+2`
  integration-by-parts constant; use that concrete certificate for compact
  multiplier families rather than treating physical uniformity as opaque.
* `MSS.lean`: exact 2π-normalized half waves; fixed and space-time `L2`
  endpoint; compact-symbol kernel/convolution facts; the local-smoothing and
  discrete-local-smoothing target predicates; gain algebra; finite radial
  enumeration and finite vertical/angular/plate-pair algebra, plus a finite
  Fourier-cube `L2` square-function package with exact physical/frequency
  energy identities and a literal finite-overlap bound.  Its geometric
  plate-overlap target now explicitly requires ordered-sector geometry rather
  than arbitrary directions. The zero-thickness planar model now has an
  unconditional multiplicity-at-most-two theorem for positive radii under
  that geometry, via Mathlib's two-circle intersection theorem. The thick
  plate-overlap, Kakeya, and unconditional `p=4` local-smoothing proof are
  still missing.  The explicit `4ℤ` normal-coordinate cover of a
  `scale^γ`-thick plate, its `O(scale^γ)` cardinality bound, and its transfer
  from a translated unit-normal-thickness overlap theorem to `plateOverlap`
  are now proved; `translatedUnitNormalPlateOverlap` remains the honest cited
  planar input rather than a consequence of the zero-thickness two-circle
  lemma.  Finite fine-cube/light-ray and reverse-overlap reductions are
  source-checked but do not replace their continuum counterparts.  The
  planar sharp half-wave-kernel route is now complete for arbitrary compact
  annular `lpCutoffs 2`: `MSSPhaseCalculus.lean` supplies the intrinsically
  planar radial-phase trace calculation, the cancelled Fourier-side cone
  energy is proved, and `waveKernelL1_sharp` plus
  `mssLInfinityEndpoint` are source-compiled.  The new all-d physical
  Fourier-cube kernel layer and the genuine continuum light-ray Fubini
  bridge are also in place.  `angularDyadicCubeSpaceTimeKernel` now gives a
  literal spatial source-kernel model for the actual angular half-wave of a
  Fourier-cube projection, and `angularDyadicCubePacket_eq_sum` reconstructs
  a finite literal packet kernel as the sum of those actual projected angular
  pieces.  The still-missing p=4 work is its quantitative
  ray localization, the actual continuum wave-packet/cube realization,
  reverse overlap, planar Nikodym--Kakeya input, and reconstruction to
  `fineSquareFunctionEstimate`.  The conic recombination/fine-square
  predicates compose to a real `scale^(1/8+eta)` conic L4 theorem, both
  dyadic half-wave signs are exactly identified with its two-sided time-cutoff
  normal form, and `p4LocalSmoothing_of_twoSidedConicData` plus
  `p4LocalSmoothing_to_hasPositiveLocalSmoothingGain` are proved conditional
  assembly theorems.  Do not infer the still-cited translated
  unit-normal-thickness overlap estimate from the exact zero-thickness
  two-circle lemma.
* `Bourgain.lean`: raw circular operators bridge exactly to the repository
  operators; conditional all-radius reassembly from geometric relative-band
  decay; radial Schwartz-kernel maximal majorant; verified `L2` time Sobolev
  and separated-sampling layers; exact Fourier-meridian and
  outgoing/incoming/middle coordinate-wave normal forms (also after a dyadic
  bandpass), including an exact three-term dyadic circular-average identity;
  literal `2^(j/2)`-normalized compact and fat-annular endpoint multipliers
  with half-wave factorizations; the annular endpoint multiplier is now
  packaged as a compact Schwartz symbol after removing the zero singularity;
  and reciprocal-scale planar short-interval `L2` facts. No theorem yet
  supplies the needed positive band decay.
* `DiagonalTheorem.lean`: private `q`-generic endpoint helpers plus the
  genuine conditional theorem
  `eLpNorm_sphericalMaximal_le_of_bourgain`, which proves the requested
  `d >= 2` conclusion if supplied with the real Bourgain Schwartz bound for
  every `q > 2`.  The original public unconditional theorem is deliberately
  still `d >= 3` because the Bourgain input is not yet proved.

The dimension-generic compact `C^N` inverse-Fourier integration-by-parts,
raw dyadic-localization, C--Z, and all-`p` interpolation/duality layers in
`MikhlinHormander.lean` are complete; the main Mikhlin theorem and its
Littlewood--Paley consequence have been source-compiled.

## Key reusable interfaces

* `Spherical.sphericalAverage` and `Spherical.M` are the public operators.
* `Codex.Spherical.PowerWeights.OperatorBridge` bridges public and internal
  normalized spherical operators.
* `Codex.Spherical.PowerWeights.RawLpLift.memLp_restrictedSphericalMaximal_of_memLp_of_schwartz_bound`
  lifts a finite-exponent Schwartz core to arbitrary `MemLp` input.
* `Codex.Spherical.PowerWeights.GlobalRelativeReassembly.hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_zero_of_relative_band_decay`
  turns literal geometric relative-band decay into the desired all-radius
  normalized strong type.
* `Codex.Spherical.FractalDilations.CircleSurface.exists_sharp_surfaceFourier_two_decay_and_deriv`
  is a compiled planar stationary-decay input; its bundled bridge is
  `CircleFourierBridge.hasCircleSurfaceFourierSharpBounds`.
* `Codex.Spherical.FractalDilations.CircleDyadicL2` gives short interval
  planar `L2` bounds, but not the full unit-time / full-radius Bourgain gain.
* `Codex.Spherical.InterpolationCore` supplies real Marcinkiewicz machinery
  only after suitable endpoint hypotheses are actually proved.

## Known blockers and pitfalls

* There is no existing full all-radii planar circular maximal theorem in this
  repository.  Existing circle/fractal results require a strictly sub-one
  Minkowski exponent and cannot be instantiated at exponent one.
* Uniform dyadic-block constants do not sum to an all-radius theorem; do not
  mistake blockwise dilation for a global bound.
* Mathlib/repository do not provide a ready generic full Mikhlin theorem or
  all-`p` Littlewood--Paley/Rubio de Francia theorem.  The direct
  Riesz--Thorin construction is now local to this repository; Mathlib's
  three-lines and Hölder APIs supply its analytic and pairing ingredients.
* `SmoothEndpointAmplitude.lean`, `QuadraticStationaryPhase.lean`,
  `QuadraticMomentDerivatives.lean`, `PlanarEndpointAmplitude.lean`,
  `CoordinateMeridianWaves.lean`, and
  `PlanarCoordinateMeridianWaves.lean` have all been repaired and source
  compiled on 2026-08-13.  The derivative file corrected a real
  profile-versus-moment indexing mismatch: parameter differentiation raises
  the moment while retaining the profile.  The final planar coordinate normal
  form is now safely imported by `Bourgain.lean`; do not replace it with an
  opaque/stale artifact.  The full quantitative multiplier/local-smoothing
  stages are still not proved.  `CoordinateMiddleNonstationary.lean` is now
  source-compiled and gives the literal middle-meridian `O(|l|^{-1})`
  estimate; its guarded integration-by-parts amplitude was corrected from
  `cos^(m-1)/guard` to `cos^m/guard`.  Bourgain retains the middle term
  explicitly until this scalar decay is upgraded to the required uniform
  dyadic multiplier estimate.  The latter upgrade has now begun: the literal
  middle dyadic multiplier has a proved `O(2^{-j})` pointwise bound on active
  unit-time annuli and is packaged as a Schwartz symbol by exact subtraction;
  uniform derivative/kernel estimates remain to be proved.
* The source-clean planar Q4 triple-wave normal forms are useful exact TT*
  identities, but their quantitative consumers remain fractal: in dimension
  two they require a subpower Assouad cover exponent below (or at the special
  critical value) `1/2`. They cannot be instantiated by the full interval
  `[1,2]`, whose local covering exponent is one. Do not treat that route as a
  proof of the needed full-radius MSS estimate.
* The blueprint itself has a range mismatch in its Kakeya substitution:
  `delta = lambda^(-1/2)` is below `1/2` only for `lambda > 4` although it
  states `lambda >= 2`.  Record/handle the bounded range separately.

## Immediate remaining proof route

The critical missing step is a true unconditional planar `p=4` MSS/local-
smoothing estimate with positive gain.  The two-sign conic-to-dyadic and
positive-gain assembly steps are complete conditional on the geometric input.
The blueprint isolates its nontrivial ingredients:

1. conic/radial-time localization and vertical recombination;
2. translated unit-normal-thickness wave-front plate overlap and its thick
   cover transfer;
3. quantitative ray localization of the literal angular Fourier-cube kernel;
4. Fourier-cube square function and continuum reconstruction;
5. planar light-ray/Nikodym-Kakeya estimate;
6. fine square-function and recombination;
6. interpolate only after the `p=4` bound is genuinely proved;
7. derive geometric relative-band decay, invoke Bourgain reassembly, prove
   `HasCircularMaximalSchwartzBound`, then change the public diagonal theorem
   to `2 <= d` and source-compile it.

Do not lower the public threshold conditionally or insert the final statement
until this chain is complete.

## 2026-08-14 14:16:38 -04:00 — orderly session handoff

This section supersedes the older “immediate route” only as a checkpoint.  The
public diagonal theorem is **not** complete: do not weaken its `3 <= d`
hypothesis until the unconditional planar Bourgain chain is actually proved.

### Clean source state at this checkpoint

* Final verification at `2026-08-14 14:24:12 -04:00`: direct compilation of
  `Bourgain.lean` and `lake build LeanSpherical.Codex.Spherical.Bourgain`
  both passed (only pre-existing warnings).

* `Bourgain.lean` contains the source-compiled raw middle-wave rapid-decay
  theorem
  `exists_memLp_four_and_eLpNorm_iSup_circleMiddleWaveContribution_le_rapid_dyadicDecay`.
  It has arbitrary integer decay parameter `r` and controls the literal
  short-time middle maximum by
  `dyadicTimeScale j ^ (r + 3/4)` times the fourth-root input energy.
* The completed endpoint side includes the literal moving-fat operator
  `circleRelativeBandFatHalfWaveOutput`, its product-rule time derivative,
  and
  `exists_memLp_four_and_eLpNorm_iSup_circleRelativeBandFatHalfWaveOutput_of_positiveLocalSmoothingGain`.
  These are unconditional apart from the explicitly supplied
  `HasPositiveLocalSmoothingGain`.
* `Bourgain.lean` also now has the first two source-compiled layers for the
  moving-fat middle term: public
  `circleRelativeBandFatMiddleOutput`, a private literal product-rule
  derivative, and private compact-frequency joint-continuity / `HasDerivAt`
  machinery.  The direct source compile passed after each of those two
  chunks.  The normalized fixed-time `L4`, slab-energy, and sampler theorem
  for this term have **not** yet been landed.
* `MSS.lean` has not received a new source patch in this final checkpoint.
  It still contains the proved conditional normal-cover transfer
  `plateOverlap_of_translatedUnitNormalPlateOverlap`; the actual
  `translatedUnitNormalPlateOverlap` remains unproved in source.

### Preserve and finish these three scratch-first workstreams

The following active scratch files are deliberately left in place for the
next agent.  Do not delete them before either landing their checked proof or
capturing an equivalent proof in source.

1. `ScratchBandReassembly.lean` — moving-fat middle term.

   It has source-independent, compiling exact q/qdot factorisations for the
   literal middle multiplier, including the product rule
   `qdot * middle + q * middleTimeDerivative`, plus the compact-Fourier
   joint-continuity/differentiation argument.  Resume by transplanting the
   normalized fixed-time `L4` composition (use the existing direct rapid
   middle kernel certificates), then the product integrability, slab energy,
   and quartic sampling argument.  The model to follow is the half-wave
   block around `aux_continuous_and_hasDerivAt_circleRelativeBandFatHalfWaveOutput`
   in `Bourgain.lean` (roughly lines 11645–13106).

   Immediately after that theorem is source-built, assemble it with
   `exists_memLp_four_and_eLpNorm_iSup_circleRelativeBandFatHalfWaveOutput_of_positiveLocalSmoothingGain`
   and the literal five-band/fat-cutoff identities.  Export a direct bound
   for the full unit-slab expression
   `F⁻[surfaceFourier (-t·eta) * movingRelativeBand_j(t,eta) * fat_j(eta) * g(eta)]`
   for arbitrary Schwartz frequency datum `g` (use physical input `F⁻ g`).
   Do not leave a new opaque Prop wrapper: this exact local expression is the
   premise of the all-radius theorem below.  Land Bourgain edits in small
   UTF-8 chunks, direct-compile after each, then run the module build,
   update `Status.md`, audit axioms/hygiene, and delete this scratch only once
   it is fully superseded.

2. `ScratchHighRelativeL4.lean` (with `ScratchHighRelativeCore.lean`) —
   all-radius relative-band (p=4) reassembly.

   This scratch proof is complete and compiled.  Its main private theorem is
   `aux_hasRelativeCircularBandGeometricDecay_four_of_unitFat`: from the
   literal full unit-slab moving-fat fourth-moment estimate it proves
   `HasRelativeCircularBandGeometricDecay 4 C.cutoff`.  It uses:

   * exact shifted-fat = five ordinary dyadic bands;
   * the proved `L4` Littlewood--Paley reassembly (constant `625` in the
     finite formulation);
   * exact physical radius-block dilation;
   * a no-cardinality-loss finite fourth-moment block union inequality; and
   * `GlobalBandExhaustion.lintegral_rpow_restrictedRelativeBandpassSphericalMaximal_of_dyadicRadiusBlockExhaustion`.

   First wait until the BandReassembly local five-piece theorem exists, then
   move the literal unit-fat definition and this proof into `Bourgain.lean`.
   State the global theorem directly with that literal local inequality, not
   a new predicate.  Convert the fourth moment to `MemLp`/`eLpNorm` exactly as
   in the scratch, with `rho = theta ^ (1/4)`.  Run source/module builds and
   update Status before deleting the two scratch files.

   A planar (L^2) companion has only begun.  `circleBandpassUnitIntervalL2`
   is for a fixed symbol and cannot be applied directly to the moving
   relative cutoff.  The viable route is: use uniform q/qdot kernel
   majorants only for fixed-time (L^2) stability; use the fixed-band circle
   `L2` maximal theorem to control the ordinary half-wave and its compact
   derivative input; then apply the existing (L^2) time sampler at mesh
   `2^{-j}` so the derivative factor cancels.  Do not invoke the
   higher-dimensional relative-moving endpoint (`d >= 2`, ambient dimension
   at least three) in the planar case.

3. `ScratchUnitNormalPlateOverlap.lean` — actual translated unit-normal
   plate overlap in MSS.

   This is an active, substantially developed scratch proof.  It has
   compiled low-scale global-box and high-scale tangent-class packings,
   normalized two-cone/polar identities, the coupled normal-time/radius
   estimates, a transverse same-area-sign direction bound, and finite label
   box counting.  The correct final partition is **three** regimes/boxes:
   tangent, positive oriented area, and negative oriented area.  The old
   direct-or-swap two-box clustering is false (unequal-radius mirror
   configurations); do not reintroduce it.

   Finish the high-separation area-sign classification using the existing
   polar bound, turn the three direction caps into label boxes via
   `angularSectorGeometry`, and then source-land the actual
   `translatedUnitNormalPlateOverlap` in `MSS.lean`.  Coarse explicit Nat
   constants are preferred to optimizing the bound.  Then direct-compile and
   module-build MSS, update Status/ErrorReport, run `git diff --check` and an
   axiom/placeholder audit, and delete this scratch only after the source
   theorem replaces it.

### Order after these checkpoints

1. Finish the moving-middle local theorem and its five-band wrapper.
2. Land the all-radius (p=4) relative geometric-decay theorem and obtain
   the corresponding conditional circular (L^4) Schwartz bound.
3. Finish the literal planar relative (L^2) endpoint above, then use the
   repository’s real interpolation machinery with (L^4) decay and the
   existing top endpoint to cover every finite `q > 2`.
4. This still does **not** prove the required positive local-smoothing gain:
   the genuinely remaining MSS work is the continuum wave-packet/cube
   realization, reverse overlap, measurable light-ray TT*/Córdoba logarithmic
   estimate, `fineSquareFunctionEstimate`, and `recombination`.  The source
   has conditional assembly theorems only; do not promote them to proofs.
5. Only after `HasCircularMaximalSchwartzBound q` is proven for every
   `q > 2` may `DiagonalTheorem.eLpNorm_sphericalMaximal_le` be changed from
   `3 <= d` to `2 <= d`.  Compile the final diagonal module at that point.

When resuming, serialize edits to `Bourgain.lean`: BandReassembly owns the
next local source transaction; the global relative reassembly must wait for
its clean module-build boundary.  Source scratch files use UTF-8; keep source
patches small and raw to avoid mojibake.  Do not use `sorry`, `admit`, or new
axioms.

## Live continuation checkpoint — 2026-08-19 23:24:23 -04:00

This checkpoint supersedes the older “Current verified state” and “Order
after these checkpoints” text above wherever they disagree.  It records the
actual source/build boundaries at the end of the current working session.

### Verified since the previous checkpoint

* `MSS.lean` now proves the actual translated unit-normal plate overlap:
  `translatedUnitNormalPlateOverlap_of_angularSectorGeometry`, followed by
  the unconditional `plateOverlap_of_angularSectorGeometry`.  The proof uses
  the correct low-scale/tangent/two-area-sign decomposition; do not revive the
  false direct-or-swap clustering formulation.
* The literal finite plate-overlap square-energy and cube-output-fibre layers
  are source-compiled.  They consume explicit pair-realization data, rather
  than claiming that arbitrary fine cubes already provide it.
* Fixed-time spatial Fourier support of actual angular cube pieces, exact
  separable space-time Fourier identities (including finite mixed Schwartz
  tensor sums), and finite vertical recombination `L2` / common-kernel
  `L∞` endpoints are source-compiled in `MSS.lean`.  These all retain their
  explicit Schwartz profile, overlap, and kernel-envelope hypotheses.
* `Bourgain.lean` now has literal moving-fat endpoint and middle local
  `L4` maximal theorems, the exact five-dyadic decomposition of the full
  unit-slab moving relative band, and
  `hasRelativeCircularBandGeometricDecay_four_of_circleRelativeBandFatUnitSlab`.
  The latter is the complete all-radius `p=4` reassembly from the literal
  local fourth-moment hypothesis; it is no longer scratch-only.

### Active continuation order

1. **Finish the local unit-slab `p=4` bridge in `Bourgain.lean`.**  The
   active block is assembling the exact full
   `circleRelativeBandFatUnitSlabMaximal` from its five dyadic summands.
   The high relative-frequency case is reduced to the proved endpoint-plus,
   endpoint-minus, and rapid-middle estimates (with the required
   `surfaceMass 2` factor).  Its fat-projected input rewrite is already
   source-compiled.  Handle the finite low relative indices `j ≤ 2` by a
   direct compact-annular family estimate, then state the literal
   fourth-moment bound against `circleRelativeBandFatInputProjection`.
   Do not introduce a new wrapper predicate.  Apply the existing all-radius
   `p=4` bridge immediately afterwards.
2. **Finish the planar moving-relative `L2` endpoint in scratch, then land
   it after the Bourgain transaction.**  The viable construction is literal
   q/qdot fixed-time kernel control plus the public `L2` time sampler.  A
   planar `surfaceFourier` derivative-rescaling lemma replaces the invalid
   ambient-dimension-at-least-three shortcut.  Its regularity and fixed-time
   energy layers have already checked in scratch.  After `L2` and `L4` are
   both actual all-radius estimates, use the repository’s concrete
   interpolation machinery to obtain every finite `q > 2`; do not state an
   abstract interpolation assumption.
3. **Finish the finite vertical `L4` theorem in `MSS.lean`.**  A checked
   scratch proof combines the new literal finite profile `L2` and common-time
   kernel `L∞` endpoints.  It must remain an explicit finite separable-packet
   result; it does not prove `verticalRecombination` or a cutoff half-wave
   statement.
4. **Keep the main MSS frontier honest.**  The current actual
   `angularDyadicCubePacket` only has fixed-time spatial Fourier support.  It
   lacks radial/normal labels, space-time output cells, and a conic plate
   support theorem.  A nonzero physical time cutoff cannot have exact compact
   temporal Fourier support.  Completing the continuum wave-packet/Fourier
   multiplier bridge, reverse overlap, measurable light-ray TT*/Córdoba
   estimate, `fineSquareFunctionEstimate`, and `recombination` remains the
   genuine route to proving `p4LocalSmoothing`, hence the final unconditional
   dimension-two diagonal theorem.

### Build and cleanup discipline

Only one agent should edit/build `Bourgain.lean` at a time.  An MSS module
build temporarily removes `MSS.olean`; wait for its completion before
compiling Bourgain scratch files.  Keep scratch files while they are the only
checked copy of a proof, then delete them immediately after the source
replacement has direct-compiled, module-built, passed `git diff --check`,
and received the required Status/ErrorReport updates.

## Live continuation checkpoint — 2026-08-20 02:12:29 -04:00

This checkpoint supersedes the older continuation order above where it
disagrees with the current source state.

### Verified Bourgain chain

* The literal moving-fat local `L4` estimate, including the high five-piece
  endpoint/middle decomposition and finite low-relative-scale compact-family
  fallback, is source-compiled.  It yields
  `hasRelativeCircularBandGeometricDecay_four_of_positiveLocalSmoothingGain`
  and the corresponding conditional `L4` circular Schwartz bound.
* The planar literal moving-fat local `L2` sampler/reassembly is now fully
  source-compiled.  Its public all-radius endpoint is
  `exists_memLp_two_and_eLpNorm_restrictedRelativeBandpassSphericalMaximal`.
  It is deliberately uniform in the relative scale; do not try to package it
  as `HasRelativeCircularBandGeometricDecay 2 ...`, whose definition requires
  a strict ratio below one.
* The source-compiled all-finite-exponent interpolation block is at the tail
  of `Bourgain.lean`:
  `hasRelativeCircularBandGeometricDecay_all_gt_two_of_uniform`,
  `hasRelativeCircularBandGeometricDecay_of_positiveLocalSmoothingGain`, and
  `hasCircularMaximalSchwartzBound_of_positiveLocalSmoothingGain`.
  It uses a private raw ENNReal top bound, rather than incorrectly inferring
  finiteness from `.toReal`.
* Direct source compiles, module builds, `git diff --check`, placeholder
  scans, and standard-axiom audits passed for the verified p=2/p=4/all-p
  transactions.  Their scratch proofs were deleted after verification.

### Current compiler-blocked adapter

`Bourgain.lean` currently contains one additional, small source patch:
`hasCircularMaximalSchwartzBound_of_p4LocalSmoothing`.  It applies
`MSS.p4LocalSmoothing_to_hasPositiveLocalSmoothingGain` with `rho = 1/16`
and then the verified all-p positive-gain theorem.  It has **not** yet been
validated: the required Lean command was denied by the environment's Codex
usage limit, not by a reported Lean error.  Do not treat this declaration as
verified or edit `DiagonalTheorem.lean` until compiler authorization is
available.

When compilation is restored, first run the prescribed direct Bourgain
compile and Bourgain module build, then hygiene/axiom audits and Status
update.  Next add and validate the one-line diagonal adapter
`eLpNorm_sphericalMaximal_le_of_p4LocalSmoothing`, by applying
`eLpNorm_sphericalMaximal_le_of_bourgain` to the new Bourgain theorem.

### Honest remaining frontier

These results are conditional on `p4LocalSmoothing C.cutoff`.  MSS already
converts that assumption to any gain `0 < rho < 1/8`, but no unconditional
producer is proved.  The real upstream work remains the compact-time
half-wave to spectral/conic-plate approximation, output-cell/reverse-overlap
realization, vector-valued finite/continuum recombination, fine square
function estimate, and planar light-ray/Kakeya input.  The spectral Schwartz
packet and finite plate-overlap results are genuine model-level components;
they must not be presented as an exact compact-time packet proof.

The next narrow MSS infrastructure target is not a duplicate packet model:
`spectralCubeRadialNormalPacket` already provides that.  First prove the two
generic Fubini conversions identifying `spaceTimeFourier` and
`spaceTimeFourierInv` on a joint `SchwartzMap WaveSpaceTime Complex` with the
canonical Schwartz Fourier pair.  A later wavefront support lemma must take a
supplied annular Schwartz realization and an equality only *after* multiplying
by the input spectrum.  An exact compact physical-time cutoff half-wave
cannot be asserted to have compact conic Fourier support.

## Live continuation checkpoint — 2026-08-20 12:33:42 -04:00

This checkpoint supersedes the compiler-blocked adapter note above.

The source-level `p = 4` local-smoothing bridge is now complete and verified:

* `Bourgain.hasCircularMaximalSchwartzBound_of_p4LocalSmoothing` applies
  `MSS.p4LocalSmoothing_to_hasPositiveLocalSmoothingGain` at `rho = 1 / 16`
  and supplies the conditional circular maximal Schwartz bound for every
  finite real exponent `q > 2`.
* `FractalDilations.DiagonalTheorem.eLpNorm_sphericalMaximal_le_of_p4LocalSmoothing`
  applies that bridge to the existing Bourgain diagonal theorem, yielding the
  conditional all-radii estimate in every `d ≥ 2` and
  `p > d / (d - 1)`.

Both declarations passed direct source compilation and their respective
module builds.  `git diff --check`, placeholder scans, and the axiom audit
also passed; each theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.  The temporary audit file was removed.

These are still conditional on `MSS.p4LocalSmoothing C.cutoff`; do not label
the final diagonal theorem unconditional.  The next agent should resume the
honest MSS frontier described above, beginning with the generic joint-Schwartz
Fubini Fourier conversions and preserving the distinction between the
spectral packet model and a compact-time half-wave construction.

## Live continuation checkpoint — 2026-08-20 13:42:18 -04:00

The joint-Schwartz Fourier conversions and the explicitly spectral
wavefront-support realization have now landed in `MSS.lean`; they still do
not identify a compact physical-time half-wave with a plate-supported packet.
On the vertical branch, the finite additive temporal Schwartz core now also
has exact convolution realization
`verticalTemporalSchwartzMultiplier_eq_convolution` and the scalar
`L1`-kernel `L∞` estimate
`norm_verticalTemporalSchwartzMultiplier_le`, both source-compiled and
module-built. These expose the correct kernel for the next vector-valued
step without asserting a continuum result.

The current narrow next task is either:

1. finish the scratch-only specialized joint-Schwartz external product and
   annular/sheared compact-time spectral profile, keeping its application to
   actual cutoff half-waves conditional on a future approximation theorem; or
2. prove a finite temporal-core common pointwise-kernel envelope and the
   resulting `sqrt indices.card` `PiLp 2` top bound, then construct the
   all-input/density extension needed before applying Riesz--Thorin.

The conditional Bourgain/Diagonal theorem remains verified, but all claims
still depend on `MSS.p4LocalSmoothing C.cutoff`. Do not relabel it as an
unconditional planar circular maximal theorem.

## Live continuation checkpoint — 2026-08-20 13:49:36 -04:00

The finite temporal vertical core has advanced one honest step further:
`norm_verticalTemporalSchwartzCoreRecombined_le_of_common_kernel` is now a
verified source theorem. Given a nonnegative integrable common pointwise
envelope for the inverse-Fourier kernels, it proves the sharp
`sqrt indices.card` top bound against the temporal ℓ² square function. The
underlying one-block convolution identity and scalar kernel estimate are also
public. This removes the finite-top algebraic gap, but its inputs remain a
finite tuple of Schwartz profiles.

The next vertical task is therefore precise: construct an additive operator
on a suitable measurable `PiLp 2` input class which extends this finite core,
prove its L2 finite-overlap and the new L∞ common-kernel endpoints, establish
AEMeasurability, and only then invoke the existing Riesz--Thorin machinery.
Do not confuse this with the older profile-specific L2/L∞ energy estimates;
those do not yield the required source square-function L4 norm.

## Live continuation checkpoint â€” 2026-08-20 13:56:24 -04:00

The first compact-time spectral-tail foundation is now source-complete in
`MSS.lean`:

* `jointSchwartzExternalProduct` packages
  `B : SchwartzMap (Euclidean 2) Complex` and
  `h : SchwartzMap Real Complex` into a genuine
  `SchwartzMap JointWaveSpaceTime Complex`.
* `jointSchwartzExternalProduct_apply` gives the exact raw-coordinate value
  at `WithLp.toLp 2 (xi, tau)`: `B xi * h tau`.

The source direct compile, serialized `MSS` module build, public API check,
targeted placeholder scan, `git diff --check`, and axiom audit all passed.
The public declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  The shared `MSS.olean` artifact is restored.

This is deliberately not a compact-time half-wave theorem.  The next
spectral-tail task is to prove an annular smooth radial extension equal to
`‖xi‖` on the spatial profile's support, then a Schwartz shear producing the
joint profile `B xi * FourierTransform.fourier vartheta (tau - ‖xi‖)`.  Keep
the physical half-wave equality and any conic-plate conclusion conditional on
new Fourier-modulation/Fubini or quantitative off-plate-tail lemmas; never
claim exact compact conic support for a compact physical-time cutoff.

The vertical finite-core branch remains independent: its next task is still
the measurable additive `PiLp 2` extension required before Riesz--Thorin.

## Live continuation checkpoint — 2026-08-20 13:59:53 -04:00

`verticalTemporalSquareFunction` is now public together with exact pointwise
and all-exponent `eLpNorm` identities to its finite `PiLp 2` bundle. This is
the precise source norm required by the newly proved finite common-kernel
`sqrt indices.card` top estimate. The finite vertical endpoint is therefore
expressed in the same geometry as the future vector-valued interpolation
operator.

The missing work is not a further finite norm conversion: it is the actual
additive, AEMeasurable extension to measurable bundle-valued inputs (with its
L2 overlap and L∞ kernel bounds), followed by Riesz--Thorin and only then a
continuum/reconstruction argument.

## Live continuation checkpoint - 2026-08-20 14:09:33 -04:00

The radial-shear foundation now has a source-verified smooth annular norm
extension in `MSS.lean`:

* `smoothAnnularNormExtension` turns a compactly supported real planar
  Schwartz cutoff that vanishes on a positive-radius ball about zero into the
  Schwartz map `xi |-> u xi * ||xi||`.
* `smoothAnnularNormExtension_apply` is its literal pointwise formula.
* `smoothAnnularNormExtension_eq_norm_of_eq_one` and
  `smoothAnnularNormExtension_eq_norm_on_support` identify it with `||xi||`
  where the cutoff is one, including on a complex planar Schwartz profile's
  support.

The direct source compile, serialized `MSS` module build, and public API/axiom
audit are green. The public declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. The next independent task may use this
with `jointSchwartzExternalProduct` to formalize a smooth shear. Do not infer
a physical half-wave equality, exact compact-time conic support, or a
conic-plate theorem from this spectral smoothness result alone.

## Live continuation checkpoint - 2026-08-20 14:22:01 -04:00

The pure-Schwartz radial shear is now source-complete in `MSS.lean`:

* `jointSchwartzPrecompRadialShear rho Q` returns a genuine
  `SchwartzMap JointWaveSpaceTime Complex`.
* `jointSchwartzPrecompRadialShear_apply` gives its exact raw-coordinate
  formula at `WithLp.toLp 2 (xi, tau)`:
  `Q (WithLp.toLp 2 (xi, tau - rho xi))`.

The proof uses `SchwartzMap.compCLM`, with private temperate-growth and
degree-one properness certificates.  Direct MSS compilation, the serialized
MSS module build, the public axiom audit, the targeted no-placeholder scan,
and `git diff --check` are green; the public theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

The next narrow spectral task is to combine
`jointSchwartzExternalProduct` with this shear and a
`smoothAnnularNormExtension`, obtaining the literal profile
`B xi * h (tau - rho xi)` and then using the equality `rho xi = ||xi||` on
the support of `B`.  Keep any relation to a compact-time half-wave,
Fourier-modulation identity, or conic-plate support conditional on a new
physical-to-spectral approximation/off-plate-tail theorem.  The independent
vertical branch still needs the measurable additive `PiLp 2` extension before
Riesz--Thorin.

## Live continuation checkpoint - 2026-08-20 14:27:06 -04:00

The next pure spectral composition is now source-complete in `MSS.lean`:

* `jointSchwartzModulatedAnnularProfile B vartheta rho` is the radial-shear
  precomposition of `jointSchwartzExternalProduct B (fourier vartheta)`.
* `jointSchwartzModulatedAnnularProfile_apply` gives the exact value
  `B xi * fourier vartheta (tau - rho xi)`.
* `jointSchwartzModulatedAnnularProfile_eq_norm_on_support` gives the same
  formula with `tau - ||xi||` whenever supplied `rho = ||.||` on the support
  of `B`.

The direct source compile, serialized `MSS` module build, public API/axiom
audit, and scratch regression are green. This is still purely spectral. The
physical Fourier-modulation/Fubini calculation, any compact-time half-wave
identity, and any exact conic-plate support claim remain separate work.

## Live continuation checkpoint - 2026-08-20 14:47:41 -04:00

The narrow physical Fourier/Fubini bridge is now source-complete in
`MSS.lean` for supplied Schwartz data:

* `spaceTimeFourierInv_jointSchwartzModulatedAnnularProfile B vartheta rho z`
  proves the exact identity
  `spaceTimeFourierInv (jointSchwartzRaw
  (jointSchwartzModulatedAnnularProfile B vartheta rho)) (x, t) =`
  `vartheta t * FourierTransform.fourierInv (fun xi => B xi *`
  `Real.fourierChar (rho xi * t)) x`.
* `spaceTimeFourierInv_jointSchwartzModulatedAnnularProfile_eq_halfWave_of_eq_norm_on_support`
  specializes it when supplied `rho = ||.||` on `Function.support B`, with
  the positive branch `halfWaveMultiplier WaveSign.plus`.  The phase sign is
  correct for Mathlib's inverse Fourier convention:
  `Real.fourierChar (||xi|| * t) = halfWaveMultiplier WaveSign.plus t xi`.

The proofs use an exact one-dimensional translated-Fourier inversion lemma,
literal joint kernel integrability, and Fubini.  Direct source compilation,
the serialized `MSS` module build, public API check, axiom audit, targeted
placeholder scan, and `git diff --check` are green; the public theorems use
only `propext`, `Classical.choice`, and `Quot.sound`.

The scope remains deliberately narrow: `vartheta` is supplied as a Schwartz
map, not automatically compactly supported.  Do not infer an instantiation of
legacy `angularPiece`, any exact conic-plate support, an off-plate-tail bound,
recombination, a fine-square estimate, or a `p4LocalSmoothing` conclusion.

## Live continuation checkpoint - 2026-08-20 14:56:59 -04:00

Two further exact Fourier-conversion APIs are now source-complete in
`MSS.lean`:

* `spaceTimeFourier_spaceTimeFourierInv_jointSchwartzRaw P zeta` proves that
  the iterated forward transform of the iterated inverse of a joint Schwartz
  raw representative is exactly `P (WithLp.toLp 2 zeta)`. It reuses the
  existing generic forward/inverse conversion APIs and
  `FourierTransform.fourier_fourierInv_eq`; it introduces no new Fubini layer.
* Under supplied `rho = ||.||` on `Function.support B`,
  `spaceTimeFourier_temporalSchwartzHalfWave_eq_jointSchwartzModulatedAnnularProfile`
  identifies the iterated Fourier transform of the temporal-Schwartz
  positive half-wave with `jointSchwartzModulatedAnnularProfile B vartheta rho`.

Direct source compilation, the serialized `MSS` module build, public API and
axiom audit, targeted placeholder scan, and `git diff --check` are green. The
public declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

Keep the scope exact: this is a supplied-Schwartz spectral profile identity,
not a proof of compact physical-time support or compact conic/plate support.
It does not give a legacy `angularPiece` realization, a tail estimate,
recombination, a square-function estimate, or a local-smoothing theorem.

## Live continuation checkpoint - 2026-08-20 15:12:42 -04:00

The first honest projected spatial/normal model for the temporal-Schwartz
annular positive half-wave is now source-complete in `MSS.lean`:

* `jointSchwartzSpatialNormalCutoff u beta rho` is a genuine joint Schwartz
  cutoff with raw value `u xi * beta (tau - rho xi)`.
* `temporalSchwartzAnnularNormalProjection B u vartheta beta rho` is the
  physical output obtained by applying that cutoff to the Fourier profile of
  `jointSchwartzModulatedAnnularProfile B vartheta rho`.
* `spaceTimeFourier_temporalSchwartzAnnularNormalProjection` proves its exact
  Fourier transform is the cutoff times the supplied temporal-Schwartz
  positive-half-wave profile.
* `support_spaceTimeFourier_temporalSchwartzAnnularNormalProjection_subset_conicPlate`
  proves plate support only under literal spatial radial/angular containment
  of `support B`, the displayed vertical-label condition for every
  `xi ∈ support B` and `s ∈ support beta`, and the displayed normal-width
  condition on `support beta` (as well as `rho = ||.||` and `u = 1` on
  `support B`).

Direct source compilation, the serialized `MSS` module build, public API and
axiom audit, targeted placeholder scan, and `git diff --check` are green. The
public declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

This is a projected model only. Schwartz data does not by itself give compact
support, and the result must not be misread as support for the unprojected
temporal cutoff half-wave, a legacy `angularPiece` realization, an
approximation/off-plate-tail bound, recombination, a fine square function, or
`p4LocalSmoothing`.

## Live continuation checkpoint - 2026-08-20 15:42:44 -04:00

`MSS.lean` now has a bounded exact normal-tail API for the supplied
temporal-Schwartz annular positive-half-wave model:

* `temporalSchwartzAnnularNormalTail B u vartheta beta rho` is the literal
  joint-Schwartz inverse transform of the spectral complement of
  `temporalSchwartzAnnularNormalProjection`.
* `temporalSchwartzHalfWave_eq_projection_add_normalTail` reassembles the
  literal temporal-Schwartz positive half-wave from the projection and tail
  under the supplied `rho = ||.||` condition on `support B`.
* `spaceTimeFourier_temporalSchwartzAnnularNormalTail` gives the exact tail
  factor `(1 - u xi * beta (tau - rho xi)) *
  B xi * fourier vartheta (tau - rho xi)`.
* `support_spaceTimeFourier_temporalSchwartzAnnularNormalTail` gives only the
  honest support exclusion `support B ∩ {beta (tau - rho xi) != 1}` when
  `u = 1` on `support B`.

The direct source compile, serialized MSS module build, public API check,
targeted placeholder scan, `git diff --check`, and standard-axiom audit all
passed. The public theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The tail API is exact but does not prove compact physical-time
support, unprojected plate support, off-plate or quantitative tail decay,
approximation, recombination, a fine square function, or local smoothing.

## Live continuation checkpoint - 2026-08-20 16:50:51 -04:00

The finite temporal common-kernel branch is now source-complete in
`MSS.lean`. The public literal endpoint is
`memLp_four_and_eLpNorm_finiteTemporalCommonKernelOutput_of_overlap`; it
acts on `finiteTemporalCommonKernelBundle` data in the concrete
`finiteTemporalCommonKernelMeasurableDomain`, and its output is the literal
finite convolution sum `finiteTemporalCommonKernelOutput` with kernels
`finiteTemporalCoreKernel`.

Its proof uses a private quotient-to-raw `L²` extension, the sharp
`sqrt(card)` common-kernel top bound, literal measurable hard truncations,
and the supplied-split Marcinkiewicz theorem. The explicit public
`finiteTemporalCoreTopCoefficient` and
`finiteTemporalCoreFourthMomentBound` retain the finite-vector constants.

Scope remains deliberately finite and temporal: this does not prove a
continuum extension, `verticalRecombination`, a spacetime packet theorem,
a fine square function, or `p4LocalSmoothing`. A later consumer may rewrite
the finite Schwartz core into the finite sum of vertical temporal projections,
but must not infer any of those stronger conclusions.

## Live continuation checkpoint - 2026-08-20 17:05:10 -04:00

`MSS.lean` now has the first finite Schwartz-profile consumer of the literal
finite common-kernel `L⁴` endpoint:

* `memLp_four_and_eLpNorm_verticalTemporalSchwartzCoreRecombined_of_overlap`
  takes supplied `m : Int → SchwartzMap Real Complex`, the existing profile
  and finite-overlap hypotheses, and supplied
  `g : Int → SchwartzMap Real Complex`.
* It proves `MemLp` at exponent four for
  `verticalTemporalSchwartzCoreRecombined indices m g` and retains the exact
  existing RHS
  `finiteTemporalCoreFourthMomentBound C indices m
  (fun t => WithLp.toLp 2 (fun i : ↥indices => g (i : Int) t)) ^ (4 : Real)⁻¹`.
* Private helpers immediately above it build that `PiLp 2` bundle, establish
  its literal `finiteTemporalCommonKernelMeasurableDomain` membership from
  Schwartz continuity, `L²`, boundedness, and coordinatewise integrability,
  and identify the common-kernel convolution sum with the finite core.

Direct source compilation, the serialized `MSS` module build, the public API
check, target axiom audit, and `git diff --check` are green. The public theorem
depends only on `propext`, `Classical.choice`, and `Quot.sound`.

Keep the scope finite and temporal. This does not prove a continuum/vector
extension, any spatial or half-wave assertion, a spacetime packet estimate,
`verticalRecombination`, a fine square-function theorem, or local smoothing.

## Live continuation checkpoint - 2026-08-20 17:12:35 -04:00

`MSS.lean` now has the finite common-spatial space--time consumer
`memLp_four_and_eLpNorm_verticalSchwartzCoreRecombined_commonSpatial_of_overlap`.
It takes one spatial `SchwartzMap (Euclidean 2) Complex` profile `F`, a finite
temporal Schwartz family `g`, and the existing finite profile/overlap data.
The literal output is exactly
`verticalSchwartzCoreRecombined indices m (fun _ => F) g`.

Its proof first factors that output pointwise as the finite temporal core at
time `t` times `F x`, then uses product Lebesgue measure to factor the fourth
`eLpNorm`. The public right-hand side is the explicit temporal
`finiteTemporalCoreFourthMomentBound` from the preceding theorem, multiplied
by `eLpNorm F 4 volume`.

Keep this scope precise: it covers one shared spatial Schwartz profile and a
finite temporal Schwartz family only. It is not a result for varying spatial
profiles, arbitrary vector-valued inputs, `verticalRecombined`, a continuum
limit, a spacetime-packet/fine-square-function estimate, or local smoothing.

## Live continuation checkpoint - 2026-08-20 17:30:56 -04:00

The first finite supplied-Schwartz varying-spatial consumer is now public:

* `memLp_four_and_eLpNorm_verticalSchwartzCoreRecombined_of_overlap` takes a
  finite spatial family `F : Int → SchwartzMap (Euclidean 2) Complex` and a
  finite temporal Schwartz family `g`, in addition to the existing multiplier
  profile and finite-overlap hypotheses.
* It proves `MemLp 4` for `verticalSchwartzCoreRecombined indices m F g` and
  bounds its fourth `eLpNorm` by the finite sum over `n ∈ indices` of
  `eLpNorm (F n) 4 volume` times
  `finiteTemporalCoreFourthMomentBound` for the temporal family that equals
  `g n` at `n` and zero elsewhere.
* The proof uses only singleton common-spatial applications and finite
  Minkowski. Private helpers identify those singleton outputs with the
  corresponding summands of the varying-spatial core.

Direct source compilation, the serialized `MSS` module build, the exported
API check, target axiom audit, and `git diff --check` are green. The theorem
uses only `propext`, `Classical.choice`, and `Quot.sound`.

This is intentionally a finite supplied-Schwartz Minkowski estimate, not the
stronger one-shot spatial square-envelope theorem. Do not infer a
vector-valued/continuum extension, `verticalRecombined`, a square function,
a spacetime packet estimate, or local smoothing.

## Live continuation checkpoint - 2026-08-20 17:39:18 -04:00

The supplied joint-Schwartz annular normal-projection branch now has two
source-verified finite APIs in `MSS.lean`:

* `spaceTimeFourier_temporalSchwartzAnnularNormalProjection_eq_jointAmplitude`
  gives the exact joint Fourier value
  `B xi * (beta (tau - rho xi) * fourier vartheta (tau - rho xi))` under the
  displayed unit-cutoff-on-support hypothesis.
* `overlapSquareFunction_temporalSchwartzAnnularNormalProjections` takes a
  finite `(n, nu)` family of those literal projections, all explicit spatial,
  vertical-label, and normal-width support data, and the analytic
  `overlapSquareFunction` hypothesis.  It yields the corresponding literal
  projected-model recombined-square `L⁴` bound.

The second theorem is a direct finite consumer of the base overlap hypothesis
and the public projection plate-support theorem.  It does not identify the
model with `angularPiece`, a separable spectral packet, or `fineSquareFunction`;
it gives no normal-tail decay, `fineSquareFunctionEstimate`, `p4LocalSmoothing`,
or local-smoothing conclusion.

## Live continuation checkpoint - 2026-08-20 17:59:26 -04:00

The regular supplied-Schwartz angular/radial bridge and the pointwise normal
tail branch are now source-complete in `MSS.lean`:

* `fourier_radialPiece_eq_schwartzProfile_mul_fourier` derives the raw radial
  piece's Fourier formula from a **supplied** Schwartz radial representative
  `R`; it never infers regularity from a raw cutoff.
* `temporalSchwartzHalfWave_eq_angularPiece_of_schwartzRadialProfile` and
  `angularPiece_eq_projection_add_normalTail_of_schwartzRadialProfile` turn
  supplied `R` and spatial amplitude `B` identities into the exact literal
  `angularPiece` equality and then its projected-plus-tail decomposition.
* The two long `exists_nonneg_one_add_normal_pow...NormalTail...` theorems
  give arbitrary pointwise Fourier decay in the normal coordinate, and its
  normal-ball-radius refinement when `beta = 1` on that ball.

These are regular-model and pointwise spectral statements only.  They do not
construct `R` or `B` from raw cutoffs, control an `Lp` tail, establish raw
compact-time plate support, identify a separable packet, prove a fine square
function estimate, or imply `p4LocalSmoothing`/local smoothing.

## Live continuation checkpoint - 2026-08-20 18:19:32 -04:00

The joint-Schwartz branch now has literal product-coordinate `L²` Plancherel
transport in `MSS.lean`:

* `eLpNorm_spaceTimeFourier_jointSchwartzRaw_two_eq` is the exact `eLpNorm`
  equality for `jointSchwartzRaw G`, proved by transporting the canonical
  `Lp` Fourier isometry across `WithLp.toLp`.
* `eLpNorm_spaceTimeFourier_temporalSchwartzAnnularNormalTail_two_eq` is its
  direct regular-model specialization for
  `temporalSchwartzAnnularNormalTail`.
* `exists_regularAngularRadialBridgeData_of_normRadialSchwartzCutoffs`
  constructs the displayed `radialCutoff` and Schwartz amplitude `B` for one
  fixed norm-radial packet, with explicit unit-vector and positive-scale data.

The packet constructor chooses its scalar cutoff per packet; it does not
produce a uniform family, raw cutoff regularity, raw compact-time plate
support, a tail radius estimate, a fine-square estimate, `p4`, or local
smoothing.  The L² tail identity is for the supplied joint-Schwartz model
only, not raw packets.

## Live continuation checkpoint - 2026-08-20 19:14:40 -04:00

The supplied joint-Schwartz normal-tail branch now has uniform physical
radius-decay endpoints in MSS.lean:

* exists_finite_uniform_one_add_normal_radius_pow_mul_eLpNorm_two_temporalSchwartzAnnularNormalTail
  gives a finite uniform L2 bound after fixing B, vartheta, N, and a
  nonnegative defect envelope M.
* exists_finite_uniform_one_add_normal_radius_pow_mul_eLpNorm_four_sq_temporalSchwartzAnnularNormalTail
  gives the corresponding finite uniform squared L4 bound. It combines the
  L2 endpoint at power 2*N with a Fourier-L1 envelope transported through the
  normal shear.

Both theorems require u to equal one on the supplied spatial amplitude
support, beta to equal one on the normal ball, and a global bound
norm(1 - beta) <= M. They concern only the regular temporal-Schwartz tail
model. Do not use them as claims about raw compact-time packets, plate
support, finite or continuum recombination, a fine square function, p4
local smoothing, or the circular maximal theorem.

## Live continuation checkpoint - 2026-08-20 19:35:41 -04:00

Two narrow regular-model approximation APIs are now public in MSS.lean:

* exists_finite_uniform_one_add_normal_radius_pow_mul_eLpNorm_four_sq_angularPiece_sub_projection_of_schwartzRadialProfile
  transfers the uniform squared normal-tail L4 bound to one supplied
  angularPiece minus its temporal-Schwartz normal projection. The supplied
  radial/profile identities remain global, while the support norm agreement
  is quantified with the selected rho.
* eLpNorm_four_finset_sum_sub_le_sum_of_eq_add_of_tail_bounds is a generic
  finite Minkowski lemma. Given literal full = main + tail identities and
  measurable tail functions, it bounds the L4 error of the finite sum by the
  sum of the supplied tail L4 envelopes.

Neither theorem constructs raw regularity, proves a packet-family or
continuum approximation, establishes a square function, plate support, p4
local smoothing, or the circular maximal theorem.

## Live continuation checkpoint - 2026-08-20 20:02:41 -04:00

The finite regular angular/radial perturbation layer is now source-complete in
`MSS.lean`:

* `eLpNorm_four_verticalSquareFunction_sub_le_sum_of_eq_add_of_tail_bounds`
  gives finite one-index `l2` square-function stability from literal
  componentwise `full = main + tail` identities and supplied `L4` tail
  envelopes.
* `eLpNorm_four_aux_angularRadialRecombinedSquareFunction_sub_le_sum_of_eq_add_of_tail_bounds`
  gives the matching finite two-index recombined angular/radial version.
* `exists_regularAngularPiece_recombined_square_bound_of_overlap_plus_normalTails`
  combines the existing projected-model `overlapSquareFunction` consumer with
  the supplied regular `angularPiece = projection + normalTail` identity. Its
  conclusion retains the explicit finite sum of literal normal-tail `L4`
  norms.

The new theorems are finite and supplied-Schwartz only. They do not infer raw
compact-time packet regularity or plate support, give a tail rate for a family,
prove a fine-square estimate, establish `p4LocalSmoothing`, take a continuum
limit, or imply the circular maximal theorem.

## Live continuation checkpoint - 2026-08-20 20:23:02 -04:00

Two public finite perturbation APIs now expose the literal raw square-function
right-hand side:

* `eLpNorm_four_angularRadialSquareFunction_sub_le_sum_of_eq_add_of_tail_bounds`
  turns a finite two-index pointwise `full = main + tail` identity and
  componentwise measurable `L4` tail envelopes into an `L4` bound for the
  difference of raw `angularRadialSquareFunction`s.
* `exists_regularAngularPiece_recombined_square_bound_of_overlap_plus_normalTails_on_rawSquare`
  combines that stability estimate with the projected normal-model overlap
  bridge. Its coefficient is `q = ofReal (C * scale ^ eta)`, and its exact
  conclusion is `‖Srec(A)‖₄ ≤ q * ‖Ssq(A)‖₄ + (q + 1) * Σ ‖tail‖₄`.

These remain finite supplied-Schwartz statements under the explicit analytic
`overlapSquareFunction` and regular profile/support hypotheses. Do not read
them as a raw compact-time approximation, a uniform family tail estimate,
fine-square result, `p4LocalSmoothing`, continuum theorem, or circular
maximal theorem.

## Live continuation checkpoint - 2026-08-20 20:45:24 -04:00

`exists_finite_uniform_regularAngularPiece_recombined_square_bound_of_overlap_on_rawSquare_with_normalRadiusRate`
now supplies the finite regular-model normal-radius estimate with the useful
quantifier order:

* first `C : Real`, `0 < C`, from the analytic plate-overlap hypothesis;
* then one `D : ENNReal`, `D < ∞`, from the finite family of regular normal
  tails;
* then all supplied `u`, `beta`, `rho`, and common `normalRadius` satisfying
  the displayed support, ball-agreement, and defect hypotheses.

For `W = (ofReal (1 + normalRadius)) ^ N`, the literal conclusion is
`W * ‖Srec(A)‖₄ ≤ q * (W * ‖Sraw(A)‖₄) + (q + 1) * D`, with
`q = ofReal (C * scale ^ eta)`. This is the clean weighted version of the
normal-radius tail rate. It is finite and supplied-Schwartz only; it does not
prove a raw cutoff approximation, a fine square function, `p4LocalSmoothing`,
infinite-family summation, continuum passage, or the circular maximal bound.

## Live continuation checkpoint - 2026-08-20 21:10:33 -04:00

Two exact finite angular-synthesis APIs are now public in `MSS.lean`:

* `sum_angularPiece_eq_conicOperator_of_sum_eq_one_on_support` turns a finite
  angular partition on the literal spatial Fourier support into the equality
  `sum angularPiece = conicOperator`. It requires per-time, per-index
  integrability of the raw angular Fourier symbols.
* `radialTimeReconstruction_eq_verticalRecombined_angularPiece_of_sum_eq_one_on_support`
  applies that identity at every finite radial label and exposes the literal
  angular family inside `verticalRecombined`.

These are algebraic identities only. They do not manufacture a partition or
integrability proof for raw MSS cutoffs, commute a finite angular sum through
`verticalProjection`, prove a vertical endpoint, establish a fine square
function or `p4LocalSmoothing`, or make a continuum claim. Supplied Schwartz
profiles can discharge the integrability side condition through the private
regular-data helper.

## Live continuation checkpoint - 2026-08-20 21:16:34 -04:00

`conicOperator_eq_verticalRecombined_angularPiece_add_radialTimeResidual_of_sum_eq_one_on_support`
now gives the exact finite outer decomposition required by the p4 audit:

`conicOperator = verticalRecombined (angular pieces) + radialTimeResidual`.

It reuses the literal support-local angular partition and raw integrability
hypotheses; the proof is pointwise additive algebra after the preceding
reconstruction identity. It supplies no residual decay, vertical endpoint,
square-function/fine-square estimate, partition construction,
`p4LocalSmoothing`, or continuum passage.

## Live continuation checkpoint - 2026-08-20 21:31:58 -04:00

The finite supplied-Schwartz temporal core now has the exact foundations for
the varying-spatial Fubini lift:

* `verticalTemporalSchwartzMultiplier_smul` and
  `verticalSchwartzCoreRecombined_fiber` identify each spatial fiber with a
  temporal core applied to the scalar-scaled temporal profile family.
* `finiteTemporalCoreFourthMomentCoefficient` and
  `finiteTemporalCoreFourthMomentBound_eq_coefficient_mul_lintegral` expose
  the input-independent interpolation coefficient without unfolding it.
* `lintegral_norm_rpow_four_verticalTemporalSchwartzCoreRecombined_le_of_overlap`
  is the raw fourth-moment temporal endpoint with a literal finite `PiLp 2`
  bundle on the right, suitable for Tonelli.

The next bounded consumer may perform only the finite supplied-Schwartz
space-time Fubini lift.  It must not infer an arbitrary measurable endpoint,
`verticalRecombined` identity, square-function/fine-square estimate,
`p4LocalSmoothing`, or continuum result.

## Live continuation checkpoint - 2026-08-20 21:50:09 -04:00

The finite supplied-Schwartz varying-spatial Fubini lift is now public:

* `lintegral_norm_rpow_four_verticalSchwartzCoreRecombined_le_of_overlap`
  is the literal space-time raw fourth-moment estimate with the finite
  `verticalSquareFunction` fourth moment on the right.
* `memLp_four_and_eLpNorm_verticalSchwartzCoreRecombined_le_of_overlap`
  adds the finite-core `MemLp 4` and coefficient-to-the-one-quarter norm
  bound.
* `eLpNorm_four_verticalRecombined_verticalSeparablePackets_le_of_overlap`
  is only the supplied-profile rewrite to literal finite
  `verticalRecombined` separable packets.

Any next consumer must retain finite supplied Schwartz data and the explicit
profile/overlap hypotheses.  These theorems do not supply arbitrary input
extension, `verticalRecombination`, continuum passage, a square-function or
fine-square estimate, `p4LocalSmoothing`, or local smoothing.

## Live continuation checkpoint - 2026-08-20 22:32:52 -04:00

The finite-rank-per-original-label supplied-Schwartz core is now public:

* `finiteRankVerticalSchwartzCore` and `finiteRankVerticalPackets` retain a
  finite rank sum inside each original vertical index.
* `lintegral_norm_rpow_four_finiteRankVerticalSchwartzCore_le_of_overlap`
  and `memLp_four_and_eLpNorm_finiteRankVerticalSchwartzCore_of_overlap`
  give the raw and L4 forms with the original temporal coefficient.
* `finiteRankVerticalSchwartzCore_eq_verticalRecombined_of_schwartzProfiles`
  is the exact finite Fourier rewrite, and
  `eLpNorm_four_verticalRecombined_finiteRankPackets_le_of_overlap` is its
  literal recombined corollary.

The right-hand square function is over rank-summed packets indexed by the
original finite vertical labels.  Do not turn this into further packaging:
the next substantive step must instead address the sharp l2-envelope
endpoint with its beta modulation/dilation bridge, or a direct
vertical/fine-square advance.  No arbitrary-input, density,
`verticalRecombination`, scale, continuum, fine-square, p4, or local
smoothing conclusion follows here.

## Codex source management

- Do not create new source files under `LeanSpherical/Codex`.
- Consolidate finished MSS work into `LeanSpherical/Codex/Spherical/MSS.lean` before handoff.
- Scratch files may be used for temporary experiments, but delete them as soon as they are no longer needed. Do not leave obsolete scratch artifacts in the repository.

## Live verification checkpoint - 2026-08-24 13:41:49 -04:00

`MSS.lean` now proves the unconditional planar endpoint theorem
`p4LocalSmoothing_of_lpCutoffs : ∀ C : lpCutoffs 2, p4LocalSmoothing C.cutoff`.
It is source-compiled and module-built; its axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The proof reconstructs the
positive sign from a finite coarse conic atlas and obtains the negative sign
by reflected-conjugate Fourier transport.

Accordingly, earlier checkpoint text describing unconditional p=4 local
smoothing as the missing frontier is historical and superseded.  Do not infer
from this endpoint alone that the separately labeled all-exponent
`thm:mss-local-smoothing`, `cor:mss-discrete`, Bourgain, or diagonal results
are complete; validate each downstream adapter before updating its ledger row.

## Live verification checkpoint - 2026-08-24 13:48:00 -04:00

The required downstream all-exponent adapter has now been verified in
`MSS.lean`: `localSmoothing_of_lpCutoffs` applies
`p4LocalSmoothing_to_localSmoothing_all_p` to the proved endpoint, so it
establishes `localSmoothing C.cutoff p eta` for every `C : lpCutoffs 2`,
`2 < p`, and `0 < eta`.  Its source compile, the top-level
`LeanSpherical.Theorems` build, and its axiom audit (only `propext`,
`Classical.choice`, and `Quot.sound`) all pass.

This supersedes the preceding checkpoint only for
`thm:mss-local-smoothing`.  The discrete, Bourgain, and diagonal ledger rows
remain unchanged until their own unconditional public declarations are
verified.

## Live verification checkpoint - 2026-08-24 13:57:41 -04:00

The continuous MSS route is now closed through the requested final
integration.  `Bourgain.lean` provides `bourgainCircularMaximal` by choosing
an `lpCutoffs 2` witness and applying `p4LocalSmoothing_of_lpCutoffs`; the
diagonal module provides `eLpNorm_sphericalMaximal_le_of_mss` for every
dimension at least two; and `LeanSpherical.Theorems` exports the matching
`Spherical.eLpNorm_sphericalMaximal_le_of_mss` facade while retaining its
older dimension-at-least-three theorem unchanged.

Each edited source direct-compiles, the `LeanSpherical.Theorems` module build
passes, and declaration-level audits report only `propext`,
`Classical.choice`, and `Quot.sound`.  This supersedes the preceding
checkpoint for Bourgain and diagonal integration.  The only still-unproved
listed MSS result is the separately formulated `cor:mss-discrete`, which
requires a source-level time-sampling/derivative bridge rather than a further
consequence of continuous local smoothing.

## Live verification checkpoint - 2026-08-24 16:00:45 -04:00

`DiagonalTheorem.eLpNorm_sphericalMaximal_le` itself now has the requested
`2 <= d` signature. Its `d = 2` branch invokes the completed unconditional
Bourgain/MSS bound through the existing finite- and top-exponent raw lifts;
the `d >= 3` branch is the prior restricted-dilation proof. The edited source
compiles directly.

Do not infer that the separately updated `Theorems.lean` restricted,
lacunary, or power-weight wrappers are complete in dimension two. Their
`1 < p < 2` planar cases require the missing global moving-band/selector
estimate, and the power-weight result additionally requires its planar
negative-weight branch. Preserve those signatures as an explicit open
integration issue unless those independent results are genuinely proved.
