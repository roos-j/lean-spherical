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

## Mathematical requirements

* Follow the blueprint in linear order.  Do not begin a later theorem before
  its preceding theorem is truly finished, except for independently required
  foundational development needed by it.
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

`Status.md` must have a section for every working file and an entry for every
labeled definition/theorem/lemma in the blueprint.  Each individual Lean
name must have its **own table row** with its own status and timestamp; do
not place a comma-separated group of names on one row.  Do not report
`aux_` declarations there.  Use exactly one of:

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

* Complete one source file at a time.  A file is complete only after its
  required main theorem has source-compiled; then update `Status.md` with a
  separate, easy-to-find main-theorem row and a completed-file row.
* State reusable foundations in arbitrary Euclidean dimension and for the
  natural full range `1 < p < ∞` whenever their proof does not genuinely use
  a planar or endpoint-specific feature.  Treat `d = 2` and `p = 4` as
  downstream circular-maximal/MSS specializations, not as default foundation
  targets.
* Keep `Status.md` current for every public non-aux declaration.  Do not use
  a "progress notes" section.
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
