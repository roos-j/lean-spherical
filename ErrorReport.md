# Bourgain circular maximal formalization — error report

## 2026-08-24 07:39:55 -04:00

`MSSWavefrontRawProfileRealization.radialProfile_apply` was quantified over
all real scales, although every consumer works at a positive (indeed at least
two) scale. At `scale = 0` and `n = 0`, its displayed identity forces a
Schwartz map on `Euclidean 2` to be the constant function `radial 0 = 1`
(the radial cutoff is one at zero). Such a map cannot be Schwartz. The
raw-realization interface must therefore require `0 < scale` for this
identity; its existing source consumers already carry that fact. This is a
formal interface inconsistency, not a discrepancy in the MSS argument.

## 2026-08-22 12:51:53 -04:00

The tempting replacement of the missing fine Fourier-cube `L⁴` square-function
estimate by a bound uniform over *every deterministic Rademacher signing* is
false for an expanding separated lattice of translated cubes.  Already in one
dimension, take a nonzero compact prototype, choose signs matching the Fourier
coefficients of an input packet, and the multiplier maps a random-sign input
to an all-positive Dirichlet packet.  Its `L⁴` operator norm grows like a
positive power of the number of cubes.

The valid Khintchine formulation averages the fourth moment over sign choices;
that averaged statement is essentially the desired cube square-function
estimate, not a consequence of lattice separation or the existing Mikhlin
development.  The source APIs therefore retain the every-sign statement only
as a clearly marked stronger conditional lemma and use a sign-average target
for the actual missing analytic step.

## 2026-08-21 20:02:43 -04:00

The former internal route through
`aux_HasLightRayTTStarIntersectionSchurEstimate` is not a valid formulation
of the planar Kakeya input.  Besides omitting measurability of a chosen
direction field, its pointwise row-Schur conclusion is false even for smooth
unit-valued fields: a tube bush can make one row of the literal smooth TT*
intersection kernel of order `delta^-1`, rather than polylogarithmic.
The desired light-ray maximal theorem itself remains the faithful MSS
statement, but its proof must use Córdoba's quadratic/angular-overlap
argument rather than a uniform TT* row estimate.

## 2026-08-13 10:26:15 -04:00

In `prop:mss-fine-square-function`, the blueprint invokes the Kakeya estimate with
`δ = λ⁻¹ᐟ²`.  Its stated hypothesis is `0 < δ < 1/2`, whereas the proposition
allows `λ ≥ 2`; the displayed substitution only gives `δ < 1/2` for `λ > 4`.
The bounded range `2 ≤ λ ≤ 4` must be handled separately (or the cited
interface must be restated with a compatible range).

## 2026-08-13 10:26:15 -04:00

The blueprint's Mikhlin theorem assumes three derivatives because it is
two-dimensional.  A dimension-generic formulation needs a dimension-dependent
derivative order (for example `⌊d / 2⌋ + 1`, or the stronger convenient order
`d + 1`), rather than a fixed `C³` hypothesis.

## 2026-08-13 10:26:15 -04:00

The radial-majorant lemma is written in dimension two.  Its dimension-generic
version has kernel scale `r⁻ᵈ` and needs a decay exponent `N > d`; the annular
sum has exponent `N - d`.

## 2026-08-13 10:26:15 -04:00

The blueprint defines circular averages using `f (x - t • ω)`, while the
repository's public `Spherical.sphericalAverage` uses `f (x + t • ω)`.  The
two agree after the antipodal symmetry of normalized spherical measure, but
the Lean development must use the repository convention and adjust the signs
in its Fourier identities.

## 2026-08-13 10:26:15 -04:00

The blueprint uses the Fourier phase `exp (-i x · ξ)`.  Mathlib's Fourier
infrastructure carries a `2π` normalization.  Accordingly, compatible
half-wave phases are normalized as `exp (± 2π i t |ξ|)`; this changes constants
and phases but not the frequency exponents in the argument.

## 2026-08-13 10:26:15 -04:00

The blueprint treats separated time sets as sets while summing over them.
Lean will use finite sets (or prove finiteness from compactness and
separation) before forming the discrete local-smoothing sum.

## 2026-08-13 10:26:15 -04:00

The requested final diagonal theorem quantifies over `p : ENNReal`, including
`p = ⊤`.  Bourgain/MSS supplies only finite exponents.  The planar branch must
therefore combine its finite-`p` bound with a separate elementary `L∞`
contraction argument.

## 2026-08-13 10:26:15 -04:00

The blueprint explicitly cites the plate-overlap, Fourier-cube square-function,
and light-ray/Kakeya inputs.  No corresponding Mathlib theorem is currently
available under those names, so the requested standard-axiom formalization
requires actual proofs or a later repository-provided replacement; they cannot
be introduced as axioms.

## 2026-08-13 10:57:57 -04:00

The blueprint treats Mikhlin, Littlewood--Paley, Riesz--Thorin, and the MSS
geometric estimates as imported/cited analytic inputs, while the task requires
their standard-axiom Lean proofs.  In the current checked-in source, there is
no generic Mikhlin weak-`(1,1)` theorem, full-`p` Littlewood--Paley or
vector-valued Calderón--Zygmund theorem, or complex `L^p` interpolation
theorem.  The existing Calderón--Zygmund development is specialized to
spherical relative-bandpass operators (and its packaged endpoints require
dimension at least three), so it cannot discharge those cited inputs without
substantial new foundational development.

## 2026-08-13 10:57:57 -04:00

The available planar circle theorem is a local/fractal-dilation estimate for
radius sets of strictly sub-one upper Minkowski exponent.  A full unit interval
of radii has exponent one, and rescaling that local theorem to dyadic radius
blocks produces uniform, not summable, constants.  Thus it cannot supply the
all-radii `d = 2` branch required to replace the `d \ge 3` hypothesis in the
existing diagonal theorem.

## 2026-08-13 13:22:00 -04:00

The exact planar coordinate-meridian wave normal form cannot currently be
imported safely into `Bourgain.lean`.  Its dependency chain reaches
`SmoothEndpointAmplitude.lean` through `QuadraticStationaryPhase`; a direct
source compilation fails at lines 189, 197, 230, 245, and 263 (two unclosed
`ContDiff.comp` coercion goals, two unresolved `𝓝` identifiers, and a stuck
`NormedSpace` instance).  The corresponding `.olean` files are absent, so
using that normal form would require a broken source dependency or stale
artifacts.  The import and re-exported decomposition have therefore been
removed.  The already source-checked `circleStationaryPhase` Fourier-bound
interface remains the safe Bourgain input.

## 2026-08-13 13:52:00 -04:00

The immediate `SmoothEndpointAmplitude.lean` obstruction from the preceding
entry was a Lean-version compatibility problem rather than a mathematical
discrepancy.  Its complexification proofs now state the continuous-linear-map
composition literally, stale neighbourhood notation was replaced by `nhds`,
and the derivative congruence was given its concrete function types.  The
file source-compiles.  Rebuilding its dependent
`QuadraticStationaryPhase.lean` exposed further independent stale
integration-by-parts/coercion proofs, so the planar coordinate-wave normal
form remains unavailable until that entire source chain is repaired.

## 2026-08-13 14:09:04 -04:00

`QuadraticStationaryPhase.lean` has now also been repaired and source-checked.
The required changes were compatibility-level corrections to neighbourhood
notation, continuity/integrability arguments for the current
integration-by-parts API, explicit scalar coercions, and stale simplifier
steps.  Its compact quadratic stationary estimates remain mathematically the
same.  The next source gates are `QuadraticMomentDerivatives.lean`,
`PlanarEndpointAmplitude.lean`, and `CoordinateMeridianWaves.lean`; the
coordinate-wave normal form is still not imported into `Bourgain.lean` until
that whole chain has compiled.

## 2026-08-13 14:17:00 -04:00

`FractalDilations/CoordinateMeridianWaves.lean` contained a stale endpoint
rewrite: after replacing the globally smooth endpoint amplitude by the cutoff
times `endpointQuadraticAmplitude`, the proof tried to close the literal
algebraic identity without unfolding the latter definition.  Lean therefore
retained the amplitude opaque and could not match the two sides.  An explicit
local unfolding resolves this elaboration-level discrepancy and the file now
source-compiles.  This does not change the blueprint argument or any stated
estimate.

## 2026-08-13 14:20:00 -04:00

The original parameter-derivative spelling in
`QuadraticMomentDerivatives.lean` conflated the raised quadratic moment with
the endpoint integral having a raised *profile index*.  Differentiating
`smoothEndpointQuadraticIntegral m` raises the monomial moment while keeping
the same smooth profile, so the literal result is
`quadraticMomentIntegral (m + 2*k) (smoothEndpointProfile m)`, not
`smoothEndpointQuadraticIntegral (m + 2*k)`.  The source proof was corrected
to this mathematically accurate identity and now source-compiles.  This is a
blueprint-level notation ambiguity rather than a change of the stationary
phase decay mechanism.

## 2026-08-13 14:35:56 -04:00

The planar stationary dependency chain is now source-clean through
`PlanarEndpointAmplitude.lean`, `CoordinateMeridianWaves.lean`, and
`PlanarCoordinateMeridianWaves.lean`.  The exact theorem
`surfaceFourier_two_eq_coordinatePlanarSmoothWaves` has consequently been
imported into `Bourgain.lean` and used to prove the literal outgoing/incoming/
middle Fourier decomposition.  This resolves the temporary unavailability
recorded at 13:22; it is not a new mathematical estimate.  The full
multiplier bounds and local-smoothing estimate remain separate outstanding
steps.

## 2026-08-13 14:35:56 -04:00

The initial Lean scaffold for `plateOverlap` quantified over an arbitrary map
`directions : Int → Euclidean 2`, while its angular-separation classes used
only the integer labels.  With no hypothesis relating labels to sector
directions, the stated uniform conic-plate overlap bound is false: all labels
can be assigned the same direction.  The MSS target must therefore include
explicit ordered angular-sector geometry (or use concrete sector data) before
the geometric overlap theorem can be proved.  This is an omitted hypothesis
in the translation of the blueprint's phrase “indices by consecutive integers
in increasing angular order.”

## 2026-08-13 14:42:30 -04:00

The `plateOverlap` target has been corrected to require
`angularSectorGeometry`: unit direction centres in a fixed narrow sector and
two-sided chordal-spacing control by the consecutive integer labels at scale
`scale^(-1/2)`. Its quantifiers now have the blueprint-compatible order
`∀ gamma, ∃ Cgamma`; in particular, the normal-thickness constant may depend
on `gamma`. This fixes the earlier false target but does not prove the
geometric overlap estimate, which remains an outstanding foundational step.

## 2026-08-13 14:52:24 -04:00

At equal radial frequencies, the zero-thickness model already shows that a
literal multiplicity-one pair-sum claim is false for ordered angular pairs:
`(ν, ν')` and `(ν', ν)` have the same sum whenever they are distinct. The
formal model consequently uses the sharp elementary two-to-one formulation
as its first possible injection target. The blueprint's stated overlap bound
is compatible with this constant factor, but a Lean proof must not silently
replace ordered pairs by an injective family.

## 2026-08-13 14:56:30 -04:00

The repository's repaired planar Q4 triple-wave and pair-kernel path is not
an alternative proof of Bourgain's full-radius theorem. Its dyadic maximal
rate theorems require `HasSubpowerAssouadCoverBound E gamma ...`; in ambient
dimension two the applicable regimes have `gamma < 1/2` (with a separate
critical `gamma = 1/2` result). The full interval `[1,2]` has local covering
dimension one, so it cannot satisfy these hypotheses. Those results also
control fractal dyadic maximal operators rather than the unit-time wave
local-smoothing estimate required here.

## 2026-08-13 15:16:55 -04:00

The blueprint states its circle stationary-phase expansion directly as two
outgoing/incoming symbols.  The source-clean coordinate-meridian construction
first yields two endpoint quadratic integrals **and a literal middle-meridian
integral**.  `Bourgain.lean` therefore records an exact three-wave identity.
The middle term can only be absorbed into the two-symbol formulation after a
uniform nonstationary integration-by-parts/symbol estimate is proved.  Keeping
it explicit is mathematically equivalent to the usual partition-of-unity
proof, but avoids silently treating the nonstationary remainder as zero.

## 2026-08-13 15:42:35 -04:00

The existing `CoordinateMiddleNonstationary.lean` is not source-compatible
with the repaired coordinate-meridian chain.  A direct rebuild exposes
stale trigonometric rewrite orientations, interval-order (`uIcc` versus
`Icc`) obligations, complexification/coercion mismatches, and several
unfinished integration-by-parts algebra steps.  Its intended one-step
`O(|l|^{-1})` middle-meridian estimate is therefore not yet a usable input to
`Bourgain.lean`; the exact three-term decomposition continues to retain the
middle term explicitly.  This is a Lean/API repair backlog, not a reason to
discard the mathematically necessary middle nonstationary-phase estimate.

## 2026-08-13 16:06:10 -04:00

The repaired coordinate-middle integration-by-parts identity exposed an
indexing error in the original amplitude formula.  To recover a middle
density containing `cos(theta)^m` after multiplication by the sine-phase
derivative `cos(theta)`, the guarded amplitude must be
`cos(theta)^m / guard(theta)`, not `cos(theta)^(m - 1) / guard(theta)`.
The latter loses one power (and is especially misleading at `m = 0`).  The
source now uses the corrected formula and proves the intended `O(|l|^{-1})`
middle-meridian bound; this is a correction to the coordinate IBP bookkeeping,
not a change to the stationary/nonstationary decomposition.

## 2026-08-13 17:11:45 -04:00

`CoordinateMiddleRapidDecay.lean`, which is the all-orders version of the
middle-meridian nonstationary estimate, contained several stale Lean/API
forms: an unopened neighbourhood notation, a complex-valued quotient proved
with the scalar-field division lemma (although the differentiation scalar is
real), and a parenthesization error in the iterated integration-by-parts
factor.  The corrected proof treats division by the positive real cosine
guard as real scalar multiplication, and uses the mathematically correct
factor `(-(((-l : Complex) * I)⁻¹))^N`.  This repairs the intended rapid
decay statement; it does not alter the circle decomposition or introduce an
additional analytic hypothesis.

## 2026-08-13 17:18:50 -04:00

The blueprint states Riesz--Thorin directly from two `L^p` endpoint bounds.
Mathlib has Hadamard's three-lines theorem but does not package the analytic
input powers, normalized `L^{p'}` dual-test family, or the norming-duality
construction for arbitrary measure spaces.  The completed Lean theorem
`RieszThorinAnalyticDatum` / `rieszThorin` therefore makes precisely those
standard constructions explicit as datum fields and proves the advertised
geometric-mean conclusion from them.  This is the usual proof with no
additional mathematical assumption, but callers must now discharge the
analytic-power/measurability details instead of receiving an opaque global
library instance.

## 2026-08-13 17:25:13 -04:00

The preceding Riesz--Thorin entry was too optimistic for the requested
blueprint target.  A theorem whose hypotheses already contain the analytic
`L^p` deformations and norming-duality datum is a useful three-lines core,
but it is not the stated theorem from two endpoint `L^p` operator bounds.
The status has therefore been reverted to `ToDo`; the remaining work is to
construct those families and prove the scalar and `L^p(X; ell^2)` endpoint
interpolation statements directly, including the `p_1 = infinity` case.

## 2026-08-13 21:00:50 -04:00

The blueprint writes a linear operator directly on functions. In Lean, the
natural theorem must distinguish raw representatives from `Lp` equivalence
classes: endpoint estimates on a raw simple-function core determine a
bounded operator on the interpolated `Lp` space only after AE-compatibility
and completion are made explicit. The formal main theorem will therefore
state the standard bounded-extension conclusion (and an agreement statement
on the core), rather than applying an arbitrary representative-level map to
every `Lp` quotient element. This is a domain/formulation clarification, not
an additional analytic assumption or a weakening of the Riesz--Thorin bound.

## 2026-08-13 22:08:26 -04:00

The Riesz--Thorin discrepancy recorded above is now resolved.  The completed
`RieszThorin.lean` constructs the analytic powers and the norming dual test
directly from the literal endpoint estimates, proves the sharp finite-simple
core bound, and completes it to the interpolated `Lp` space.  Its public
finite-interior theorem supports an infinite endpoint through the ENNReal
reciprocal identity; direct `1,1` and `∞,∞` endpoint theorems cover the
degenerate cases.  The bounded-extension formulation remains intentional:
it is the precise Lean form of the conventional completion step used in the
blueprint.

## 2026-08-14 02:36:45 -04:00

The blueprint writes the planar Mikhlin hypothesis using conventional
multi-index notation `∂_ξ^α`. Mathlib does not expose a reusable
multi-index partial-derivative API for maps on `EuclideanSpace`; the source
therefore states `PlanarCoordinateMikhlinCondition` using the values of
`iteratedFDeriv` on every tuple of standard coordinate basis vectors. For a
`C³` symbol these are exactly the ordered coordinate derivatives, and the
new finite-dimensional multilinear expansion proves the needed invariant
bound with factor `2^3 = 8`. Thus this is a notation/interface translation,
not an extra regularity or analytic assumption; a literal syntax-level
equivalence to `∂_ξ^α` remains unformalized because that syntax is absent
from the library.

## 2026-08-14 03:05:00 -04:00

The blueprint's one-dimensional stationary-phase theorem invokes the local
Morse normal form as a standard black box. Mathlib has a smooth inverse
function theorem but no packaged one-dimensional Morse lemma that constructs
the signed square coordinate, its smooth inverse, the compactly supported
amplitude pullback, and the resulting interval-integral substitution in one
step. `OneDimStationaryPhase.lean` now exposes the proved conditional
`HasQuadraticNormalForm` transport layer instead: a concrete application
must supply the exact change-of-variables identity and its smooth compact
transported amplitude, after which the full order-`-1/2` derivative bounds
are proved. The general `stationaryPhase` theorem remains `ToDo`; this is a
formalization gap, not a claim that nondegenerate phases fail to admit the
usual Morse reduction.

## 2026-08-14 04:11:34 -04:00

The new theorem
`stationaryPhase_of_normalForm_and_rapidRemainder` composes an explicit
`HasQuadraticNormalForm` witness with a separately proved all-derivative
rapid remainder into the literal oscillatory-integral expansion.  It does
not close the original unrestricted blueprint theorem: constructing the
normal-form witness and deriving the remainder bounds from arbitrary smooth
phase/amplitude data remain concrete obligations.  The public conclusion is
therefore deliberately named as a conditional composition theorem, while
the original `stationaryPhase` status remains `ToDo`.

## 2026-08-14 04:27:27 -04:00

`HasNonstationaryRapidDecayData.hasRapidDecayRemainder` now proves the full
all-parameter-derivative rapid remainder estimate from a positive lower
bound for `|phaseDeriv|` and explicit nonlinear integration-by-parts chains
for every inserted parameter moment. It deliberately does not assert that
arbitrary smooth nonstationary data automatically produces those chains or
the endpoint vanishing they encode; constructing that concrete data remains
an application-specific obligation. Thus the unrestricted `stationaryPhase`
blueprint theorem remains `ToDo`.

## 2026-08-14 04:36:39 -04:00

The new smooth nonstationary construction derives the full explicit
integration-by-parts chain, and hence `HasRapidDecayRemainder`, from a
`C∞` amplitude vanishing near both integration endpoints and a `C∞` phase
derivative that is globally nonzero. The more flexible version accepts a
globally smooth nonvanishing extension `phaseDeriv` which only has to agree
with the actual phase derivative on the integration interval. A merely local
lower bound for the actual derivative does not yet automatically construct
that global smooth reciprocal extension; Mathlib's `ContDiff.inv` API is
global. This limitation is explicit in the hypotheses, so no local
nonstationary assertion is being overstated.

## 2026-08-14 04:51:05 -04:00

`HasTwoBranchQuadraticMorseChart.toHasQuadraticNormalForm` now turns an
explicit pair of smooth inverse Morse branches into the existing normal-form
witness. It proves both branch substitutions with
`intervalIntegral.integral_deriv_smul_comp`, combines their Jacobian-weighted
amplitudes, and derives smoothness plus endpoint vanishing from a smooth
amplitude that vanishes near the two outer chart endpoints. The chart records
`φ'(s₀)=0`, `φ''(s₀)≠0`, the orientation, endpoints, and exact quadratic phase
identities. What remains open is construction of those two smooth branches
from only the bare nondegenerate-critical-point hypotheses; the original
unrestricted `stationaryPhase` theorem therefore remains `ToDo`.

## 2026-08-14 05:00:35 -04:00

`localInverse_of_contDiffAt_of_hasDerivAt_ne` and
`HasLocalQuadraticMorseCoordinate.toHasLocalQuadraticMorseInverse` now make
the inverse-function portion of the local one-dimensional Morse argument
explicit. They use Mathlib's `ContDiffAt.localInverse` to turn a supplied
smooth signed quadratic coordinate with nonzero derivative into a smooth
local inverse satisfying the exact quadratic phase identity near zero. This
does not construct that coordinate from `phi'(s0)=0` and
`phi''(s0) != 0`, nor does it extend the local inverse to the two global
branches/endpoints required by `HasTwoBranchQuadraticMorseChart`. Those are
still the remaining Hadamard-factorization and extension obligations, so the
unrestricted `stationaryPhase` theorem remains `ToDo`.

## 2026-08-14 05:04:59 -04:00

The canonical `quadraticHadamardFactor`, defined as an iterated `dslope`, now
has a source-compiled exact identity
`phase x - phase s0 = (x - s0)^2 * quadraticHadamardFactor phase s0 x` at a
critical point. This isolates the factorization algebra without making a
false regularity claim: Mathlib's `DSlope` API provides the exact identity,
but not a theorem that an iterated divided difference of a C-infinity real
map is C-infinity at the diagonal. The Taylor-integral formula supplies an
alternative exact factor, but the same missing parametric-integral
smoothness theorem remains. Thus this is progress toward, not completion of,
the bare Morse-chart construction.

## 2026-08-14 05:52:59 -04:00

The earlier parametric-integral regularity gap has now been closed in
`OneDimStationaryPhase.lean`. `affineMomentAverage` differentiates under the
integral using `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
after a local compact uniform-bound construction; a finite-order induction
then gives its `C∞` regularity. The exact Taylor-integral factor
`quadraticTaylorFactor` consequently has both a global `C∞` theorem and the
identity `phase x - phase s0 = (x - s0)^2 * quadraticTaylorFactor phase s0`
at a critical point.

`HasLocalQuadraticMorseCoordinate.ofNondegenerate` now constructs a signed
local square-root coordinate from `C∞` phase data, `phase'(s0) = 0`, and
`phase''(s0) ≠ 0`; its exact local quadratic phase identity and nonzero
coordinate derivative are source-compiled. This is deliberately only a
local chart/transport result. It does not construct two globally defined
inverse branches over prescribed endpoints, a global compactly supported
amplitude transport, or a stationary/nonstationary amplitude split.
Accordingly `HasTwoBranchQuadraticMorseChart` and `HasQuadraticNormalForm`
still require explicit global extension/transport data, and the original
unrestricted `stationaryPhase` theorem remains `ToDo`.

## 2026-08-14 06:13:48 -04:00

A bare local Morse coordinate cannot soundly instantiate the pre-existing
unit-endpoint `HasTwoBranchQuadraticMorseChart`: that structure requires
`phase (branch 1) = phase s0 + epsilon`, whereas a local inverse only supplies
coordinates in some interval `|u| < radius`, and there is no reason for that
radius to contain one (a smooth nondegenerate phase can have total variation
strictly below one).  Localizing the amplitude does not make those global
phase-identity fields true.

There is also a Lean-specific regularity distinction: the present local
inverse has `ContDiffAt ... ∞`, which supplies every finite derivative at the
base point but does not promote via `ContDiffAt.contDiffOn` to one
neighbourhood-level all-order smoothness certificate.  It therefore cannot
by itself certify globally smooth branch extensions after a bump cutoff.
The development now proves a positive local coordinate radius from bare
nondegenerate data and introduces an explicit globally-smooth,
radius-scaled chart/normal-form interface.  Its exact transport uses
`radius^2 * lambda`, with the matching high-frequency symbol estimate.  The
global branch-extension/localization construction remains an explicit
application obligation; no unrestricted `stationaryPhase` claim has been
made.

## 2026-08-14 07:35:11 -04:00

`aux_HasLightRayTTStarIntersectionSchurEstimate` quantifies over every
unit-valued direction field `direction : Euclidean 2 -> Euclidean 2`, but
asks each literal TT* row to be `Integrable`. Unit length alone gives no
measurability: the row contains
`lightRayKernel delta N (direction y') y' (x, t)`, so an arbitrary
nonmeasurable selection can make even this terminal-variable factor
nonmeasurable. Thus the stated unrestricted Schur predicate is not a sound
formulation of the continuum Córdoba input.

The original declaration is retained to avoid silently changing downstream
interfaces. MSS now proves the minimal safe analytic fact
`aestronglyMeasurable_lightRayKernel_terminal_of_aestronglyMeasurable_direction`:
an `AEStronglyMeasurable` direction field makes every fixed space-time
kernel slice strongly measurable. A completed Kakeya/TT* theorem must take
such direction regularity (and the remaining joint Fubini and geometric row
estimate) explicitly; the pairwise hard-tube geometry and spatial mass
normalization do not by themselves supply Córdoba's logarithmic estimate.

## 2026-08-14 11:09:38 -04:00

`CentralMeridianIBP.lean` and `CoordinateMiddleParameterDerivatives.lean`
had accumulated Lean-version compatibility failures in their already intended
compact nonstationary-phase proofs: obsolete neighbourhood notation,
real-versus-complex scalar differentiation for the guarded reciprocal,
interval endpoint coercions, and a parenthesized iterated-IBP factor. The
repair now source-compiles both modules and retains the literal formulas.
In particular, the public all-order estimate
`exists_iteratedDeriv_coordinateMiddleMeridianLocalizedIntegral_abs_decay`
is available without a new analytic hypothesis. The independently failing
`CoordinateWaveRegularity.lean` import chain is not used by this repair and
remains a separate legacy proof backlog.

## 2026-08-19 21:33:17 -04:00

The former foundational thick-plate-overlap gap is now discharged for the
literal `angularSectorGeometry` formulation.  The new theorem
`translatedUnitNormalPlateOverlap_of_angularSectorGeometry` proves the
existing predicate without an additional geometric assumption.  Its proof
does not use the false direct-or-swap clustering claim: it splits low scale,
the zero separation class, and the high tangent/positive-area/negative-area
regimes, obtains uniform directional caps from the coupled time and normal
constraints, and converts each cap to a finite label box via the supplied
chordal spacing.  The one-line corollary
`plateOverlap_of_angularSectorGeometry` then closes the existing normal-cover
transfer (with its intended positivity assumption on `angularConstant`).
Direct MSS compilation and the MSS module build both pass; the earlier notes
about the missing ordered-sector hypothesis remain historical explanations of
the corrected target rather than current blockers.

## 2026-08-19 21:49:36 -04:00

The literal finite bridge from a supplied cube realization to plate-overlap
fibers is now source-proved.  It takes direct data: a cube owner into angular
pairs, an output-frequency label, pair-separation and Minkowski-sum facts,
and injectivity of the owner together with the output label.  The resulting
`card_plateOverlapCubeOutputFiber_le_plateOverlapMultiplicity_of_pairRealization`
injects each finite output fiber into the existing `plateOverlapPairs` fiber;
its scaled corollary consumes `plateOverlap`.

This does **not** yet instantiate the existing `angularDyadicCubePacket`
layer.  That packet API has a finite spatial Fourier-cube family and a
reconstruction identity for an explicitly supplied owner map, but it has no
space-time output-cell label and no theorem placing the packet's
`spaceTimeFourier` support in a `conicPlate`.  In particular the packet has
no radial label or normal-frequency localization, and its time cutoff is
arbitrary.  A true analytic realization must construct these labels/cells,
prove the per-packet conic plate support (or first connect it to the
wavefront-projected radial/angular packets), and prove the needed fiberwise
injectivity before the finite plate theorem can feed the fine-cube or
continuum square-function argument.

## 2026-08-19 22:01:21 -04:00

The missing bridge has narrowed, but it is still genuinely analytic.  The
source now proves the exact fixed-time spatial Fourier formula for
`angularDyadicCubePiece`, its support in the supplied `frequencyCube`, the
scaled-ray specialization, and the identity expressing a singleton
`angularDyadicCubePacket` as its time cutoff times that piece.  These facts
give literal spatial-frequency data for an actual packet; they do **not**
give a `spaceTimeFourier` support theorem.

To feed `plateOverlapPairs`, the next concrete theorem must add a normal/radial
frequency label and prove that the space-time Fourier support of the relevant
packet lies in the corresponding `conicPlate`.  The present packet allows an
arbitrary time cutoff and carries neither that label nor a normal-frequency
cutoff, so no such conclusion follows from its fixed-time spatial support.
Equivalently, one needs a proved connection to the existing
`wavefrontAngularRadialWave` plate-support API (or a new literal normal
Fourier decomposition), followed by actual output-cell labels and the
fiberwise injectivity needed by the finite realization lemma.

## 2026-08-19 23:11:12 -04:00

The finite vertical route now has literal separable-packet `L²` and
pointwise `L∞` endpoint lemmas.  The latter is
`norm_verticalRecombined_verticalSeparablePackets_le_of_schwartz_profiles_of_common_time_kernel`:
it requires actual Schwartz representatives of the translated temporal
multipliers and an explicit inverse-Fourier common time-envelope hypothesis.
Together with a uniform spatial square envelope it gives a finite pointwise
`L∞` bound, without invoking the abstract `verticalRecombination` predicate.

What remains is not a missing finite-sum inequality.  The current source
does not construct the required common time-kernel bound for the radial
pieces/physical-time-cutoff half-waves, nor does it package those pieces as a
single linear vector-valued operator on a density class suitable for the
eventual Riesz--Thorin step.  That construction must prove the kernel or
multiplier estimates with their scale dependence, connect the supplied
Schwartz profiles to the actual radial/half-wave inputs, and retain the
finite-to-continuum convergence hypotheses already exposed by the existing
closedness theorem.  No unconditional continuum vertical-recombination
estimate has been inferred from the finite endpoint.

## 2026-08-19 23:26:14 -04:00

The finite missing interpolation inequality is now source-proved as
`eLpNorm_four_rpow_two_verticalRecombined_verticalSeparablePackets_le_of_schwartz_profiles_of_common_time_kernel_and_spatial_envelope`.
It applies the concrete `L²`--`L⁴`--`L∞` log-convexity lemma to the actual
finite `verticalRecombined` output after proving its Schwartz-profile
measurability.  Its right-hand side retains the literal input-energy sum,
the Fourier-overlap constant, and the common-time-kernel/spatial-envelope
constant.

This closes the finite packet-level interpolation step only.  It does not
construct the required common kernel for the actual radial/half-wave pieces,
extend the finite Schwartz core to a linear vector-valued density class, or
infer any continuum `verticalRecombination` estimate.

## 2026-08-20 00:45:10 -04:00

The wavefront frontier now has a literal spectral conic-plate bridge.
`spectralCubeRadialNormalPacket` is the vertical projection of the separable
Schwartz tensor `(FourierInv cubeProfile) ⊗ g`.  Its exact space-time Fourier
formula is the product of the vertical factor, the actual Schwartz cube
profile, and the temporal Fourier profile.  The new support theorem places
that packet in the exact `conicPlate` whenever the displayed spatial
radial/angular, vertical-band, and joint normal spectral conditions hold.
The cube specialization consumes the existing `isFourierCubeCutoff` interface,
and the finite-family corollary has exactly the support-premise shape required
by `overlapSquareFunction`.

This deliberately does not prove `wavefrontPlateSupport` for
`wavefrontAngularRadialWave` or give a space-time conic-support theorem for
`angularDyadicCubePacket`: their compact physical-time cutoff may have
noncompact temporal Fourier support.  The next necessary construction is a
finite radial/angular family of such Schwartz spectral packets, together with
a quantitative reconstruction or rapidly decaying off-plate error from the
actual compact-time half-wave pieces.  Only after that analytic bridge can
the existing output-cell and fiber-injectivity realization feed the finite
plate-overlap estimate.

## 2026-08-20 00:56:09 -04:00

The spectral packet family now has two literal downstream consumers.  First,
`overlapSquareFunction_spectralCubeRadialNormalPackets` supplies the exact
finite-family conic support premise to the analytic `overlapSquareFunction`
hypothesis; its separate plate-overlap premise is discharged by the proved
`plateOverlap_of_angularSectorGeometry` theorem.  Second,
`exists_finitePlateOverlapSquareEnergy_spectralCubeRadialNormalPackets_le_scaled`
uses that same geometry to bound the actual finite `finitePlateOverlapSquareEnergy`
formed from two fixed radial spectral packet families, for an explicit finite
set of output-frequency labels.  Its conclusion also records the conic-plate
support of both packet factors.

These are model-level consequences only.  The former still assumes the
analytic `overlapSquareFunction`, and the latter uses plate-pair filtered
output labels rather than claiming a physical compact-time packet-product
realization.  The missing bridge remains a quantitative passage from the
literal compact-time half-wave cube packets to these spectral Schwartz
packets (or an off-plate error formulation), followed by output-cell and
fiber-injectivity data for their products.

## 2026-08-20 01:32:35 -04:00

The finite spectral cube/radial-normal model was checked against the literal
vertical-recombination API.  There is an exact finite type-level packing when
the temporal Schwartz profile `g n` is shared by all angular labels at a
fixed radial label: after summing the angular cube factors,
`∑ n ∑ ν spectralCubeRadialNormalPacket ... n cubeProfile[n,ν] (g n)` is
literally `∑ n V_n H_n`, where `H n` is the corresponding packed separable
Schwartz tensor.  The raw packed
`aux_angularRadialRecombinedSquareFunction` is exactly
`verticalSquareFunction H`; the analogous square function of the spectral
packets is instead `verticalSquareFunction (fun n => V_n (H n))`.

Thus this is a genuine finite specialization of the *objects* in the
vertical-recombination path, but it does not prove its estimate.  The present
finite Schwartz `L²`/`L∞`/interpolated-`L⁴` results bound the total output by
an explicit input-energy times common-time-kernel/spatial-envelope expression.
They do not give the required vector-valued comparison
`‖∑ n V_n H_n‖₄ ≤ scale^gain ‖verticalSquareFunction H‖₄` (nor the needed
scale gain).  Proving that finite vector-valued `L⁴` endpoint, and only then
handling its density/continuum passage, remains the next real recombination
theorem.  No source theorem was added from the scratch audit.

## 2026-08-20 13:06:49 -04:00

The source now has the literal finite-model transfer
`overlapSquareFunction_spectralCubeRadialNormalPackets_to_fineSquareFunction_of_model`.
It consumes `overlapSquareFunction_spectralCubeRadialNormalPackets` and an
explicit equality, for every selected radial/angular index, between the
spectral Schwartz packet and the corresponding actual angular/radial piece.
It therefore transfers the auxiliary recombined square-function `L4` bound to
the angular/radial square function (the later `fineSquareFunction` definition
unfolded) with the same `C * scale^eta` loss.

This is deliberately conditional on the supplied finite realization equality;
it does not construct that equality, claim exact conic-plate support for a
compact physical-time cutoff, or turn the analytic `overlapSquareFunction`
hypothesis into a proof.  In particular it supplies no bound from the fine
square function to the original input, so `fineSquareFunctionEstimate`, the
continuum realization/reverse-overlap step, and the remaining recombination
work are still open.

## 2026-08-20 13:19:33 -04:00

The raw product type `WaveSpaceTime = Euclidean 2 × Real` does not carry the
joint inner-product structure required by Mathlib's `SchwartzMap`.  The new
Fourier-conversion layer therefore works on the explicitly corrected Hilbert
coordinate model `JointWaveSpaceTime = WithLp 2 WaveSpaceTime`, with
`jointSchwartzRaw` returning to the physical product coordinates.  Its
volume transport is proved through Borel measurability because the
`WithLp.measurableSpace` instance and the Haar/Borel structure selected by
the canonical joint Fourier transform are not definitionally identical.

For an explicitly supplied joint Schwartz cutoff `q`, the literal premise
`wavefrontMultiplier … * FourierTransform.fourier G = q *
FourierTransform.fourier G` yields both a raw `wavefrontProjection` identity
and the exact `conicPlate` support statement consumed by
`overlapSquareFunction`.  This is a spectral realization theorem, not a
producer for the premise.  It deliberately does not apply to
`angularRadialWave`, `wavefrontAngularRadialWave`, or another compact
physical-time cutoff: compact temporal localization generally broadens the
normal Fourier variable and cannot justify exact conic support.  The remaining
analytic task is to construct suitable local joint-Schwartz spectral cutoffs
and a quantitative approximation/off-plate-error bridge from the actual
compact-time half-wave packets.

## 2026-08-20 13:30:02 -04:00

The finite Schwartz vertical layer now has a genuinely additive bundle core:
`verticalTemporalSchwartzMultiplier`,
`verticalTemporalSchwartzCoreRecombined`, and
`verticalSchwartzCoreRecombined`.  Under an explicit finite profile equality,
the temporal and space--time cores identify exactly with the literal sums of
`verticalTemporalProjection` and `verticalRecombined` on separable Schwartz
packets.  Their finite-overlap raw `L²` bounds are exposed as source theorems.
The finite vertical square function is also identified exactly with the norm
of its natural finite `PiLp 2` bundle (and hence has the corresponding all-p
`eLpNorm` equality).

This is deliberately only a finite Schwartz additive core.  It does not
construct a common time kernel, establish an `L∞` endpoint for the bundle
operator, interpolate an `L⁴` recombination bound, or extend the construction
to arbitrary measurable inputs or a continuum limit.  Those remain the
missing analytic recombination work.

## 2026-08-20 13:42:18 -04:00

The finite temporal Schwartz multiplier now has an exact convolution
identity and a scalar `L1`-kernel-to-`L∞` estimate. This removes the prior
ambiguity about the physical kernel of one temporal block, but it does not
yet give the needed vector-valued endpoint. The next honest step is a common
pointwise kernel-envelope theorem for the finite temporal core, yielding the
sharp `sqrt indices.card` top bound against the `PiLp 2` input norm. Turning
that finite Schwartz result into the all-input, measurable additive operator
required by `rieszThorin_two_top_four_of_additive` still needs an
extension/density construction. Do not derive an L4 recombination estimate
merely from the existing profile-specific L2 and L∞ energy bounds; that
would have the wrong source norm.

## 2026-08-20 13:49:36 -04:00

`norm_verticalTemporalSchwartzCoreRecombined_le_of_common_kernel` now proves
the sharp finite `sqrt indices.card` top estimate from a supplied nonnegative,
integrable common pointwise envelope for the inverse-Fourier temporal kernels.
It is the correct finite-core L∞ endpoint and uses the input temporal square
function, rather than separately bounding every input component.

The remaining obstacle is exactly the advertised one: its domain is still a
finite family of Schwartz profiles. A subsequent all-input operator must
extend this core to measurable `PiLp 2`-valued functions, retain the finite
L2 overlap estimate, and prove AEMeasurability before the existing
Riesz--Thorin theorem can be applied. No such extension, continuum passage,
or `verticalRecombination` theorem has been claimed here.

## 2026-08-20 13:56:24 -04:00

`jointSchwartzExternalProduct` now rigorously packages a planar Schwartz
profile `B(ξ)` and a temporal Schwartz profile `h(τ)` as genuinely joint
Schwartz data on `JointWaveSpaceTime = WithLp 2 (Euclidean 2 × Real)`, with
the exact raw-coordinate formula at `WithLp.toLp 2 (ξ, τ)`.  Its proof uses
coordinate derivative contractions, the finite Leibniz rule, and Schwartz
seminorm decay; it does not add any unsupported regularity assumption.

This is only the first tensor-product foundation for the compact-time
spectral-tail route.  It does not construct a smooth annular radial extension
equal to `‖ξ‖`, a Schwartz shear by that extension, the profile
`B(ξ) * FourierTransform.fourier ϑ (τ - ‖ξ‖)`, a physical half-wave equality,
or exact conic support for a compact physical-time cutoff.  The latter is
generally false without a quantitative off-plate tail formulation.

## 2026-08-20 13:59:53 -04:00

The finite temporal input square function now has an exact pointwise and
all-exponent `eLpNorm` identification with the natural finite `PiLp 2`
bundle. This aligns the existing common-kernel top estimate with the eventual
Riesz--Thorin source geometry. It does not itself define an operator on
measurable bundle-valued data, provide the required L2 extension, or remove
the density/AEMeasurability gap.

## 2026-08-20 14:09:33 -04:00

`smoothAnnularNormExtension` now proves the small smooth spectral foundation
needed for the radial-shear route. Given a real planar Schwartz cutoff `u`, a
compact-support witness, `epsilon > 0`, and literal vanishing of `u` on the
open `epsilon`-ball around the origin, it constructs the Schwartz map
`x |-> u x * ||x||`. The public evaluation and equality-on-one/support
corollaries make the radial-norm identification available exactly on the
chosen profile support.

This is purely a smooth spectral construction. It supplies neither a
physical half-wave identity nor compact physical-time/conic-plate support;
those still require the planned shear and a separate Fourier-modulation or
quantitative off-plate-tail argument.

## 2026-08-20 14:22:01 -04:00

`jointSchwartzPrecompRadialShear` now implements that planned shear on the
genuine joint Schwartz space.  For any real planar Schwartz profile `rho` and
joint Schwartz profile `Q`, it returns a joint Schwartz profile whose raw
formula is exactly
`Q (WithLp.toLp 2 (xi, tau - rho xi))`.  Its `SchwartzMap.compCLM` proof is
honest: the shear has temperate growth because it is the identity minus a
continuous-linear vertical embedding of `rho` after the first-coordinate
projection; its properness bound uses `rho.decay 0 0` and has degree one.

Together with `smoothAnnularNormExtension`, this supports a future profile
formula with a smooth extension that agrees with `||xi||` on a chosen
annular spatial support.  It does not identify that profile with a compact
physical-time half-wave, prove a Fourier modulation theorem, or establish
exact conic-plate support.  Those require a separate physical-to-spectral or
quantitative off-plate-tail argument.

## 2026-08-20 14:27:06 -04:00

`jointSchwartzModulatedAnnularProfile` now makes that spectral profile
literal: it applies the public radial shear to the joint external product of
`B` and `FourierTransform.fourier vartheta`, giving exactly
`B xi * FourierTransform.fourier vartheta (tau - rho xi)` in raw product
coordinates. Its support corollary replaces `rho xi` by `||xi||` under the
literal hypothesis that `rho` agrees with the norm on the support of `B`.

This remains a joint-Schwartz spectral identity only. It does not prove an
inverse space-time Fourier formula, a physical compact-time half-wave
identity, or exact conic-plate support. The next bridge needs the separate
Fourier-translation/Fubini calculation (or a quantitative off-plate-tail
version) before any such statement can be made.

## 2026-08-20 14:47:41 -04:00

The required Fourier-translation/Fubini bridge is now source-verified for
supplied Schwartz data only.  The public theorem
`spaceTimeFourierInv_jointSchwartzModulatedAnnularProfile` identifies the
literal joint inverse profile with
`vartheta t * FourierTransform.fourierInv (fun xi => B xi *
Real.fourierChar (rho xi * t)) x`.  Under the literal hypothesis that `rho`
equals `||xi||` on the support of `B`, its public corollary identifies that
phase with `halfWaveMultiplier WaveSign.plus t xi`.

This is an exact temporal-Schwartz identity; it does not assert that an
arbitrary Schwartz `vartheta` has compact physical-time support.  It makes no
claim about legacy `angularPiece`, conic-plate support, off-plate tails,
approximation, recombination, fine square functions, or `p4LocalSmoothing`.

## 2026-08-20 14:56:59 -04:00

The generic joint-Schwartz inversion conversion is now source-verified:
`spaceTimeFourier_spaceTimeFourierInv_jointSchwartzRaw` derives directly from
the existing forward and inverse raw-coordinate conversions together with
`FourierTransform.fourier_fourierInv_eq`. Its supplied-data corollary
`spaceTimeFourier_temporalSchwartzHalfWave_eq_jointSchwartzModulatedAnnularProfile`
identifies the iterated Fourier transform of the temporal-Schwartz positive
annular half-wave with the already-defined joint modulated annular profile.

This adds no compact conic-support statement: `vartheta` remains an arbitrary
supplied Schwartz map, and the conclusion is only an exact spectral profile
identity. It does not establish a plate condition, off-plate decay,
approximation, legacy `angularPiece` realization, recombination, fine square
function estimate, or local smoothing bound.

## 2026-08-20 15:12:42 -04:00

The first honest projected spatial/normal model is now source-verified.
`jointSchwartzSpatialNormalCutoff u beta rho` has literal raw value
`u xi * beta (tau - rho xi)`, and
`temporalSchwartzAnnularNormalProjection` applies that joint Schwartz cutoff
to the Fourier profile of the supplied temporal-Schwartz annular half-wave.
Its public Fourier identity is exact.

The public conic-plate theorem applies only to this projected output and
requires all of the following literal hypotheses: spatial radial/angular
containment of `support B`; a vertical-label bound for each `xi` in
`support B` and normal value `s` in `support beta`; and a normal-width bound
on `support beta`, in addition to `rho = ||.||` and `u = 1` on `support B`.
No compactness follows from the Schwartz cutoff data alone. In particular,
there is still no Fourier-support claim for the unprojected temporal cutoff
half-wave, no legacy `angularPiece` realization, approximation or quantitative
tail theorem, recombination, fine square-function estimate, or local smoothing
result.

## 2026-08-20 15:42:44 -04:00

The verified normal-tail split for the temporal-Schwartz annular model is an
exact spectral identity, not a quantitative tail bound. Its Fourier factor is
`1 - u xi * beta (tau - rho xi)`. Consequently the honest support exclusion
is the region where `beta (tau - rho xi) != 1` (assuming `u = 1` on
`support B`), not merely the complement of `support beta`: a nonzero cutoff
value different from one still contributes to the tail.

The reassembly theorem requires the supplied agreement `rho = ||.||` on
`support B` to identify the joint-Schwartz inverse profile with the literal
positive half-wave. It does not assert plate support for that unprojected
half-wave, compact physical-time support, approximation, off-plate decay, a
quantitative tail estimate, recombination, a fine square function, or local
smoothing.

## 2026-08-20 16:50:51 -04:00

The earlier finite-vector density/AEMeasurability obstruction is resolved for
the concrete restricted domain only. `MSS.lean` now proves
`memLp_four_and_eLpNorm_finiteTemporalCommonKernelOutput_of_overlap` for a
literally measurable, bounded, coordinatewise-integrable finite `PiLp 2`
temporal bundle under the stated profile and finite-overlap hypotheses.
The result controls the literal finite common-kernel convolution output and
has an explicit fourth-moment coefficient.

This is not an all-input vector-valued multiplier theorem. The proof does
not extend the operator to arbitrary measurable `Lp` data, and it does not
produce `verticalRecombination`, a continuum limit, a spacetime packet
estimate, a fine square-function bound, or local smoothing. Those remain
separate consumers/problems; do not use this finite restricted-domain result
to bypass their hypotheses.

## 2026-08-20 17:05:10 -04:00

The finite Schwartz-profile consumer is now source-verified.  The public
theorem
`memLp_four_and_eLpNorm_verticalTemporalSchwartzCoreRecombined_of_overlap`
packages a supplied finite family `Int → SchwartzMap Real Complex` into the
concrete finite `PiLp 2` measurable domain, invokes the existing literal
common-kernel endpoint, and rewrites its output to
`verticalTemporalSchwartzCoreRecombined`.  Its fourth-moment right-hand side
is exactly the existing `finiteTemporalCoreFourthMomentBound` evaluated on
that concrete bundle.

This remains a finite temporal Schwartz-core corollary.  It does not extend
the endpoint to arbitrary vector-valued `Lp` inputs, and it does not prove a
spatial, continuum, half-wave, spacetime packet, recombination, fine
square-function, or local-smoothing statement.

## 2026-08-20 17:12:35 -04:00

The product-measure concern for the common-spatial finite core is resolved in
the literal finite setting. The proof of
`memLp_four_and_eLpNorm_verticalSchwartzCoreRecombined_commonSpatial_of_overlap`
uses `Measure.volume_eq_prod`, `lintegral_prod_mul`, and
`ENNReal.mul_rpow_of_nonneg` to obtain the exact fourth-`eLpNorm` tensor
factorization. The temporal output's `AEStronglyMeasurable.comp_snd` and the
Schwartz profile's `comp_fst` give the required product measurability.

This is not a way around the remaining scope boundaries: the theorem requires
one common spatial Schwartz profile, finite temporal Schwartz data, and the
existing finite-overlap temporal hypotheses. It gives no estimate for varying
spatial profiles, arbitrary measurable bundles, `verticalRecombined`,
continuum reassembly, spacetime packets, fine square functions, or local
smoothing.

## 2026-08-20 17:30:56 -04:00

The finite varying-spatial Schwartz-core consumer is now source-verified:
`memLp_four_and_eLpNorm_verticalSchwartzCoreRecombined_of_overlap`. It applies
the common-spatial finite theorem to the singleton temporal family supported
at each `n ∈ indices`, identifies their finite sum with
`verticalSchwartzCoreRecombined indices m F g`, and uses finite Minkowski.
The public RHS is the explicit finite sum of each spatial fourth `eLpNorm`
times the existing fourth-moment bound for that singleton bundle.

This is a finite, supplied-Schwartz, deliberately non-square-function bound.
It does not yield a single spatial square-envelope estimate from the temporal
endpoint, an arbitrary measurable/vector-valued extension,
`verticalRecombined`, a continuum limit, a spacetime-packet estimate, a fine
square function, or local smoothing.

## 2026-08-20 17:39:18 -04:00

The finite supplied-Schwartz normal-projection overlap bridge is now
source-verified.  Its only transplant issue was declaration order: the first
placement was before the later `overlapSquareFunction` and square-function
definitions, so the source compiler could not resolve those names.  Moving
the same wrapper below the generic overlap declaration resolved the issue.

`spaceTimeFourier_temporalSchwartzAnnularNormalProjection_eq_jointAmplitude`
records the actual sheared joint profile.  The finite wrapper
`overlapSquareFunction_temporalSchwartzAnnularNormalProjections` applies the
base overlap hypothesis directly after the existing projected-model conic
support theorem.  It intentionally supplies no equality to a raw
`angularPiece` or a separable spectral packet; therefore it does not close a
fine-square, tail, `p4`, or local-smoothing gap.

## 2026-08-20 17:59:26 -04:00

The raw angular/radial compatibility gap is resolved only in its legitimate
regular supplied-data form.  `fourier_radialPiece_eq_schwartzProfile_mul_fourier`
requires an explicit Schwartz representative `R` for the radial multiplier,
and the two angular-piece theorems require the explicit Schwartz amplitude
identity for `B`.  No theorem attempts to manufacture either datum from an
arbitrary raw cutoff.

The normal-tail branch now has arbitrary rapid pointwise decay in
`tau - rho xi`, plus a cutoff-radius refinement when the supplied normal
cutoff equals one on the stated normal ball.  Both are strictly Fourier-side
pointwise estimates.  They do not supply physical-space `L²`/`L⁴` tail
control, raw compact-time plate support, a fine-square estimate, `p4`, or
local smoothing.

## 2026-08-20 18:19:32 -04:00

The regular-model L² transport gap is resolved.  The generic theorem
`eLpNorm_spaceTimeFourier_jointSchwartzRaw_two_eq` moves canonical Plancherel
through the public `WithLp.toLp` measure-preserving equivalence, and the
normal-tail specialization applies it definitionally.  This is an exact
product-coordinate identity for supplied joint-Schwartz data, not an L²
estimate for raw compact-time packets.

The fixed-packet bridge constructor
`exists_regularAngularRadialBridgeData_of_normRadialSchwartzCutoffs` likewise
has deliberately narrow scope: its scalar radial cutoff is chosen from a
single supplied norm-radial Schwartz `R`, positive scale, integer packet, and
unit direction.  It does not derive a shared cutoff family or fill any raw
`p4`/fine-square/local-smoothing hypothesis.

## 2026-08-20 19:14:40 -04:00

The new normal-tail radius estimates are deliberately restricted to the
supplied joint-Schwartz model. Their constants are uniform only after fixing
the spatial amplitude B, temporal Schwartz factor vartheta, power N, and a
global defect envelope M, then quantifying over u, beta, rho, and the
normal-ball radius R. The hypotheses require u = 1 on the support of B,
beta = 1 on the stated normal ball, and norm(1 - beta) <= M globally.

The L4 result is a squared eLpNorm estimate assembled from the L2 theorem at
twice the requested power and a separate Fourier-L1 defect envelope. It does
not produce a raw compact-time packet estimate, a plate-support statement, a
finite-family recombination, a fine square function, p4 local smoothing, or
a local-smoothing theorem.

## 2026-08-20 19:35:41 -04:00

The new angular-minus-projection estimate is only a supplied regular
one-packet transfer. It requires the explicit Schwartz radial profile and
amplitude identities, and its norm-agreement condition for rho must be
quantified with the chosen rho. It therefore does not construct regular data
from arbitrary angular or radial cutoffs.

The accompanying finite-sum theorem is only finite Minkowski: its conclusion
uses a sum of already-supplied L4 tail envelopes. It is not a square-function
estimate, a continuum reassembly theorem, a packet-family approximation, p4
local smoothing, or local smoothing.

## 2026-08-20 20:02:41 -04:00

The new finite square-function perturbation bridge closes only the finite,
supplied regular-model error step. In particular, its regular angular/radial
consumer still assumes the analytic `overlapSquareFunction` hypothesis,
explicit Schwartz profiles `R` and `B`, and an explicit finite sum of
normal-tail `L4` norms. It does not provide a uniform packet-family tail
budget, manufacture regular profiles from raw compact-time cutoffs, or
discharge `fineSquareFunctionEstimate`, `p4LocalSmoothing`, or a continuum
reassembly hypothesis. Those remain genuine separate gaps.

## 2026-08-20 20:23:02 -04:00

The raw angular/radial square-function perturbation is now available only as
the intended finite elementary estimate: componentwise `full = main + tail`
and measurable finite tails give an `L4` bound by the sum of supplied tail
envelopes. Its implementation uses a private arbitrary finite-index `PiLp`
argument, without changing the existing `Int`-indexed vertical API.

The regular consumer replaces only the projected square function on the
right-hand side of the existing overlap-plus-tail bridge by the literal raw
angular/radial square function, at the cost of the explicit `(q + 1)` tail
coefficient. It still requires the analytic `overlapSquareFunction` premise,
finite indices, and all supplied Schwartz `R`, `B`, `rho`, and support data.
It does not construct raw compact-time data, furnish a uniform family tail
budget, prove a fine-square estimate or `p4LocalSmoothing`, or take a
continuum limit.

## 2026-08-20 20:45:24 -04:00

The finite supplied regular family now has a uniform normal-radius rate in
weighted form. The positive overlap coefficient and a single finite tail
constant are chosen before all supplied spatial cutoffs, normal cutoffs,
normal shears, and the common normal radius. The internal tail constant is a
finite sum of one-packet squared-`L4` witnesses; no square-root or inverse
ENNReal estimate is hidden in the theorem.

The result remains conditional on the analytic `overlapSquareFunction`, uses
only supplied finite Schwartz profiles and explicit support identities, and
retains the raw two-index square function on its right-hand side. It does not
construct a raw cutoff model, establish a fine-square or `p4` estimate, bound
an infinite family, or perform a continuum/recombination argument.

## 2026-08-20 21:10:33 -04:00

The finite angular partition layer is now formalized at the literal raw
Fourier level. The partition is required only on the support of the spatial
Fourier multiplier, while every angularized multiplier carries an explicit
integrability hypothesis. This is necessary because raw `fourierInv` has no
unconditional finite-additivity instance.

The reconstruction theorem rewrites only the finite radial-time term as a
`verticalRecombined` family of angular pieces. It supplies no vertical
recombination estimate, angular/radial square-function bound, partition
construction, fine-square estimate, `p4LocalSmoothing`, or continuum result.
The private regular-profile helper discharges the integrability hypothesis
only from explicitly supplied Schwartz radial and angular amplitudes; it does
not infer those data from arbitrary raw cutoffs.

## 2026-08-20 21:16:34 -04:00

The angularized reconstruction is now connected to the original conic
half-wave by the exact identity `conicOperator = verticalRecombined +
radialTimeResidual`. It consumes the same finite support-local partition and
raw Fourier-integrability hypotheses as the preceding reconstruction theorem.

This is only the algebraic outer decomposition. It does not estimate the
residual, prove a vertical recombination bound, construct the angular
partition, establish a square-function/fine-square estimate,
`p4LocalSmoothing`, or make any continuum claim.

## 2026-08-20 21:31:58 -04:00

The finite supplied-Schwartz temporal core now exposes the literal raw
fourth-moment form required for a later spatial Fubini/Tonelli lift.  Its
input-independent interpolation coefficient is public and the existing
fourth-moment bound factors exactly as that coefficient times the fourth
moment of the finite `PiLp 2` input bundle.  The spatial core also has an
exact fixed-fiber identity after scaling each temporal Schwartz profile by
the corresponding spatial value.

These APIs remain finite, supplied-Schwartz statements.  They do not create
an endpoint for arbitrary measurable vector inputs, prove a space-time
Fubini lift, identify `verticalRecombined`, establish a square-function or
fine-square bound, or imply `p4LocalSmoothing`.

## 2026-08-20 21:50:09 -04:00

The finite supplied-Schwartz space-time Fubini lift is now formalized.  It
uses the temporal fourth-moment coefficient on each spatial fiber and
Tonelli to bound the literal `verticalSchwartzCoreRecombined` by the fourth
moment of the corresponding finite `verticalSquareFunction`.  A companion
gives `MemLp 4` and the resulting `eLpNorm` bound, and a rewrite-only
corollary identifies the same estimate with the literal finite
`verticalRecombined` separable-packet family.

The scope remains deliberately narrow: finite indices and supplied Schwartz
temporal/spatial profiles under the displayed profile and overlap
hypotheses.  It does not prove an endpoint for arbitrary measurable inputs,
`verticalRecombination`, a continuum limit, a square-function or
fine-square estimate, `p4LocalSmoothing`, or local smoothing.

## 2026-08-20 22:32:52 -04:00

The varying-spatial Fubini layer now also accepts a finite rank expansion
inside each original vertical label.  The original `m` profile and overlap
hypothesis remain indexed by the vertical label; the finite rank sum is
collected before applying the temporal fourth-moment theorem.  The right
hand side is consequently the vertical square function of the rank-summed
packet family, not a flattened two-index square function.

The exact supplied-Schwartz Fourier calculation additionally identifies this
finite-rank core with a literal `verticalRecombined` family.  This remains a
finite algebraic/Schwartz result: it does not establish arbitrary-input
density, a scale-normalized endpoint, `verticalRecombination`, a continuum
limit, fine-square control, `p4LocalSmoothing`, or local smoothing.

## 2026-08-21 14:54:33 -04:00

The former `verticalRecombination` predicate was not blueprint-faithful: it
took an arbitrary raw cutoff and quantified arbitrary functions
`Int → WaveSpaceTime → Complex`, without the smooth compact-support or
measurability/integrability data needed by the physical convolution,
Plancherel, and interpolation proof.  It has been corrected to use
`MSSVerticalCutoff`, which records a Schwartz cutoff with
`tsupport ⊆ Ioo (-1) 1` and the pointwise support condition used in spectral
overlap, and to quantify finite joint-Schwartz families through
`jointSchwartzRaw`.  The proved public theorem is
`verticalRecombination_of_MSSVerticalCutoff`; it is intentionally not an
arbitrary measurable-input or continuum-extension assertion.

## 2026-08-21 17:29:49 -04:00

The earlier positional wave-front-localization predicate lacked the
scale-indexed cutoff geometry, raw Schwartz realization, and polynomial
spatial-profile regularity from which its two literal conclusions must be
derived.  In particular, supplying a rapid residual or output estimate there
would have restated the desired normal-tail conclusion rather than proved it.
The active blueprint item is now expressed through
`MSSWavefrontCutoffData`, `MSSWavefrontKernelData`,
`MSSWavefrontRawProfileRealization`, and
`MSSWavefrontSpatialProfilePolynomialRegularity`; the proved theorem
`wavefrontLocalization_of_MSSWavefrontKernelData` establishes the exact raw
`L⁴` square-function error and active conic-plate Fourier support.  Its
normal-tail multiplier bound is derived privately from the stated cutoff and
profile data, not assumed as residual, kernel, or output data.

## 2026-08-21 17:40:37 -04:00

The fixed-separation plate-overlap theorem is already proved as
`plateOverlap_of_angularSectorGeometry`: its `angularSectorGeometry`
hypothesis is the Lean-level form of the blueprint's ordered, uniformly
spaced angular partition, and it yields the stated thick-plate multiplicity
bound with exponent `2 * gamma`. The newly introduced wave-front cutoff data
records localization supports and cardinality, but deliberately does not
imply this stronger spacing/order geometry. Consequently a later composition
must supply an explicit angular-geometry bridge; wave-front localization
alone must not be treated as a plate-overlap hypothesis.

## 2026-08-21 18:58:10 -04:00

The former overlap-square-function predicate quantified arbitrary raw
space-time functions and required a constant uniform in `gamma` after
choosing `eta`.  That has the wrong quantifier order for the blueprint:
plate-overlap loss depends on `gamma`, which must be chosen sufficiently
small after `eta`.  It also lacked the finite separation-level coverage and
logarithmic bound needed to partition all angular pairs exactly.

The proved statement `overlapSquareFunction_of_levelData` therefore uses
finite joint-Schwartz spectral packets, chooses `gamma` after `eta`, and
requires the explicit `angularSeparationLevelData` that supplies the pair
partition and logarithmic level count.  The older raw formulation is retained
only as the explicitly named conditional
`overlapSquareFunctionRawHypothesis` for pre-existing regular-model transfer
lemmas; it is not claimed as this proved blueprint proposition.

## 2026-08-21 19:52:22 -04:00

The former `removeVerticalProjections` predicate quantified an arbitrary raw
vertical cutoff and arbitrary raw space-time packets.  The literal
`verticalProjection` is defined through iterated Fourier integrals, so that
formulation had no justified common-kernel realization on all `L⁴` inputs.

The proved `removeVerticalProjections_of_schwartz` now has the blueprint's
supplied-Schwartz packet model: `beta : SchwartzMap Real Complex` and a finite
joint-Schwartz family, evaluated through `jointSchwartzRaw`.  Its proof uses
the exact affine inverse-Fourier temporal kernel, finite `PiLp 2` Minkowski,
and time-only `L⁴` Young.  The constant is
`1 + ∫ y, ‖fourierInv beta y‖`, independent of the radial and angular packet
counts.  Extending the raw Fourier definition to arbitrary measurable `L⁴`
families would require a separately proved operator extension and agreement
theorem; it is not asserted here.

## 2026-08-22 15:01:36 -04:00

The existing scaled-ray localization results do not instantiate the literal
MSS fine-cube kernel. They concern `angularDyadicCubeSpaceTimeKernel` with a
dyadic-bandpass factor and require a cube centered exactly at
`scale • direction`, together with explicit uniform high-order residual
seminorm (or derivative-integral) bounds. In contrast,
`mssFineCubeHalfWaveKernel` uses
`cube.cutoff * D.spatialProfile * halfWaveMultiplier`; its cubes are only
known to lie within `O(sqrt scale)` of the packet ray, and no theorem equates
that literal symbol with the angular-dyadic one. The decomposition's cutoff
derivative bounds also do not control derivatives of the product with the
scale-indexed spatial profile.

This is a genuine mathematical gap, not only an API gap: the current
wavefront data impose no scale-uniform derivative/size budget on the angular
cutoffs beyond support, so their spatial profiles and literal fine kernels
can be rescaled with the MSS scale while preserving the structural fields.
Thus a scale-independent `kernelConstant` or `massConstant` cannot follow
from `MSSWavefrontKernelData` and `MSSCubeDecomposition` alone.

A valid next bridge must supply an exact literal-kernel/source representation,
ray-centered cutoff geometry (or a controlled enlargement), and uniform
high/zero residual bounds with a scale-independent coefficient. Once such
domination is available at decay order `N > 2`, source integrability and a
mass bound follow from the existing light-ray-kernel mass theorem.  A later
audit established that the literal source representation and individual
source integrability themselves are automatic from the current compact
annular data; the remaining nonautomatic localization clauses are precisely
uniform ray domination and its uniform source mass.

## 2026-08-22 15:23:00 -04:00

The available analysis-cube regularity does not prove the missing averaged
Rademacher `L4` estimate.  It supplies support, square overlap, and normalized
derivative `L1` bounds, whereas the existing Mikhlin API needs uniform
pointwise weighted derivative bounds.  For fine cubes of width
`sqrt scale` at frequency `scale`, the ordinary first Mikhlin quantity is
typically of size `sqrt scale`, so that route is not scale-uniform.  Existing
Littlewood--Paley/Rademacher results are restricted to the repository's
integer-dyadic cutoff family and provide no bridge to arbitrary translated
fine cubes.

Accordingly the next analytic input must be a genuine finite smooth
Rubio/random-sign `L4` theorem (or precisely the existing
`HasScaleAverageMSSAnalysisCubeRademacherL4` hypothesis).  It must be an
averaged result: the deterministic-sign substitute is already known to be
false.  No current structural cube regularity field supplies this theorem.

## 2026-08-22 15:23:00 -04:00

The literal HLE duality closure uses tests supported on
`lightRayTimeInterval`.  General `MSSRadialTimeCutoffs` records only compact
support for the physical time cutoff, not support in that fixed slab.  The
new source-compiled closure therefore takes the honest additional condition
`D.HasLightRayTimeSlabSupport`.  Removing it from the final MSS route will
require a proved finite temporal partition/translation reduction from an
arbitrary compact time cutoff to the fixed HLE slab; such a reduction is not
currently present and must not be silently inferred from compactness.

## 2026-08-23 21:35:07 -04:00

The current structured target `mssFineSquareFunctionEstimate` is still too
weakly specified to be a true unconditional proposition.  In particular,
`MSSFineAngularData` gives only sector support, a complex-valued partition,
and `‖chi‖ ≤ 1`; it supplies no uniform rescaled derivative or fixed-template
control.  At a sequence of scales one can insert arbitrarily rapid smooth
chirps into two overlapping angular cutoffs, keeping their sum equal to one
and each norm at most one.  The resulting `spatialProfile` remains Schwartz
at each individual scale and all present cube-geometry fields remain valid,
but the corresponding packet multiplier has an unbounded `L4` norm relative
to every fixed subpower scale loss.

This differs from the blueprint's fixed smooth cube partition and its
uniformly rescaled packet amplitudes.  A genuine final theorem therefore
needs those quantitative cutoff/profile assumptions (and a structured
equal-cube Rubio input), not merely the current support and zero-order
fields.  The existing conditional localization and averaged-cube hypotheses
remain honest until that interface and analytic proof are supplied.

## 2026-08-23 22:00:54 -04:00

The structured fine-square target was moved to `MSS.lean` and corrected to
take two necessary structural hypotheses: the scale-uniform natural-packet
`L1` derivative bounds in `MSSFineSpatialProfileUniformRegularity`, and
`D.HasLightRayTimeSlabSupport`.  The former prevents the scale-dependent
angular chirps identified above and implies the existing polynomial profile
regularity interface; the latter is exactly the fixed time-slab premise used
by the existing light-ray-maximal closure.  Neither is a disguised
square-function or kernel-localization conclusion.

This makes the proposition's statement honest, but it remains `ToDo`.
What is still required is a proved smooth equal-cube/Rubio `L4` input and
literal fine-kernel light-ray domination (or a fully formalized replacement);
arbitrary `MSSCubeDecomposition` data alone establish neither one.

## 2026-08-23 22:06:28 -04:00

`Status.md` previously marked `thm:fourier-cube-square-function` as proved,
but the cited declaration `fourierCubeSquareFunction` is only a definition.
The current unconditional API proves the corresponding `L2` estimate from
square overlap; the `L4` routes are explicitly conditional on all-sign or
averaged Rademacher hypotheses.  In particular, the existing Mikhlin and
integer-dyadic Littlewood--Paley results do not establish the translated
natural-scale equal-cube estimate needed by MSS.  The status entry has been
corrected to `ToDo` so the remaining analytic input is not obscured.

## 2026-08-23 22:20:14 -04:00

The literal fine-kernel route is now reduced to one honest analytic premise.
`MSS.lean` proves that every actual fine-cube multiplier is compact smooth,
that its packet has the displayed source-kernel representation, and that a
literal light-ray pointwise bound automatically supplies all fields of
`MSSFineCubeKernelLocalization`, including source mass.  It also proves the
exact residual-symbol translation and derives that light-ray pointwise bound
from uniform order-zero and order-`N` inverse-Fourier residual seminorms.

The latter seminorm bounds have not been proved from the present data.  Their
proof needs generic natural-scale product/Leibniz and residual-phase estimates
for the actual `cube.cutoff * spatialProfile` symbol.  Thus the new bridge is
not a replacement for nonstationary phase; it precisely identifies the
remaining argument.  The updated `MSS` source and the full
`LeanSpherical.Codex.Spherical.MSS` module build both compile without
`sorry`, `admit`, or added axioms.

## 2026-08-23 22:29:39 -04:00

The first residual-decay bridge was too strong at one point: it requested
inverse-Fourier residual seminorms for every space--time point.  That cannot
be derived from the literal residual symbol, because differentiating its
plane-wave phase grows with unbounded physical time, while the outer physical
time cutoff only makes the *actual kernel* vanish outside its support.

The source-compiled bridge now requests residual seminorm or derivative-
integral bounds only for `z.2 ∈ lightRayTimeInterval`, under the explicit
`HasLightRayTimeSlabSupport` hypothesis.  It splits the conclusion into the
slab case, where Fourier integration by parts applies, and the complementary
case, where the outer time factor is exactly zero.  A nonnegative residual
constant is now explicit because it is needed to compare that zero value with
the nonnegative light-ray envelope.  This corrects the scope of the remaining
phase/product estimate; it does not prove that estimate or the separate
smooth equal-cube `L4` input.

## 2026-08-23 22:51:07 -04:00

The original Fourier-integration-by-parts residual wrapper was mathematically
valid but not natural-scale: its right side used an unweighted sum of all
frequency derivatives.  Natural packet estimates give the order-`j` integral
at size `R^(2-j)` for the cube radius `R`, so the unweighted sum is dominated
by its zeroth-order `R^2` term and cannot yield the desired order-`N`
physical decay.

`MSS.lean` now proves `fourierInv_seminorm_le_scaled_derivativeIntegrals`,
which first rescales frequency by `R` and gives
`2^N * R^(-N) * sum_{j <= N} R^j * integral ||D^j q||`.  Its new literal
residual wrapper consumes exactly the corresponding weighted bound
`2^N * sum R^j * integral ||D^j q|| <= A * R^2`, on the fixed time slab,
and derives the light-ray kernel estimate.  This corrects the scale of the
endpoint.  It still leaves the genuinely analytic product/phase derivative
bound and the independent smooth equal-cube `L4` theorem to prove.

## 2026-08-23 23:04:01 -04:00

The blueprint's Fourier-cube theorem is specifically a fixed smooth lattice
partition, whereas `MSSAnalysisCubeRegularity` currently records only support
in equal-size coordinate cubes, a pointwise square-overlap bound, and scaled
`L1` derivative integrals.  Those fields do not encode lattice indexing,
geometric finite overlap, a nondegenerate core, or a common translated/dilated
prototype.  For example, arbitrarily many scaled copies of one bump at the
same center satisfy the present square-overlap and derivative requirements
after reducing their amplitudes; therefore the usual finite-colouring and
fixed-prototype Rubio argument cannot even be stated from this record.

This is not a counterexample to every conceivable abstract `L4` conclusion,
but it is a genuine interface discrepancy: deriving such a conclusion from
the present fields would require a new generalized vector-valued Rubio theorem.
The appropriate repair is a fixed-lattice/prototype atlas (or an equivalent
disjoint-core, bounded-enlargement, uniform-symbol formulation), followed by
an actual proof of the smooth equal-cube Rubio estimate.  Mathlib and this
repository currently contain neither that theorem nor the BMO/vector-valued
Calderon--Zygmund infrastructure of its standard proof.  The status of
`thm:fourier-cube-square-function` must therefore remain `ToDo`.

## 2026-08-24 02:22:05 -04:00

The exact fixed-lattice part of the Fourier-cube argument is now
source-proved in `MSS.lean`.  The public theorem
`latticeFourierCubeSquareFunction_lintegral_four` gives the uniform fourth
moment estimate for every finite selected family of translated/dilated copies
of one Schwartz prototype on the common `R Z^2` lattice.  The accompanying
`MSSAnalysisCubeLatticeData` interface and
`uniformScaleMSSAnalysisCubeSquareFunctionL4_of_lattice` theorem transfer
that estimate to an MSS analysis-cube family when its cutoffs are exactly that
lattice model.

This does not remove the discrepancy recorded above: no current constructor
derives `MSSAnalysisCubeLatticeData` from `MSSCubeDecomposition` and
`MSSAnalysisCubeRegularity`.  Completing the blueprint item still requires a
canonical finite smooth lattice partition of the active annulus (or a proved
generalized equal-cube Rubio theorem for the weaker abstract record).  The
ledger therefore remains `ToDo`, but no longer describes the fixed-lattice
case as merely conditional.

## 2026-08-24 02:47:09 -04:00

The first missing construction layer is now source-verified in `MSS.lean`:
`mssUnitLatticeTransitionPiece(t) = smoothTransition(t + 1) -
smoothTransition(t)` supplies a compact smooth one-dimensional integer
partition, and its tensor product supplies a planar synthesis prototype.
The file proves its coordinate-cube support, compact Schwartz realization,
finite product-indexed lattice partition identity, and unit square-overlap.
A radius-three `ContDiffBump` gives a fixed Schwartz analysis prototype which
equals one on the synthesis support, so the exact cutoff absorption identity
is also proved.

This is only the common fixed-prototype layer.  It does not yet construct the
scale-dependent finite global grid, per-packet cube sets, bounded packet
fibers, reverse overlap, ray alignment, or derivative fields required by
`MSSCubeDecomposition`; the Fourier-cube blueprint row must remain `ToDo`.

## 2026-08-24 02:59:52 -04:00

The spatial geometric prerequisite for the canonical cube construction is now
source-proved.  `mss_spatialProfile_center_ne_packet_ray` shows directly from
the literal `spatialProfile` formula, annular amplitude support, radial
window, angular-sector support, and unit direction that every nonzero packet
frequency lies within
`(2 * angularConstant + 11 / 4) * sqrt scale` of its radial--angular ray
center.  This removes the previously missing support-to-ray-ball step.

The remaining construction is genuinely combinatorial/geometric: choose a
finite global lattice at each scale, select the bounded local cube set for
each packet, and prove its uniform reverse-overlap bound from the separated
angular geometry.  No such `MSSCubeDecomposition` constructor has yet been
verified, so the ledger remains `ToDo`.

## 2026-08-24 03:19:04 -04:00

The finite combinatorial grid layer is now source-verified in `MSS.lean`.
The construction enumerates `[-M,M]^2` by an injective finite label map,
proves the coordinatewise inverse for every bounded integer label, and embeds
each packet's fixed local offset grid around
`floor (n * direction)` injectively into the scale-dependent global grid.
The embedding uses the proved radial-index and unit-direction bounds, so its
target is genuinely finite at every active scale.

This is meaningful progress toward the required canonical cube family, but
it is not yet an `MSSCubeDecomposition`: the finite-grid sum still needs to
be reindexed into the synthesis identity, and the record's global overlap,
derivative, ray-alignment, and reverse-incidence fields must be proved. In
particular, the uniform reverse-incidence proof must use separated angular
geometry, rather than the weaker cardinality data in `MSSWavefrontKernelData`
alone. The Fourier-cube row therefore remains `ToDo`.

## 2026-08-24 03:48:30 -04:00

The canonical finite lattice construction is now almost completely
source-verified in `MSS.lean`. Its cube cutoffs have unit global square
overlap, exact synthesis/analysis absorption, all-order normalized derivative
bounds, and exact packet reconstruction via the embedded local lattice grid.
The selected cube sets have uniformly bounded cardinality, and every selected
center lies within
`2 * (localLatticeRadius + 1) * sqrt scale` of its packet ray. The enlarged
analysis family is also proved to be the exact one-prototype lattice model
needed by `uniformScaleMSSAnalysisCubeSquareFunctionL4_of_lattice`.

All `MSSCubeDecomposition` fields except reverse incidence now assemble in
the verified constructor
`mssCanonicalCubeDecomposition_of_reverseOverlap`; its explicit premise is
precisely the remaining uniform reverse-overlap count. This premise cannot
follow from `MSSWavefrontKernelData` alone, since that interface has only an
angular cardinality bound. It must be derived from the separated geometry in
`MSSFineAngularData`. The ledger remains `ToDo` until that final geometric
count is source-proved.

## 2026-08-24 04:18:42 -04:00

The final reverse-incidence condition has now been source-proved from
`MSSFineAngularData`.  For two packets sharing a canonical lattice cube,
their normalized ray points are uniformly close.  At scales with
`sqrt scale >= 12`, radial relevance makes both labels positive and comparable
to `sqrt scale`; radial distance and the separated angular geometry then put
both labels in a fixed integer box.  At the bounded remaining scales, direct
radial relevance and the sector-radius label bound give the same conclusion.
Injecting each fixed-cube fiber into that box proves a scale-independent
reverse-overlap constant.

Consequently `mssCanonicalCubeDecomposition` is now a complete finite
`MSSCubeDecomposition`, its enlarged cutoffs have
`mssCanonicalCubeAnalysisLatticeData`, and
`mssCanonicalCube_uniformAnalysisL4` applies the proved fixed-lattice
fourth-moment theorem.  This resolves the canonical-lattice interface gap in
the Fourier-cube blueprint item.  It does not by itself prove the separate
literal fine-kernel residual product/phase estimate needed for the subsequent
fine-square-function proposition.

## 2026-08-24 05:25:06 -04:00

The remaining fine-square-function assembly is now source-proved in
`MSS.lean`.  The canonical cubes satisfy the literal residual-phase kernel
localization, their enlarged analysis cutoffs satisfy the direct lattice
fourth-moment estimate, and the light-ray maximal estimate supplies the
continuum fourth-moment bound.  The final conversion rewrites the literal
packet fourth moment into the `eLpNorm` formulation and absorbs the
three-halves logarithmic factor into an arbitrary scale power.  The new
theorem `mssFineSquareFunctionEstimate_of_canonicalData` has been compiled as
source and module output and audited to use only `propext`,
`Classical.choice`, and `Quot.sound`.

## 2026-08-24 05:27:10 -04:00

The legacy `recombination` predicate in `MSSBase.lean` is not a valid
unconditional formulation of blueprint Proposition `prop:mss-recombination`.
It quantifies arbitrary radial-index, angular-index, and angular-cutoff
families but assumes no radial--angular reconstruction relation. In
particular, choosing the radial index family to be empty makes its fine
square function identically zero while leaving a nonzero conic operator on
the left; the asserted arbitrarily rapidly decaying error cannot then hold
at large scales. The predicate must be replaced or bridged by a structured
recombination theorem whose data include the actual radial-time localization,
vertical cutoff, angular partition, and finite reconstruction identities.

This is a defect in the current formal interface, not in the MSS argument.
The mathematical recombination proof remains the standard sequence of
radial-time localization, vertical recombination, wave-front localization,
plate-overlap square-function control, removal of vertical projections, and
the now-proved fine square-function estimate.

## 2026-08-24 06:40:01 -04:00

The corrected structured interface is now proved by
`Codex.Spherical.MSS.mssRecombination_of_structuredData`.  It proves
`mssRecombination` from the fixed cutoff core, the scale-indexed angular
partition, the admissible gamma-family of wave-front realizations, and the
declared uniform/slab data.  The proof uses the exact angularized
radial-time reconstruction, the outer vertical `1/8` estimate, the
wave-front/plate-overlap auxiliary estimate at decay order `N + 1`, and the
literal radial-time residual at order `N`; the extra inverse scale power
absorbs the outer vertical loss.

The theorem was source-compiled and module-built, and its axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.  It deliberately does
not claim the legacy unstructured `recombination` predicate from the prior
entry, which remains false for the stated reason.  This resolves blueprint
`prop:mss-recombination` through the repaired, mathematically faithful
interface; the separate `thm:mss-p4` statement remains unfinished.

## 2026-08-24 13:41:49 -04:00

`Codex.Spherical.MSS.p4LocalSmoothing_of_lpCutoffs` is now source-compiled
and module-built.  For every `C : lpCutoffs 2`, it proves the existing target
predicate `p4LocalSmoothing C.cutoff`: the positive half-wave is reconstructed
from the finite coarse conic atlas, and the negative half-wave is transported
by reflected-conjugate Fourier symmetry.  Its declaration-level axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

This supersedes the final sentence of the preceding checkpoint: blueprint
`thm:mss-p4` is complete.  This checkpoint does not promote the separately
listed all-exponent local-smoothing, discretization, Bourgain, or diagonal
theorems; those labels require their own verified downstream declarations.

## 2026-08-24 13:48:00 -04:00

The verified endpoint now has the public all-exponent consumer
`Codex.Spherical.MSS.localSmoothing_of_lpCutoffs`.  For every
`C : lpCutoffs 2`, `2 < p`, and `0 < eta`, it applies the existing proved
endpoint interpolation theorem to `p4LocalSmoothing_of_lpCutoffs C` and
concludes `localSmoothing C.cutoff p eta`.

The new declaration source-compiles, the top-level
`LeanSpherical.Theorems` build succeeds through the Bourgain and diagonal
imports, and its axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.  This supersedes the immediately preceding caution for the
all-exponent row: blueprint `thm:mss-local-smoothing` is complete.  No claim
about the separately formulated discrete theorem is made here.

## 2026-08-24 13:57:41 -04:00

The remaining continuous chain is now closed unconditionally.  The new
`Codex.Spherical.Bourgain.bourgainCircularMaximal` chooses a dimension-two
`lpCutoffs` witness from `exists_lpCutoffs` and applies
`p4LocalSmoothing_of_lpCutoffs`; it proves the circular maximal
Schwartz-core bound for every finite exponent greater than two.  The new
`Codex.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_sphericalMaximal_le_of_mss`
uses that closure to supply the all-radii diagonal estimate for every
dimension at least two, and the public facade
`Spherical.eLpNorm_sphericalMaximal_le_of_mss` exposes it without changing
the pre-existing dimension-at-least-three theorem.

Direct source compiles of `Bourgain.lean`, `DiagonalTheorem.lean`, and
`Theorems.lean`, followed by the `LeanSpherical.Theorems` module build, all
pass.  Declaration-level audits of the Bourgain, diagonal, and public facade
theorems report only `propext`, `Classical.choice`, and `Quot.sound`.  This
resolves `thm:intro-bourgain`, `cor:bourgain-final`, and the final requested
integration.  The separately formulated sampled-time
`cor:mss-discrete` remains a distinct open transaction.

## 2026-08-24 16:00:45 -04:00

The user updated the remaining public wrappers in `LeanSpherical/Theorems.lean`
from `3 ≤ d` to `2 ≤ d`. The all-radii wrapper is now genuinely supported:
`DiagonalTheorem.eLpNorm_sphericalMaximal_le` has a planar branch using the
proved unconditional Bourgain/MSS theorem and retains the prior `d ≥ 3`
branch.

The other three updated wrappers are not consequences of that result and
must not be weakened by an unproved Codex adapter. The planar restricted
strong theorem requires the global `1 < p < 2` fractal-radius estimate; the
existing finite physical-CZ/selector route explicitly requires codimension
at least two (ambient `d ≥ 3`). The lacunary theorem has the same missing
planar moving-band `L²` selector core for `1 < p ≤ 2`. Finally,
`PowerWeightTheorem.closure_typeSet_eq` is the full weighted Theorem 1.1,
whose negative-weight subquadratic branch depends on those missing planar
global estimates, not merely on Bourgain's unweighted full-radius `p > 2`
bound.

Direct compilation of the updated facade therefore passes the all-radii
line but still fails exactly at the restricted, lacunary, and power-weight
wrappers. Completing the requested `d ≥ 2` façade requires a separate
formalization of those planar global/weighted results.
