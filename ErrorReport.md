# Bourgain circular maximal formalization — error report

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
