# BRS formalization instructions

Mathematical reference: David Beltran, Joris Roos, Andreas Seeger,
*Spherical maximal operators with fractal sets of dilations on radial
functions*, [arXiv:2412.09390](https://arxiv.org/abs/2412.09390),
Studia Mathematica **289** (2026), 1--32.  Cited below as BRS.

## Goal

Formalize, `sorry`-free and depending only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), **every main result stated in
the introduction of BRS**:

- Theorem 1.1 (i)--(iii): the radial type set for `d ≥ 3`;
- Theorem 1.2: the radial type set for `d = 2`, in terms of `ν♯`;
- Corollary 1.3 (i)--(ii): the quadrangle consequence of Theorem 1.2;
- Theorem 1.4 (i)--(v): the `d = 2` endpoint results.

Each Lean statement must be true to the original mathematical meaning.

## File layout (hard constraints)

All BRS work goes into the single file

- `LeanSpherical/Auto/Spherical/FractalDilations/BRSRadial.lean`

inside the `Auto` namespace.  Do not create any other new file.

Existing files may be adapted *slightly* — to export a private lemma, to
generalize a hypothesis, to add an import — but every such change must leave
the whole project building.  Run `lake build` (not just the single module)
before recording any advance.

`LeanSpherical.lean` imports `BRSRadial.lean`, so `lake build` covers it.

## Reuse before reinventing

Much of the required groundwork already exists in this repository.  Search
for it before writing anything.  In particular:

- radial functions: `Auto.RadialFourierTransform.IsNormRadial`,
  `IsOrthogonallyInvariant`, and the polar-coordinate integration lemmas
  (`lintegral_polar_unitSurfaceMeasure`, `integral_polar_unitSurfaceMeasure`,
  `volumeIoiPow`) used throughout `BRRS.lean` and `SurfaceMeasureDecay.lean`;
- the radial profile correspondence `brrsRadialProfileMeasure`,
  `brrsRadialProfileLift`, `eLpNorm_brrsRadialProfileLift_eq`,
  `memLp_brrsRadialProfileLift_iff` in `BRRS.lean`, which is the
  `L^p(ℝ^d)` ↔ `L^p(r^{d-1} dr)` isometry BRS uses constantly;
- the spherical maximal operator `Spherical.M`, `Spherical.sphericalAverage`,
  `Spherical.unitSphereMeasure` from `LeanSpherical/Definitions.lean`, and the
  strong-type/type-set vocabulary in
  `Auto.Spherical.FractalDilations.Auxiliary`;
- covering numbers and dimensions: `Auto.FractalDimensions`
  (`upperMinkowskiDimension`, `upperAssouadSpectrum`, `quasiAssouadDimension`,
  `IsQuasiAssouadRegular`) and `Auto.Spherical.LegendreAssouad`
  (`brrsEntropyNumber`, `logBall`, `upperMinkowskiExponent`,
  `brrsLegendreAssouadFunction`).  **BRS (1.2) `ν♯` is the same quantity as
  BRRS (1.4)**; reuse `brrsLegendreAssouadFunction` and the facts already
  proved about it rather than redefining it;
- the Stein/Bourgain/Seeger--Wainger--Wright results in
  `Auto.Spherical.SphericalMaximal` and
  `Auto.Spherical.FractalDilations.AHRSUpperBounds`, including the sharpness
  machinery `stein_eLpNorm_sphericalMaximal_eq_top_of_one_on_closedBall`.

Reuse only where the hypotheses and conclusions genuinely match.  Never
present a weaker existing estimate as a BRS result.

## Required workflow

The first step for each main result is **not** to write Lean.  It is to read
the actual BRS proof of that result and reorder it into strict forward
reasoning: a topological order of the dependency DAG in which every statement
appears only after all statements its proof actually uses.  Record that order
in `automation/Status-BRS.md` (see below) before formalizing anything in it.

Then, at any time, select the first row of the ledger which is not complete
and whose prerequisites are all complete.  Formalize exactly that item, keep
it faithful to BRS, compile, update its ledger row, and only then start the
next.  Do not accumulate unrelated auxiliary lemmas, and do not work on two
incomplete items of the same result at once.  Independent main results may be
advanced in either order, but never simultaneously.

Treat the proof as a DAG, not as a numbered reading list.  Source labels
identify statements; they never determine which statement comes next.

## Source-faithfulness rule

A row may be marked `complete` only when the Lean statement is
mathematically equivalent to the BRS statement.  A weaker hypothesis or
conclusion, an unproved bridge, a conditional wrapper, an altered operator,
or a claim whose proof does not establish the source statement is **not**
completion; such a row stays `not started` or `in progress`.

Harmless convention-level differences (empty-set conventions, closed versus
open covering normalizations, an expression evaluated outside its stated
domain) are acceptable inside a `complete` row.  A genuine typographical
error in BRS may be repaired, but the repair must preserve the intended
mathematical meaning; it may never silently strengthen, weaken, or substitute
the paper's claim.  Note any such repair in the commit message, not in the
ledger.

On every resumption, re-audit the rows on the active dependency path against
the paper and the actual Lean declarations.

## Ledger format (`automation/Status-BRS.md`)

The ledger is structured into one section per main result, and the sections
appear in the order in which the results are to be proved.  Within a section,
the rows appear in strict forward reasoning order: a row may depend only on
rows above it (in its own section or an earlier one).

Every important step of the reasoning is **exactly one line**, of the form

```
<status> | <paper location> <short name> | <ISO 8601 Eastern timestamp>
```

with `<status>` one of `not started`, `in progress`, `complete`.  Prefer the
paper's own label (`Lemma 3.5`, `(1.3)`, `P₃,β^rad`); invent a short label
only where the paper has none.  The timestamp records when that line's status
last changed.

**No explanations, no evidence column, no narrative.**  One line, three
fields.  Nothing else belongs in this file except the section headers and a
single line recording the last full-project build check.

Update a line's status and timestamp immediately when it changes, before
starting the next item.

## Proof standards

- No `sorry`, no `admit`, no new axioms, no wrapper assuming its own claim.
- Preserve existing main results and namespace conventions.
- `lake build` must succeed for the whole project after each advance.
- `#print axioms` on each finished main result must show only `propext`,
  `Classical.choice`, `Quot.sound`.

## Done

Done means: Theorem 1.1, Theorem 1.2, Corollary 1.3 and Theorem 1.4 are all
fully proved in `BRSRadial.lean`, the project builds, and the axiom check
above passes for each of them.

## Current handoff

Section 0 and all of §3 (the necessary conditions) are complete: Lemma 3.1,
Lemma 3.2(i)(ii), the packing/covering bridge, the dimensional condition, the
half-plane description of `Delta`, the endpoint exclusions, Corollary 3.3
(`radialTypeSet_subset_Delta`), and Lemma 3.4
(`le_eLpNorm_ratio_stein`, with `steinBump`, `le_brsKernel`,
`le_integral_stein_weight`, `le_norm_sphericalAverage_steinFun`).

In §4 the following are complete: the (4.3) definitions (`brsProfileSub`,
`brsMainMaximal`, `brsRemainderOne`, `brsRemainderTwo`), the three kernel
bounds (`brsKernel_le_main'`, `brsKernel_le_small`, `brsKernel_le_large`), the
per-range average estimates (`le_brsMainMaximal_of_mem`,
`le_brsRemainderOne_of_le`, `le_brsRemainderTwo_of_le`), Lemma 4.1 itself
(`le_brsDecomposition`), and for `R₁` the elementary window bound
(`brsRemainderOne_le_window`: `R₁ f₀ r ≤ ∫_{r/2}^{3r/2} |f₀|`, together with
`brsRemainderOne_eq_zero_of_lt` for `r < 2`).

Conventions worth keeping: ambient dimension is `d + 1` with `hd : 2 ≤ d`, and
all real exponents are written with the cast `((d + 1 : ℕ) : ℝ)` so that they
match `brsMainMaximal (d + 1)` syntactically — do not rewrite them to
`(d : ℝ) + 1`.  Lemma 4.1 is stated for `absProfile f₀` (the modulus of the
profile), because BRS's (4.3) puts the absolute value outside the integral;
`‖f₀‖_p` is unchanged by this, so the propositions apply verbatim.

Proposition 4.2 is complete (`prop42_brsRemainderOne`), as are (4.5)
(`brsRemainderTwo_le_local`) and Proposition 4.3 in the non-endpoint range
`q < pd` (`prop43_brsRemainderTwo`).

Reusable one-dimensional tools now in the file:

- `profileLpNorm d p h = (∫⁻ s, ofReal s ^ (d-1) * h s ^ p)^{1/p}`, an integral
  over all of `ℝ` — the weight kills `s ≤ 0`, so window integrals extend to it
  by `setLIntegral_le_lintegral` with no null-set bookkeeping;
- `lintegral_le_rpow_mul_measure_univ`: Hölder against the constant function,
  `∫⁻ Φ ≤ (∫⁻ Φ^p)^{1/p} (μ univ)^{1-1/p}` (`p = 1` handled separately, since
  `Real.HolderConjugate` needs `1 < p`);
- `lintegral_window_swap`: `∫⁻ r (∫⁻ s in [r-2,r+2], Ψ) = ofReal 4 * ∫⁻ Ψ`, via
  translation (`lintegral_add_right_eq_self`) plus `lintegral_lintegral_swap` —
  translating to the fixed window `[-2,2]` avoids all joint-measurability work
  on the region `{(r,s) : |s-r| ≤ 2}`;
- `lintegral_rpow_Ioc_lt_top`, `enorm_brsProfileSub_rpow`, `pow_sub_eq_rpow`.

**Scope note for Theorem 1.1.**  The paper's main claim is
`closure 𝒯^rad_E = Δ_β`, so the *interior* of `Δ_β` suffices for the inclusion
`⊇` — every `L^p → L^q` bound may be taken with strict inequalities, where the
radial integrals converge and no interpolation is needed.  The endpoint cases
(here `q = pd` for `R₂`; later the `p_d` endpoint for `𝔐_p`) are needed only
for the refinements (i)-(iii).  Mathlib has no Marcinkiewicz interpolation, so
those endpoints will need the layer-cake formula
(`Mathlib/MeasureTheory/Integral/Layercake.lean`) and the standard splitting;
defer them until the interior statement is assembled.

Proposition 4.4 is complete (`prop44_brsMainMaximal`, with the pointwise bound
`brsMainMaximal_le_of_lt` and the support lemmas
`brsMainMaximal_eq_zero_of_le/_ge`).  Its shape: `𝔐_p g` is supported in
`(2/3, 4)` because `t ∈ E ⊆ [1,2]` and `r/2 < t < 3r/2`, and on that range
Hölder against the kernel weight `s^{(d-1)/p'-1}` works because
`p > p_d = d/(d-1)` is exactly the condition `p' < d` making
`s^{d-1-p'}` integrable at the origin (`lintegral_kernel_weight_lt_top`,
`conjExponent_lt_of_lt`, `kernel_weight_rpow`).

One more reusable tool: `ofReal_norm_intervalIntegral_le_lintegral` dominates
`ofReal ‖∫ s in a..b, F s‖` by any `ℝ≥0∞` majorant of the integrand with **no
integrability hypothesis** — if `F` is not interval integrable the Bochner
integral is `0` by convention (`intervalIntegral.integral_undef`).  Use it
whenever the integrand has an `s^e` factor with `e < 0`, where continuity at
`s = 0` fails and integrability side conditions would otherwise proliferate.

Proposition 4.5 is complete: `prop45_brsMainMaximal`.  Its hypotheses are
worth reading before reusing it:

- `hae : (((d:ℝ)-1)*(1-1/p)-1) + 1 - 1/p = a` and `ha : a < 0` — the second is
  exactly `p < p_d`, and `a = d - 1 - d/p`;
- `hcov : ∀ n, (N(E, 2^{-n}) : ℝ≥0∞) ≤ ofReal (S^q * (2^{-n})^{-(q*a+1)})` — the
  dyadic form of the paper's supremum (the supremum implies it, so this is the
  weaker hypothesis);
- `hEnull : volume (closure E) = 0` — from `dim_M E < 1`, needed because the
  shells only cover `U_0` up to the closure of `E`;
- `hEne : E.Nonempty` — without it `volume_brsU_le` fails.

The chain, for reference: `lintegral_le_tsum_brsD` → `lintegral_brsD_le_shell`
→ `tsum_shell_block_le` → `tsum_rpow_le_tsum_rpow` +
`tsum_brsBlockNorm_rpow_le`, then the `q`-th root.  `shell_factor_identity` is
where the powers of `2` cancel, and `blockSumConst_eq` converts the `ℝ≥0∞`
block-sum constant back to an `ofReal`.

The active row is Proposition 4.6, the endpoint `p = p_d`.  Fetched proof
structure (§4 of the paper), with `B := sup_{δ<1/2} δ^{1/q} N(E,δ)^{1/q}
(log 1/δ)^{1/d}`:

1. `|U_n| ≲ B^q n^{-q/d}`, hence `|Ω_ℓ| ≲ B^q 2^{-ℓq/d}` for the grouped shells
   `Ω_ℓ = ⋃_{2^{ℓ-1} ≤ n < 2^ℓ} D_n`;
2. `𝔐_p g ≲ 𝔑_p g + ℰ g` where
   `𝔑_p g(r) = ∑_{n>0} 1_{D_n}(r) ∫_{2^{-n}}^{1/2} s^{-1/d}|g|` and
   `ℰ g(r) ≲ 1_{[1/3,2]}(r) ∫_{1/2}^4 s^{-1/d}|g|`.  Note `e = -1/d` at
   `p = p_d`, which is why the weight is `s^{-1/d}`;
3. `ℰ` is handled by plain Hölder on `[1/2,4]`;
4. for `𝔑`, with the doubly exponential blocks `J_m = [2^{-2^{m+1}}, 2^{-2^m}]`,
   Hölder with the pair `(d, p_d)` gives
   `|𝔑_p g(r)| ≲ ∑_{k=0}^{ℓ} 2^{(ℓ-k)/d} (∫_{J_{ℓ-k}} |g|^{p_d})^{1/p_d}`
   for `r ∈ Ω_ℓ`, because `∫_{J_m} s^{-1} ds = 2^m log 2`.

Done this cycle: `brsOmega` with `volume_brsOmega_le` and `brsOmega_disjoint`;
`brsLogBlock` with `integral_inv_brsLogBlock` (`∫_{J_m} s^{-1} = 2^m log 2`).

The paper finishes step 4 with the triangle inequality in `ℓ^q`, i.e. countable
Minkowski, which Mathlib does not have.  **Use the Prop 4.5 route instead**:
write `2^{(ℓ-k)/d} G_{ℓ-k} = c_k · (2^{ℓ/d} G_{ℓ-k})` with `c_k = 2^{-k/d}`,
apply `tsum_weighted_le` in `k`, raise to the `q`-th power, then Tonelli
(`ENNReal.tsum_comm`) and `|Ω_ℓ| 2^{ℓq/d} ≲ B^q`; the `k`-sum contributes
`(∑_k c_k)^{q-1} · ∑_k c_k = (∑_k 2^{-k/d})^q < ∞` and the `ℓ`-sum collapses by
disjointness of the `J`'s plus `tsum_rpow_le_tsum_rpow`.  This is exactly the
architecture of `prop45_brsMainMaximal`, with the geometric gain replaced by
the `2^{-k/d}` weights.

## Handoff addendum (2026-09-05)

§4 is now complete through the exponent bookkeeping: `prop46_brsMainMaximal`
(the `p = p_d` endpoint, with `logShell_term_le`, `tsum_brsOmega_le`,
`exists_endpoint_bound`), `exists_cov_bound_of_minkowski` ((4.9): a Minkowski
exponent `β < q a + 1` supplies the dyadic covering hypothesis of Prop 4.5),
`volume_closure_eq_zero_of_minkowski` (discharges `hEnull` from `β < 1`), and
`exists_combined_bound` (Lemma 4.1's three pieces collected into one bound by
the weighted profile norm; takes the main-term estimate as a hypothesis, so
Prop 4.4, 4.5 or 4.6 can be plugged in).

Two facts needed for that collection, now available:

- `measurable_brsRemainderOne/Two` and `measurable_brsMainMaximal`: the
  dilation supremum may be taken over a countable set — over `ℚ` for the
  remainders (the constraint on `t` is an interval with rational interior
  points) and over a countable dense subset of `E` for the main term (the
  constraint `t ∈ Ioo (r/2) (3r/2)` is *open*, so density suffices).  The
  window integral is continuous in `t` because after the substitution the
  integrand is `s^{D-2} |f₀(s)|`, continuous for `D ≥ 2`
  (`mainMaximal_window_eq`, `continuous_window_integral`).
- lintegral additivity needs only *one* measurable summand
  (`lintegral_add_right'`), which is why the two remainders suffice.

### Remaining plan for Theorem 1.1

1. Radial lift: `Auto.Spherical.SurfaceMeasureDecay.lintegral_euclidean_radial`
   turns `∫⁻ F ‖x‖` into `ofReal (surfaceMass D) * ∫⁻ r in Ioi 0, r^{D-1} F r`
   for **measurable** `F` — now applicable to `F = (𝔐 + R₁ + R₂)^q`.
2. `MemLp (M E f) q` for a continuous radial `f`: use the public
   `measurable_restrictedNormalizedSphericalMaximal` route of
   `memLp_restrictedSphericalMaximal_of_le` in `AHRSUpperBounds` (measurability
   of `M E f` for continuous `f`), plus the finite norm bound.
3. Scope warning for the `⊇` inclusion: `HasRadialStrongType` as defined
   quantifies over *all* `MemLp f p` radial data, whereas Lemma 4.1 needs a
   continuous profile.  Passing from continuous profiles to all of `L^p_rad`
   needs a radial density argument that Mathlib does not have (the RS
   development in this repo restricts its type set to a Schwartz core, and
   BRRS's `HasRadialSchwartzLpApproximation` is left as a hypothesis).  So the
   `⊇` inclusion should first be proved for the continuous-profile core; a
   single-definition `𝒯^rad_E = Δ_β` additionally requires upgrading the two
   endpoint exclusions of §3 (`not_hasRadialStrongType_top_left/right`, which
   use indicator test functions) to continuous test data — the trapezoid
   construction of `steinBump` is the model for that.
