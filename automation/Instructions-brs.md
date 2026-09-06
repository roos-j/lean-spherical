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

## Handoff addendum (2026-09-06)

Section 5 progress this session:

* **Lemma 5.1** (`le_brsDecompositionTwo`) is complete: the planar spherical
  maximal operator on radial data is dominated pointwise by
  `8 * (surfaceMass 2)⁻¹ * surfaceMass 1` times the sum of the two main terms
  `brsMainTwoLeft/Right` and the four remainders `brsRemTwoOne{Left,Right}`,
  `brsRemTwoTwo{Left,Right}`.  The four remainder operators now carry the
  dilation set `E` as their first argument (they used to range over all of
  `[1,2]`); this is required for Proposition 5.2 and Lemma 5.3, whose gains
  come from covering numbers of `E`.
* **(5.1)** (`brsRemTwoOne{Left,Right}_le_tsum`) decomposes `R_1^±` into the
  dyadic blocks `brsR1Piece{Left,Right}` at scales `brsDyadic m = 2^{-m}`.
* **Proposition 5.2** (`prop52_brsRemTwoOne{Left,Right}`) is complete for
  `1 < p ≤ q`.  The machinery is: `brsCenteredWindow`/`brsCenteredPiece`
  (windows of length `3δ` moving with slope `+1` in the radius, cut to
  `s ≥ r/2`, `s ≥ 1`), `lintegral_brsCenteredPiece_pow_le` (Hölder + Tonelli),
  `iSup_rpow_le_sum` (`(sup)^q ≤ Σ`), and `lintegral_weight_rpow_tsum_le`
  (Minkowski for countable sums with the weight `r dr`, itself built on
  `lintegral_rpow_tsum_le`).
* **Lemma 5.3** (`lemma53_brsRemTwoTwo{Left,Right}`) is proved **for
  `1 ≤ p ≤ 2`** exactly in the paper's form.  Machinery:
  `brsWindowSigned`/`brsPieceSigned` (windows moving with slope `σ = ±1`, cut
  to `s ≥ r/2`, `s ≥ 1/3`), `lintegral_brsPieceSigned_diag_le`, and
  `lintegral_iSup_signed_diag_le`.
  *Scope note*: the paper states Lemma 5.3 for all `1 ≤ p < ∞` and defers the
  proof to [20, Prop. 5.3].  The elementary Hölder+Tonelli argument used here
  gives the stated exponent `N(E,2^{-m})^{1/p} 2^{-m/2}` only for `p ≤ 2`; for
  `p > 2` the same argument yields `N(E,2^{-m})^{1/p} 2^{-m/p}`, which is
  weaker (it is not summable for sets of full dimension).  The `p > 2` case
  needs the argument of [20] (or a disjointified grid cover, which gives
  `2^{-m/p}` with no covering factor).  This is the one gap in §5 so far.

## Blocker analysis (2026-09-06) — what remains and why it is not reachable here

Rows still open fall into three groups, and all of them are downstream of
machinery that Mathlib does not have (verified against the pinned Mathlib in
`.lake/packages/mathlib`: no `Marcinkiewicz`/real interpolation, no
Littlewood--Paley, no local smoothing / L^p-improving spherical estimates):

1. **§5 (5.5)–(5.14), Propositions 5.4, 5.5, 5.6.**  BRS's proof of
   Proposition 5.4 needs (a) Marcinkiewicz interpolation to upgrade the
   weak-type bound for the `ℬ_k` terms to (5.6), and (b) a Littlewood--Paley
   resolution of the identity `δ = u_k + Σ_{m≥1} υ_{k+m} * ψ_{k+m}` with
   vanishing-moment kernel estimates (5.11)–(5.13) plus the square-function
   bounds used in the final summation.  Propositions 5.5 and 5.6 bound the
   main terms `𝔐_p^±` and rest on oscillatory-integral / local-smoothing
   estimates for spherical averages.  None of this exists in Mathlib; each is
   a large independent formalization project.
2. **Theorem 1.2** is the assembly of those propositions, so it inherits the
   blocker.
3. **Corollary 1.3 and Theorem 1.4 (i)–(v)** are `d = 2` results (the paper's
   abstract: higher dimensions are governed by the Minkowski dimension —
   Theorem 1.1 — while "in two dimensions we determine the closure of the
   L^p → L^q type set ... in terms of a dimensional spectrum closely related
   to the upper Assouad spectrum"), and both are corollaries of Theorem 1.2.
   Their §2 inputs are done: (2.1)–(2.3) and Lemma 2.1 (`lemma21_brs`).

Everything not in that dependency cone is finished: Theorem 1.1 (i)–(iii) for
`d ≥ 3` (`thm11_radialTypeSet`), the §3 necessary conditions including
Lemma 3.5, all of §4, and the §5 reductions Lemma 5.1, (5.1), Proposition 5.2,
Lemma 5.3 (`1 ≤ p ≤ 2`), (5.2).

Recommended next step for a future session: pick **one** of the missing
foundations and build it as a standalone file (real interpolation is the
smallest; Littlewood--Paley on `ℝ` is the one §5 really needs), then resume at
row "(5.5) decomposition of R₂^± f₀".

## Addendum (2026-09-05, later): what the elementary method reaches in §5

* `(5.5)` and `(5.6)` are done for both halves (`brsRemTwoTwo{Left,Right}_le_add`,
  `prop56_brsBFar{Left,Right}`).  Note that (5.6) needs **no** interpolation as
  long as `q < 2p`: the pointwise bound `ℬf₀(r) ≲ r^{-1/p}‖f₀‖_p`, together with
  `ℬf₀ = 0` for `r > 4/3`, integrates directly against `r dr`.  Only the
  endpoint `q = 2p` needs Marcinkiewicz.
* `prop54_brsRemTwoTwo{Left,Right}` give an **off-diagonal** bound for the whole
  of `R_2^±` in the range `1 < p ≤ q ≤ 2`, with the paper's exponent
  `2^{-m(1/2+1/q-1/p)}` but with the *global* covering numbers `N(E,2^{-m})^{1/q}`
  in place of the localized `‖ω_m^{p,q}(E,k)‖_{ℓ^{2q/(2-q)}_k}`.  The machinery is
  `lintegral_brsPieceSigned_offdiag_le` (Hölder + the linearization
  `X^{q/p} ≤ X·M^{q/p-1}` + Tonelli) and `lintegral_iSup_signed_offdiag_le`.
  Getting the localized quantity — and the range `q > 2` — is what needs the
  Littlewood--Paley decomposition of (5.7).

## Addendum (2026-09-05, evening): starting the Littlewood--Paley foundation

`(5.7)` is now partially in place, at the elementary level:

* `brsDilate φ j x = 2^j φ(2^j x)` with `integral_brsDilate` (dilation
  preserves the integral), continuity and compact support lemmas.
* `brsLPKernel φ j = brsDilate φ (j+1) - brsDilate φ j`, with
  `integral_brsLPKernel_eq_zero` — the first vanishing moment.
* `brsDilate_eq_add_sum` (pointwise telescoping) and `brs_lp_resolution`
  (its convolution form against a continuous `g`).

What is still missing before (5.11)–(5.13) can be attempted:
1. the approximate-identity limit `φ_J * g → g` (Mathlib has
   `ContDiffBump.convolution_tendsto_right`, whose normalization must be
   matched to `brsDilate`);
2. the second factorization `ψ = υ * ψ̃` with vanishing moments of order `N`
   on both factors — this is the part that makes (5.11) possible;
3. the kernel estimate `|h_k * υ_{k+m}(x)| ≲ 2^{(k+m)/2}(1+2^{k+m}|x|)^{-N}`,
   which is integration by parts against those moments.

## Addendum (2026-09-06): the Littlewood--Paley foundation as it now stands

Available in BRSRadial.lean:

* `brsDilate`, `brsLPKernel`, `brsDilate_eq_add_sum`, `brs_lp_resolution`,
  `tendsto_brsDilate_convolution`, `brs_lp_resolution_tendsto` — the dilates
  form an approximate identity and the LP pieces resolve it.
* `IsBRSProfile N φ`, `integral_pow_mul_brsLPKernel_eq_zero`,
  `isBRSProfile_of_coeffs`, `exists_brs_coeffs`, `exists_isBRSProfile` — for
  every `N` there is a profile whose LP pieces have all moments below `N`
  vanishing.  (The paper's factorization `ψ = υ * ψ̃` is unnecessary in this
  formulation: the moments sit on `ψ_j` itself.)
* `brsMomentKernel` and `integral_pow_mul_brsMomentKernel` — an alternative
  `N`-fold-difference construction with the same moment property.
* `enorm_smoothed_le` — Hölder for the smoothed function.
* `lintegral_enorm_brsDilate_rpow` — the `L^q` norm of a dilate.

The next analytic step is (5.11): the decay estimate for `h_k * ψ_{k+m}`,
obtained by integrating the vanishing moments against the Taylor remainder of
the singular kernel `h_k`.  That is where the moments finally get used, and it
is the first estimate in this chain that is not bookkeeping.

## Addendum — §5.2, the terms `𝒜_{k,m}` (2026-09-05)

**Paper formulas, confirmed against arXiv:2412.09390v1 §5.2.**

- `I_0 = [1/2, 4/3]`, `I_k = [2^{-k-1}, 2^{-k}]` for `k > 0`;
- `u_k = 2^k u(2^k ·)`, `υ_ℓ = 2^{ℓ-1} υ_1(2^{ℓ-1} ·)`, `ψ_ℓ = 2^{ℓ-1} ψ_1(2^{ℓ-1} ·)`;
- (5.7) resolution: `δ = u_k + Σ_{m≥1} υ_{k+m} * ψ_{k+m}`;
- `𝒜_{k,0} f₀(r,t) = r^{-1/2} 1_{I_k}(r) (h_k * u_k * f₀)(t-r)`;
- `𝒜_{k,m} f₀(r,t) = r^{-1/2} 1_{I_k}(r) (h_k * υ_{k+m} * ψ_{k+m} * f₀)(t-r)`;
- `ω_m^{p,q}(E,k) = sup_{|J| = 2^{-k}} 2^{-k(2/q - 1/p)} N(E ∩ J, 2^{-m-k})^{1/q}`;
- (5.11) `|h_k * υ_{k+m}(x)| ≲ 2^{(k+m)/2} (1 + 2^{k+m}|x|)^{-N}`;
- (5.12) Young with `1/p + 1/r = 1 + 1/q`:
  `‖h_k * υ_{k+m} * g‖_q ≲ 2^{(k+m)(1/p - 1/q - 1/2)} ‖g‖_p`;
- (5.13) the same with `sup` over an interval of length `2^{-k-m}`;
- (5.9) `‖sup_{t∈E} |𝒜_{k,m} f₀|‖_q ≲ 2^{-m(1/2 + 1/q - 1/p)} ω_m^{p,q}(E,k) ‖ψ_{k+m}*f₀‖_p`,
  obtained by tiling `[1,2]` into intervals `J_{k,μ}` of length `2^{-k}` (with
  `5×` dilates `J*_{k,μ}`) and covering each `E ∩ J_{k,μ}` by
  `N(E ∩ J_{k,μ}, 2^{-k-m})` intervals of length `2^{-k-m}`.

**What is now formalised for `m = 0`.**  `brs_5_8` proves

```
∫⁻ r, (∑' k, brsAZero k G r) ^ q * ofReal r
  ≤ ofReal (brsAZeroConst a q / (1 - 2 ^ (-(2 - q/p)))) * (∫⁻ ‖G‖ₑ^p) ^ (q/p)
```

for `a` the Hölder conjugate of `p` with `a < 2` (i.e. `p > 2`) and `q < 2p`.
The chain is: `brsTruncKernel k` (the kernel `y^{-1/2}` truncated to
`(0, 2^{-k}]`) with `lintegral_brsTruncKernel_rpow` for its `L^a` norm;
`enorm_convolution_le_holder` (Hölder, uniform in the translation, hence also a
bound for the `t`-supremum); `brsRadiusWindow k = Ioc (2^{-k-1}) (2^{-k})`, whose
pairwise disjointness (`brsRadiusWindow_disjoint`) turns `(∑' k · )^q` into
`∑' k (·)^q` (`tsum_brsAZero_rpow`); `lintegral_brsRadiusWindow_rpow_le` for the
`r dr` weight; and a geometric series with ratio `2^{-(2 - q/p)}`.  The
low-frequency factor `u_k` is absorbed into `G`, which is legitimate because
`‖u_k * f₀‖_p ≤ ‖u_k‖_1 ‖f₀‖_p = ‖f₀‖_p` by `lintegral_convolution_rpow_le`.

**Verified exponent arithmetic for the `m ≥ 1` terms.**  The support of
`h_k * υ_j` (`j = k + m`) is contained in `(-2^{-j}, 2^{-k} + 2^{-j}]`, and

- near the singularity (`|x| ≲ 2^{-j}`): `|h_k * υ_j| ≲ ‖υ_j‖_∞ ∫_0^{2^{-j}} σ^{-1/2} dσ ≈ 2^{j/2}`;
- in the bulk (`2^{-j} ≪ x ≤ 2^{-k}`): the vanishing moments of `υ_j` give
  `|h_k * υ_j(x)| ≲ x^{-1/2} (2^{-j}/x)^{N+1}` — this is exactly
  `brs_kernel_cancellation`, already available, with `δ = 2^{-j}`.

Both regions give `‖h_k * υ_j‖_r ≈ 2^{j(1/2 - 1/r)}`, and with
`1/r = 1 + 1/q - 1/p` this is `2^{j(1/p - 1/q - 1/2)}`, i.e. exactly (5.12).
The cancellation is *not* optional: without it the bulk contributes
`2^{-k(1/r - 1/2)}`, which is larger than the required `2^{-j(1/r - 1/2)}`.

**Next steps, in order.**  (i) the two-region `L^r` bound for `h_k * υ_j`;
(ii) (5.13), the interval maximal estimate, from
`norm_le_average_add_integral_deriv` / `iSup_enorm_le_of_cover_complex`;
(iii) the tiling/covering assembly against `brsOmegaTwo`; (iv) (5.10), the sum
over `m`, whose ratio is `2^{-m(1/2 + 1/q - 1/p)}` times the growth of
`ω_m^{p,q}(E,k)`.

**Still genuinely blocked.**  The two endpoint rows (`Proposition 4.3` at
`q = pd`, `(5.6)` at `q = 2p`) are *not* reachable by interpolation between the
bounds now available: in both cases the endpoint is where a pointwise bound's
radial integral diverges logarithmically, and the two bounds one could
interpolate lie on the same side of the endpoint.  `marcinkiewicz_diagonal` and
`lintegral_rpow_lintegral_le` (Minkowski's integral inequality, unconditional
apart from a finiteness hypothesis) are in place should an off-diagonal
interpolation still be wanted elsewhere.

## Addendum — the kernel `h_k * ψ` (BRS (5.11)–(5.12)) is formalised

`brsTruncConv k ψ x = ∫ y, h_k(x - y) ψ y dy`, with `h_k = brsTruncKernel k`.
The chain, all in `BRSRadial.lean`:

- `integral_brsTruncKernel_mul_eq_zero` / `brsTruncConv_eq_zero`: the support is
  contained in `(-δ, 2^{-k} + δ]`;
- `lintegral_brsTruncKernel_Ioc_le`: the local `L¹` norm of `h_k` on any
  interval ending at `b > 0` is at most `2√b` (worst case: starting at the
  singularity);
- `enorm_brsTruncConv_le_near`: window one, `x ≤ 4δ`, gives `M · 2√(5δ)`;
- `integral_brsTruncKernel_mul_eq` + `norm_integral_brsTruncKernel_mul_le_bulk`
  + `enorm_brsTruncConv_le_bulk`: window two, `4δ < x ≤ 2^{-k} - δ`, removes the
  truncation (the window `[x-δ, x+δ]` lies inside `(0, 2^{-k}]`) and applies
  `brs_kernel_cancellation`, gaining `δ^{N+1} (x-δ)^{-1/2-(N+1)}`;
- `brsTruncKernel_le_of_ge` + `enorm_brsTruncConv_le_far`: window three,
  `2^{-k} - δ < x ≤ 2^{-k} + δ`, where `h_k ≤ (2δ)^{-1/2}` because
  `x - δ > 2^{-k} - 2δ ≥ 2δ`;
- `lintegral_le_three_regions` glues the three windows (`lintegral_union_le`
  twice, after restricting to the support);
- `lintegral_brsTruncConv_region_{one,two,three}_le` are the three `L^r` masses,
  the bulk one using `lintegral_Ioi_shift_rpow` (the translated tail integral of
  a power);
- `lintegral_enorm_brsTruncConv_rpow_le` is the three-term bound, and
  `lintegral_enorm_brsTruncConv_rpow_le_scale` normalises it (via
  `rpow_mul_rpow_scale` and `brsTruncConv_window_{one,two,three}_le`) to

  ```
  ∫⁻ x, ‖brsTruncConv k ψ x‖ₑ ^ r ≤ ofReal (brsKernelConst Mu A N r * δ ^ (1 - r/2))
  ```

  under `5δ ≤ 2^{-k}`, `1 ≤ r`, `M·δ ≤ Mu` (`M` the height of `ψ`), `∫|ψ| ≤ A`
  and `N + 1` vanishing moments.  That is exactly `‖h_k * ψ‖_r ≈ δ^{1/r - 1/2}`,
  i.e. BRS (5.12).

Also new: `lintegral_mul_mul_le_Lp_Lq_Lr`, Hölder for three factors in `ℝ≥0∞`
(Mathlib has only two), obtained by applying the two-factor version twice with
the exponent pair `(b/a', c/a')`, which is Hölder-conjugate exactly when
`a⁻¹ + b⁻¹ + c⁻¹ = 1`.

**Immediate next step for (5.9).**  General Young `L^r * L^p → L^q` with
`1/p + 1/r = 1 + 1/q`, from the pointwise splitting
`|K(y) g(x-y)| = (|K|^r |g|^p)^{1/q} · |K|^{1-r/q} · |g|^{1-p/q}`
and `lintegral_mul_mul_le_Lp_Lq_Lr` with exponents `q`, `rq/(q-r)`, `pq/(q-p)`
(these satisfy `1/q + (q-r)/(rq) + (q-p)/(pq) = 1/r + 1/p - 1/q = 1`), followed
by Tonelli (`lintegral_convolution_swap` generalises).  The case `q = p`
(equivalently `r = 1`) is already `lintegral_convolution_rpow_le`.
Then (5.13) on an interval of length `2^{-k-m}`, then the tiling/covering
assembly against `brsOmegaTwo`.

## Addendum — Young and the localized maximal estimate in `L^q`

Three more prerequisites for (5.9) are in place.

**Young's convolution inequality** with three exponents,
`lintegral_convolution_rpow_le_young`: for `1 ≤ p`, `1 < r < q`, `p < q` and
`1/p + 1/r = 1 + 1/q`,

```
∫⁻ x, ‖∫ y, K y * g (x - y)‖ₑ ^ q ≤ (∫⁻ ‖K‖ₑ^r)^(q/r) * (∫⁻ ‖g‖ₑ^p)^(q/p)
```

The proof avoids Minkowski entirely: the pointwise splitting
`|K(y) g(x-y)| = (|K|^r|g|^p)^{1/q} · |K|^{r/s} · |g|^{p/t}` with
`s = rq/(q-r)`, `t = pq/(q-p)` (so `1/q + 1/s + 1/t = 1/r + 1/p - 1/q = 1`),
then `lintegral_mul_mul_le_Lp_Lq_Lr` (three-factor Hölder) and
`lintegral_convolution_swap'` (Tonelli with both factors raised to a power).
The four degenerate cases (`R = 0`, `P = 0`, `R = ⊤`, `P = ⊤`) are dispatched
from the pointwise estimate itself.  `r = 1`, i.e. `p = q`, remains
`lintegral_convolution_rpow_le`.

**The window maximal function** `brsWindowMax F F' a δ r`, a *measurable*
majorant of `sup_{t ∈ [a-δ/2, a+δ/2]} ‖F (t - r)‖ₑ`
(`iSup_enorm_translate_le_brsWindowMax`, from
`norm_le_average_add_integral_deriv` composed with `HasDerivAt.comp_sub_const`).
Measurability in `r` comes from `Measurable.lintegral_prod_right'`, which is why
the majorant is phrased with `∫⁻` rather than a Bochner integral.

**Its `L^q` norm** (`lintegral_brsWindowMax_rpow_le`):

```
(∫⁻ r, brsWindowMax F F' a δ r ^ q)^(1/q) ≤ ‖F‖_q + ofReal δ * ‖F'‖_q
```

via `ENNReal.lintegral_Lp_add_le` and `lintegral_setLIntegral_translate_rpow_le`,
the latter being Hölder on the window followed by Tonelli — this is what
replaces the continuous Minkowski inequality, whose finiteness hypothesis would
have been circular here.

**The localized maximal estimate** (`lintegral_iSup_enorm_translate_rpow_le`):
for an interval cover `ι` of `E` of mesh `δ`,

```
∫⁻ r, (⨆ t ∈ E, ‖F (t - r)‖ₑ) ^ q ≤ ι.card * (‖F‖_q + ofReal δ * ‖F'‖_q) ^ q
```

so the covering number enters as `N^{1/q}`, exactly as in `ω_m^{p,q}(E,k)`.
Note that no measurability of `r ↦ ⨆ t ∈ E, ‖F (t-r)‖ₑ` is needed: `lintegral`
is monotone without it.

**What remains for (5.9).**  Define `𝒜_{k,m}` from `brsTruncConv k (υ_{k+m})`
and `g = ψ_{k+m} * f₀`, then chain: `lintegral_iSup_enorm_translate_rpow_le`
with `δ = 2^{-k-m}` and the cover of `E ∩ J` (`brsOmegaTwo`), then
`lintegral_convolution_rpow_le_young` for `‖F‖_q` and `‖F'‖_q`, then
`lintegral_enorm_brsTruncConv_rpow_le_scale` for `‖h_k * υ_{k+m}‖_r`; the
derivative `F' = (h_k * υ_{k+m}') * g` costs `2^{k+m}`, which the factor
`ofReal δ = 2^{-k-m}` exactly cancels.  Finally multiply by the weight
`r^{-1/2} 1_{I_k}(r)` and integrate against `r dr`, which contributes
`2^{k/2} 2^{-k/q}`; the total exponent is
`2^{k(1/p - 2/q)} 2^{-m(1/2 + 1/q - 1/p)}`, matching BRS (5.9).

## Addendum — `brs_5_9_core`, the analytic core of (5.9)

`brsTruncConvReal k ψ x = ∫ y, h_k (x - y) ψ y` is the real-valued form of
`brsTruncConv` (`brsTruncConv_eq_ofReal`, `enorm_brsTruncConv`), and equals
Mathlib's convolution `ψ ⋆[mul] h_k` (`brsTruncConvReal_eq_convolution`).  From
`integrable_brsTruncKernel` (total mass `2·2^{-k/2}`) and
`hasCompactSupport_brsTruncKernel` one gets

- `contDiff_brsTruncConvReal`: `h_k * ψ` is as smooth as `ψ`;
- `hasCompactSupport_brsTruncConvReal`;
- `hasDerivAt_brsTruncConvReal`: `(h_k * ψ)' = h_k * ψ'`.

These are exactly the hypotheses `hasDerivAt_kernel_convolution` needs, so the
smoothed operator `F = (h_k * υ) * g` is differentiable with
`F' = (h_k * υ') * g`.  Combining that with
`lintegral_iSup_enorm_translate_rpow_le` (the localized maximal estimate) and
`lintegral_convolution_rpow_le_young` (Young) gives **`brs_5_9_core`**:

```
∫⁻ x, (⨆ t ∈ E, ‖((h_k * υ) * g) (t - x)‖ₑ) ^ q
  ≤ ι.card * (‖h_k * υ‖_r ‖g‖_p + ofReal δ * ‖h_k * υ'‖_r ‖g‖_p) ^ q
```

for any interval cover `ι` of `E` of mesh `δ`, with `1 ≤ p`, `1 < r < q`,
`p < q` and `1/p + 1/r = 1 + 1/q`.  `#print axioms` on it shows only
propext / Classical.choice / Quot.sound.

**Remaining for the (5.9) row.**  Instantiate with `υ = brsDilate υ₁ (k+m)`,
`δ = 2^{-k-m}`, `g = ψ_{k+m} * f₀`, and feed the two kernel norms from
`lintegral_enorm_brsTruncConv_rpow_le_scale` (using `enorm_brsTruncConv` to move
between the ℂ- and ℝ-valued forms).  For `υ'` the parameters are `Mu = δ^{-1}‖υ₁'‖_∞`
and `A = δ^{-1}∫|υ₁'|`, which is exactly the extra `δ^{-1}` that the prefactor
`ofReal δ` cancels.  Then take `ι` realising `intervalCoveringNumber (E ∩ J) δ`
so that `ι.card` becomes the `N(E ∩ J, 2^{-k-m})` of `ω_m^{p,q}(E,k)`, and
multiply by the radial weight `r^{-1/2} 1_{I_k}(r)` against `r dr`.

## Addendum — (5.9) is complete

`brs_5_9` and `brs_5_9_covering` are proved; the ledger row is `complete`.

`brsAmMax k j υ g E r` is `𝒜_{k,m}` as a maximal function of the radius:
`r^{-1/2} 1_{I_k}(r) · sup_{t ∈ E} |(h_k * υ_j * g)(t - r)|`, with `j = k + m`
and `g = ψ_{k+m} * f₀` carried abstractly (legitimate because everything
downstream sees `g` only through `‖g‖_p`).

The chain, with `1/r = 1 + 1/q - 1/p`:

1. `lintegral_brsAmMax_rpow_le` strips the radial weight: on `I_k`,
   `r^{-q/2} · r ≤ 2^{|1-q/2|} (2^{-k})^{1-q/2}` (`rpow_le_of_mem_brsRadiusWindow`);
2. `brs_5_9_core` = localized maximal estimate + Young;
3. `brs_5_9_dilate` instantiates the bump at scale `2^{-j}`, using
   `lintegral_enorm_brsTruncConvReal_dilate_le` for `‖h_k * υ_j‖_r` and, for the
   derivative, `deriv_brsDilate_eq` (`(υ_j)' = (2^j υ')_j`) together with
   `brsKernelConst_smul` (the constant is homogeneous of degree `r`); the extra
   `2^j` from the derivative is exactly cancelled by the prefactor `ofReal δ`;
4. `brs_5_9_covering` replaces the cardinality of an arbitrary cover by
   `intervalCoveringNumber E (2^{-j})`, via
   `exists_intervalCover_card_eq_intervalCoveringNumber`.

**The exponents check out against the paper.**  Taking `q`-th roots, the bound is
`const · (2^{-k})^{1/q - 1/2} · N^{1/q} · (2^{-j})^{1/r - 1/2} · ‖g‖_p`, and with
`1/r - 1/2 = 1/2 + 1/q - 1/p` and `j = k + m` this is
`2^{k(1/p - 2/q)} · 2^{-m(1/2 + 1/q - 1/p)} · N(E, 2^{-k-m})^{1/q} · ‖g‖_p`,
which is BRS (5.9) with `ω_m^{p,q}(E,k)` spelled out.

**Next row: (5.10), the summation in `m`.**  The ratio is
`2^{-m(1/2 + 1/q - 1/p)}` against the growth of `ω_m^{p,q}(E,k)`; the geometric
series converges when `1/2 + 1/q - 1/p` beats that growth, which is where the
Assouad spectrum enters through `brsOmegaTwo`.  The `k`-sum then reuses the
disjointness of the windows `I_k` (`brsRadiusWindow_disjoint`,
`tsum_brsAZero_rpow`), exactly as in (5.8).

## Addendum — (5.10) and (5.14) are complete

**(5.10), the summation in `m`.**  `brsAmMax` is measurable
(`measurable_brsAmMax`): the key point is that `r ↦ ⨆ t ∈ E, ‖F (t - r)‖ₑ` is a
supremum of continuous functions, hence lower semicontinuous, hence measurable
(`measurable_iSup_enorm_translate`) — no separability argument and no
restriction on `E`.  With that, the countable triangle inequality in `L^q`
applies.  Mathlib has only the two-term `ENNReal.lintegral_Lp_add_le`, so
`lintegral_Lp_finset_sum_le` (induction on the `Finset`) and
`lintegral_Lp_tsum_le` (partial sums, `ENNReal.tsum_eq_iSup_nat`,
`ennreal_iSup_rpow`, `lintegral_iSup`) were added.  `brsRadialMeasure` is
`volume.withDensity (ofReal ·)`, i.e. `r dr`, and
`lintegral_brsRadialMeasure` moves between `∫⁻ F ∂(r dr)` and `∫⁻ F · ofReal r`.
`lintegral_radial_Lp_tsum_le` is the general statement and `brs_5_10` its
instance for the terms `𝒜_{k,m}`.

**(5.14), localization by support.**  `brsTruncConvReal_dilate_eq_zero`: the
kernel `h_k * υ_j` vanishes for `|x| > 2^{-k} + 2^{-j}`.  Hence `brs_5_14`:

```
∫ y, (h_k * υ_j)(y) · g (x - y) = ∫ y, (h_k * υ_j)(y) · (S.indicator g) (x - y)
```

whenever `Icc (x - c) (x + c) ⊆ S` with `c = 2^{-k} + 2^{-j}` — the paper's
`h_k * υ_{k+m} * g = h_k * υ_{k+m} * [g 1_{J*}]`.

**Next rows.**  Proposition 5.4(i) (`2 ≤ q ≤ 2p`) and 5.4(ii) (`1 < q < 2`).
From the paper:

- 5.4(i): `‖R_2^± f₀‖_{L^q(r dr)} ≲ Σ_{m≥0} 2^{-m(1/2+1/q-1/p)} ‖ω_m^{p,q}(E,k)‖_{ℓ^∞_k} ‖f₀‖_{L^p(s ds)}`
- 5.4(ii): the same with `ℓ^∞_k` replaced by `ℓ^{2q/(2-q)}_k`

with `ω_m^{p,q}(E,k) = sup_{|J| = 2^{-k}} 2^{-k(2/q - 1/p)} N(E ∩ J, 2^{-m-k})^{1/q}`.
So the `k`-aggregation is an `ℓ^∞` (resp. `ℓ^{2q/(2-q)}`) norm over `k`, which
for `q ≥ 2` is where the disjointness of the windows `I_k` is used, exactly as
in (5.8) (`brsRadiusWindow_disjoint`, `tsum_brsAZero_rpow`).

## IMPORTANT — the repo already proves Littlewood–Paley unconditionally

`LeanSpherical/Auto/MikhlinHormander.lean` contains

```
theorem mikhlin {d N : ℕ} [NeZero d] {ι : Type*} (m : ι → Euclidean d → ℂ)
    {A : ℝ} (hA : 0 ≤ A) (hM : ∀ u, MikhlinCondition N (m u) A) (hNd : d < N)
    {p : ℝ} (hp : 1 < p) : ∃ B ≠ ∞, ∀ u f, eLpNorm (mikhlinMultiplier (m u) f) p ≤ B * eLpNorm f p

theorem littlewoodPaley_of_mikhlin {d : ℕ} [NeZero d] (C : lpCutoffs d) :
    littlewoodPaley C
```

both with `#print axioms` = propext / Classical.choice / Quot.sound, and both
files have zero `sorry`.  `littlewoodPaley C` unfolds to: for every `p > 1`
there is `A > 0` with
`∫ (finiteIntegerDyadicSquareEnergy C K f)^{p/2} ≤ A ∫ ‖f‖^p`
for every finite `K : Finset ℤ` and Schwartz `f`.  **Do not re-derive this.**

**How it enters Proposition 5.4.**  After (5.9) and (5.10) one needs
`(Σ_k ‖ψ_{k+m} * f₀‖_p^q)^{1/q} ≲ ‖f₀‖_p`.  For the BRS range `p > 2 ≤ q` the
route is: `ℓ^p ⊆ ℓ^q` (`p ≤ q`), then
`Σ_k ‖Δ_k f‖_p^p = ∫ Σ_k |Δ_k f|^p ≤ ∫ (Σ_k |Δ_k f|²)^{p/2} ≲ ‖f‖_p^p`,
whose first inequality is now available as
`ennreal_finset_rpow_sum_le_sq` (from `ennreal_finset_rpow_sum_le`, the
superadditivity of `t ↦ t^r` for `r ≥ 1`) and whose second is exactly
`littlewoodPaley_of_mikhlin`.

**The bridge that still has to be built.**  Two mismatches:

1. *Ambient type.*  The repo's LP theorem lives on `Euclidean d` (take `d = 1`)
   and acts on `SchwartzMap`; the BRS §5 work is on `ℝ` and on `L^p` functions.
   A measure-preserving identification `Euclidean 1 ≃ ℝ` plus a density
   argument is needed.
2. *Which decomposition.*  The repo's pieces are Fourier multipliers
   (`integerDyadicProjection`), whose kernels are Schwartz but **not**
   compactly supported.  The `𝒜_{k,m}` machinery proved here
   (`brs_5_9`, `brs_5_14`) assumes the bump `υ` is compactly supported in
   space — that is what gives the truncation removal, the three-window kernel
   analysis and the localization (5.14).  So the `ψ_ℓ` of the resolution
   (5.7) and the `Δ_k` of the square-function theorem are a priori different
   families; reconciling them (e.g. by proving the square-function bound for a
   spatially compactly supported wavelet family, or by keeping `υ` compactly
   supported while letting `ψ` be Fourier-localized, as BRS's
   `υ_{k+m} * ψ_{k+m}` factorization allows) is the remaining structural step
   before Proposition 5.4 can be assembled.

Note that BRS's own (5.7) factors the identity as `υ_{k+m} * ψ_{k+m}`, with the
compact support needed only for `υ` (it is `υ` that meets the singular kernel
`h_k`), while `ψ` may be Fourier-localized.  That is the intended route.

## Addendum — the `ℓ^p` Littlewood–Paley bound is now available in BRSRadial

`sum_integral_norm_rpow_dyadic_le`: for `d ≥ 1`, any
`C : Auto.LittlewoodPaley.lpCutoffs d` and any `p ≥ 2`,

```
∃ A > 0, ∀ (K : Finset ℤ) (f : 𝓢(Euclidean d, ℂ)),
  ∑ k ∈ K, ∫ x, ‖integerDyadicProjection C.cutoff k f x‖ ^ p ≤ A * ∫ x, ‖f x‖ ^ p
```

with `#print axioms` clean.  This is the quantity Proposition 5.4 needs after
(5.9) and (5.10), and the constant is uniform in the finite scale set `K`.

Route (all steps now in `BRSRadial.lean`):

- `brsDyadicSchwartz` / `brsDyadicSchwartz_apply`: the dyadic projection of a
  Schwartz function is Schwartz, namely
  `𝓕⁻ (smulLeftCLM ℂ (intDyadicBandpassMultiplier C.cutoff n) (𝓕 f))`
  (this mirrors a `private` construction in `Spherical/Bourgain.lean`);
- `integrable_norm_rpow_integerDyadicProjection`: hence `‖Δ_k f‖^p` is
  integrable for every `p > 0` (via `SchwartzMap.memLp` and
  `MemLp.integrable_norm_rpow`);
- `real_finset_rpow_sum_le` / `real_finset_rpow_sum_ge`: the two power-mean
  inequalities `∑ b^r ≤ (∑ b)^r ≤ card^{r-1} ∑ b^r` for `r ≥ 1`;
- `finset_sum_norm_rpow_le_squareEnergy`: `∑_k ‖Δ_k f x‖^p ≤ (square energy)^{p/2}`
  for `p ≥ 2` (the `ℓ² ⊆ ℓ^p` step);
- `integrable_squareEnergy_rpow`: the majorant `card^{p/2-1} ∑_k ‖Δ_k f‖^p`
  makes `(square energy)^{p/2}` integrable, which is what
  `integral_mono_of_nonneg` needs;
- then `Auto.MikhlinHormander.littlewoodPaley_of_mikhlin`.

**Remaining for Proposition 5.4.**  Only the two structural mismatches recorded
above: transporting from `Euclidean 1` / Schwartz to `ℝ` / `L^p`, and matching
the `ψ_ℓ` of the BRS resolution (5.7) with the Fourier-multiplier `Δ_k`.  The
analytic content on both sides is now in place.

## Addendum — the first structural mismatch is closed: `Euclidean 1 ≃ ℝ`

`brsLineEquiv : Euclidean 1 ≃ᵐ ℝ` is
`(MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)`,
and `measurePreserving_brsLineEquiv` proves it volume preserving by composing
`EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)` with
`volume_preserving_funUnique (Fin 1) ℝ`.  The four transport lemmas
`lintegral_brsLineEquiv`, `integral_brsLineEquiv`,
`lintegral_brsLineEquiv_symm`, `integral_brsLineEquiv_symm` move integrals in
both directions.

Consequently `sum_integral_norm_rpow_dyadic_le_line` states the `ℓ^p`
Littlewood–Paley bound *on the line*: for `p ≥ 2` there is `A > 0` with

```
∑ k ∈ K, ∫ y : ℝ, ‖Δ_k f (brsLineEquiv.symm y)‖ ^ p ≤ A * ∫ y : ℝ, ‖f (brsLineEquiv.symm y)‖ ^ p
```

for every finite `K : Finset ℤ` and Schwartz `f` on `Euclidean 1`.

**What is left before Proposition 5.4.**  Two things, both structural rather
than analytic:

1. *Schwartz to `L^p`.*  The bound above is for Schwartz `f`; BRS apply it to
   `f₀ ∈ L^p(s ds)`.  A density argument is needed (Schwartz functions are
   dense in `L^p` for `1 ≤ p < ∞`).
2. *Which family.*  The `Δ_k` above are the Fourier multipliers
   `intDyadicBandpassMultiplier C.cutoff k`, whose kernels are Schwartz but not
   compactly supported, whereas `brs_5_9` / `brs_5_14` need the bump `υ` that
   meets the singular kernel `h_k` to be compactly supported in space.  BRS's
   own factorization `υ_{k+m} * ψ_{k+m}` is designed exactly for this: `υ` is
   the compactly supported factor with vanishing moments, `ψ` the
   Fourier-localized one, and only `ψ` is fed to the square-function theorem.
   Formalizing the factorization means choosing `υ` compactly supported with
   `\hat υ` non-vanishing on the annulus `1/2 ≤ |ξ| ≤ 2` and defining
   `\hat ψ_j := (\hat φ_j - \hat φ_{j-1}) / \hat υ_j`; this is the remaining
   construction.

## Addendum — the hypotheses of (5.9) are satisfiable

`brs_5_9_dilate` carries a long list of assumptions on the bump `υ` and on
`deriv υ`.  It was worth checking that they can all hold at once, since a
mismatch would have made the estimate vacuous.  They can:

`exists_brsBumpFull N` produces `υ, Mu, A, Mu', A'` with *every* hypothesis of
`brs_5_9_dilate` satisfied — `ContDiff ℝ 1` for `υ` and for `deriv υ`, compact
support for both, `tsupport ⊆ closedBall 0 1` for both, the pointwise bounds,
the `L¹` bounds, and vanishing moments of every order `≤ N` for both `υ` and
`deriv υ`.

Construction (`exists_brsBump`): take a `ContDiffBump (0 : ℝ)` with
`rIn = 1/2`, `rOut = 1`, normalise it to `χ`, form the BRS profile
`φ = ∑_{l < N+2} a l · χ_l` with the Lagrange coefficients of
`exists_brs_coeffs`, and take `υ = brsLPKernel φ 0 = φ_1 - φ_0`.  All moments of
order `< N + 2` of `υ` then vanish (`integral_pow_mul_brsLPKernel_eq_zero`), and
the support stays inside the unit ball because the outer radius is one
(`tsupport_subset_closedBall_of_vanishing`).

For `deriv υ` the moments come from integration by parts, now available as

- `integral_deriv_eq_zero_of_hasCompactSupport`: `∫ deriv f = 0` for
  compactly supported `C¹` `f` (proved via the fundamental theorem of calculus
  on `[-R-1, R+1]`, Mathlib has no direct lemma);
- `integral_pow_mul_deriv_eq`: `∫ yⁱ · deriv f y = -i ∫ y^{i-1} · f y`;
- `deriv_eq_zero_of_vanishing`: the derivative vanishes wherever the function
  vanishes on a neighbourhood, which also gives the support statement for
  `deriv υ`.

## STRATEGIC — Littlewood–Paley may not be needed for the open range `q < 2p`

Re-examining the exponents in `brs_5_9` suggests a route to Proposition 5.4 on
the *interior* of the type region that bypasses the square-function theorem
entirely.  This matters because it also bypasses both structural mismatches
recorded above.

BRS factor the resolution as `Ψ_{k+m} = υ_{k+m} * ψ_{k+m}` so that the right
side of (5.9) carries `‖ψ_{k+m} * f₀‖_p`; the sum over `k` of those is then
handled by Littlewood–Paley, producing `sup_k ω_m^{p,q}(E,k) · ‖f₀‖_p`.

But the telescoping resolution already in this file needs no factorisation:
`δ = φ_k + ∑_{m ≥ 0} Ψ_{k+m}` with `Ψ_j = φ_{j+1} - φ_j` compactly supported and
carrying vanishing moments — exactly the bump `brs_5_9` wants.  Feeding `f₀`
itself (not `ψ_{k+m} * f₀`) to `brs_5_9` gives, per `(k, m)`,

```
2^{k(1/p - 2/q)} · 2^{-m(1/2 + 1/q - 1/p)} · N(E ∩ J, 2^{-k-m})^{1/q} · ‖f₀‖_p
```

and now the `k`-sum is geometric: `∑_k 2^{k(1/p - 2/q)} < ∞` exactly when
`1/p - 2/q < 0`, i.e. `q < 2p`.  So on the open range the `k`-aggregation costs
only a constant, and one obtains Proposition 5.4 with `∑_k ω_m^{p,q}(E,k)` in
place of `‖ω_m^{p,q}(E,k)‖_{ℓ^∞_k}` — a weaker but still finite bound, and
enough for an interior statement.  This mirrors how Theorem 1.1 was assembled
(`interior (Delta β) ⊆ radialTypeSetCont`), where every exponent inequality is
strict and no endpoint is needed.  Littlewood–Paley would then be required only
at `q = 2p`.

The shifted resolution is now available:

- `brsDilate_eq_add_sum_shift`: `φ_{k+M} = φ_k + ∑_{m < M} Ψ_{k+m}`;
- `brs_lp_resolution_shift`: the same tested against `g`;
- `brs_lp_resolution_shift_tendsto`: the partial sums converge to `g x`.

Together with `exists_brsBumpFull` (which supplies a bump meeting every
hypothesis of `brs_5_9_dilate`), the ingredients for the interior form of
Proposition 5.4 are all present; what remains is the bookkeeping that sums the
`(k, m)` estimates and identifies the result with `R₂^±`.

## Addendum — the `(k, m)` aggregate for Proposition 5.4

Three pieces, all with clean axioms:

- `lintegral_tsum_brsAmMax_rpow`: for a fixed `m` the windows `I_k` are disjoint
  (`brsAmMax_eq_zero_of_notMem`, `tsum_brsAmMax_rpow`), so the radial `L^q`
  norm of `∑_k 𝒜_{k,m}` is exactly the `ℓ^q` sum of the individual norms;
- `brs_5_4_shift_core s`: combining that with `lintegral_radial_Lp_tsum_le`
  (the `m`-summation of (5.10)) reduces the full double sum to the individual
  estimates (5.9), with the resolution based `s` scales below the truncation;
- `brs_5_4_aggregate`: feeding `brs_5_9_covering` into the above with `s = 3`
  bounds the whole `(k, m)` sum by the dyadic covering numbers of `E`.

**Why `s = 3`.**  `brs_5_9` needs `5 · 2^{-j} ≤ 2^{-k}`, i.e. the bump must be
at least three dyadic scales finer than the truncation.  Basing the resolution
at `k + 3` (legitimate: `brs_lp_resolution_shift` allows any base) makes
`j = k + m + 3` and the condition holds for every `m ≥ 0`; `brs_scale_gap`
records the arithmetic.  The low-frequency remainder becomes `φ_{k+3}` instead
of `φ_k`, which is harmless — it is still an `L¹`-normalised dilate at a scale
comparable to `2^{-k}`, so (5.8) applies to it unchanged.

**What remains for Proposition 5.4 on the open range.**  Two bookkeeping steps:

1. *Sum the geometric series.*  With `∑_k 2^{k(1/p - 2/q)}` convergent for
   `q < 2p` and `∑_m 2^{-m(1/2 + 1/q - 1/p)}` convergent for `1/2 + 1/q > 1/p`,
   the double sum in `brs_5_4_aggregate` is finite once the covering numbers
   are controlled, e.g. by an upper Minkowski or Assouad hypothesis on `E`.
   The two elementary geometric sums are the same shape as the one already done
   in `brs_5_8`.
2. *Identify the double sum with `R₂^±`.*  This is where
   `brs_lp_resolution_shift_tendsto` enters: the partial sums of
   `φ_{k+3} + ∑_m Ψ_{k+3+m}` converge to `g`, so the maximal function of `R₂^±`
   is dominated by the low-frequency term (5.8) plus the double sum above.

## Addendum — the geometric sums and the exponent bookkeeping

Two more building blocks for the interior form of Proposition 5.4:

- `tsum_ofReal_geometric`: `∑' k, ofReal (c · 2^{a k}) = ofReal (c / (1 - 2^a))`
  for `a < 0` (this generalises the inline computation used in `brs_5_8`);
- `tsum_tsum_ofReal_geometric_rpow`: the double sum with the inner one raised to
  `1/q`,
  `∑' m (∑' k ofReal (c · 2^{a k + b m}))^{1/q} = ofReal ((c/(1-2^a))^{1/q} / (1 - 2^{b/q}))`
  for `a < 0`, `b < 0`, `q > 0` — exactly the shape of `brs_5_4_aggregate`;
- `brs_term_exponent_identity`: collects the three dyadic factors of one term of
  `brs_5_4_aggregate` — the radial weight `(2^{-k})^{1-q/2}`, the covering number
  `2^{βj}` and the kernel gain `(2^{-j})^{sq}`, with `j = k + m + 3` — into a
  single power of two,
  `K₁ Cβ Cs 2^{3(β - sq)} · 2^{(q/2 - 1 + β - sq) k + (β - sq) m}`.
  The two exponents are named `brsSumExpK β s q` and `brsSumExpM β s q`.

With `s = 1/r - 1/2 = 1/2 + 1/q - 1/p` these read

```
brsSumExpK = β - 2 + q/p,       brsSumExpM = β - 1 - q/2 + q/p
```

so both are negative exactly when `q/p < 2 - β` and `q(1/p - 1/2) < 1 - β`.
For `β = 0` the first is `q < 2p` and the second is automatic when `p > 2`,
which is the expected range.

**Next step.**  Combine `brs_term_exponent_identity` with a covering-number
hypothesis `N(E, 2^{-j}) ≤ Cβ 2^{βj}` to put each term of `brs_5_4_aggregate`
into the form `ofReal (c · 2^{a k + b m}) · G^q`, then apply
`tsum_tsum_ofReal_geometric_rpow`.  That yields the interior form of
Proposition 5.4; the remaining step is to identify the double sum with `R₂^±`
through `brs_lp_resolution_shift_tendsto`.

## MILESTONE — `brs_5_4_interior`

The interior form of the main estimate behind Proposition 5.4 is proved, with
clean axioms and **without** the Littlewood–Paley theorem:

```
(∫⁻ x, (∑' m, ∑' k, brsAmMax k (k + (m+3)) υ g E x)^q * ofReal x)^(1/q)
  ≤ ofReal ( ((K₁ Cβ Cs^q 2^{3 b}) / (1 - 2^a))^{1/q} / (1 - 2^{b/q}) )
      * (∫⁻ ‖g‖ₑ^p)^{1/p}
```

with `a = brsSumExpK β s q`, `b = brsSumExpM β s q`, `s = 1/r - 1/2`, and
`Cs = C^{1/r} + C'^{1/r}` built from the two kernel constants.  The hypotheses
are: `E ⊆ [1,2]`; a covering bound `N(E, 2^{-j}) ≤ Cβ 2^{βj}`; the bump package
(supplied by `exists_brsBumpFull`); Young's relation `1/p + 1/r = 1 + 1/q` with
`1 ≤ p`, `1 < r < q`, `p < q`; and the two strict inequalities `a < 0`, `b < 0`,
which unwind to

```
q/p < 2 - β        and        q (1/p - 1/2) < 1 - β .
```

The proof chain is `brs_5_4_aggregate` → `brs_5_4_term_le` (one term, via
`brs_term_exponent_identity` and the covering bound) →
`tsum_tsum_ofReal_geometric_rpow`.

**What the Proposition 5.4 row still needs.**  `brs_5_4_interior` covers the
near part `𝒜`; the row is about `R₂^±` in full, so it also needs

1. the far part `ℬ` — `prop56_brsBFarLeft` and its mirror, already proved for
   `q < 2p`;
2. the low-frequency part — `brs_5_8`, already proved (it applies to `φ_{k+3}`
   unchanged, since that is still an `L¹`-normalised dilate at a scale
   comparable to `2^{-k}`);
3. the identification of `R₂^±` with the sum of the three, which is where
   `brsRemTwoTwoLeft_le_add` (the (5.5) split) and
   `brs_lp_resolution_shift_tendsto` (the resolution at base `k + 3`) come in.

## Addendum — the near part is a convolution

`integral_nearPart_eq_conv`: for `0 < c` and `a + c ≤ b`,

```
∫ s in a..b, 1_{Iio (a+c)}(s) · |s - a|^{-1/2} · g s
  = ∫ u : ℝ, brsTruncKernelAt c u · g (a + u)
```

where `brsTruncKernelAt c = 1_{Ioc 0 c} · (·)^{-1/2}` is the truncated kernel at
an arbitrary scale (`brsTruncKernel k = brsTruncKernelAt (2^{-k})` definitionally,
recorded as `brsTruncKernel_eq_at`).  The proof translates by `a`
(`intervalIntegral.integral_comp_add_left`), notes that the two integrands agree
off the single point `u = c` — the `Iio`/`Ioc` mismatch at the cutoff, a null
set — and extends to the line because the kernel vanishes outside `Ioc 0 c`.

**Two scale mismatches remain between this and `brsANearLeft`,** and both need a
decision before the identification can be completed:

1. *Reflection.*  `brsANearLeft` integrates `g (a + u)` while the kernel
   estimates are stated for `g (x - y)`; these differ by `y = -u`, so either the
   kernel has to be reflected onto the negative axis or the estimates restated.
2. *`r`-dependent cutoff.*  The split in (5.5) uses `brsCutScale r = r / 2048`,
   which varies with `r` inside the window `I_k` (it lies between `2^{-k-12}`
   and `2^{-k-11}`), whereas `brsTruncKernel k` has the fixed cutoff `2^{-k}`.
   Domination alone does not transfer, since `‖∫ ...‖` is not monotone in the
   cutoff; the clean fix is to restate the three-window kernel analysis for
   `brsTruncKernelAt c` with `c` a parameter, which is a mechanical but
   file-wide edit of `lintegral_enorm_brsTruncConv_rpow_le_scale` and its
   supporting lemmas.

## Addendum — arbitrary cutoff, and the reflection

Both scale mismatches flagged in the previous addendum now have their
infrastructure in place.

**Arbitrary cutoff.**  `brsANearLeftAt c` and `brsBFarLeftAt c` are the near and
far parts with the cutoff as a parameter; `brsANearLeft_eq_at` and
`brsBFarLeft_eq_at` say the originals are the case `c = brsCutScale r` (by
`rfl`), and `brsRemTwoTwoLeft_le_add_at` is (5.5) for any `c` — the split is
generic in the cutoff.  Taking `c` constant on each dyadic window `I_k` (e.g.
`c = 2^{-k-11}`) is what lets the near part be compared with the fixed-scale
truncated kernel, avoiding a rewrite of the whole (5.11)–(5.9) chain with a
parametrised cutoff.

**Reflection.**  `integral_nearPart_eq_conv` produces `∫ u, K u · g (a + u)`,
which is a convolution evaluated at `-a` after reflecting `g`; the maximal
function is then a supremum of `‖F (r - t)‖`, not `‖F (t - r)‖`.  Rather than
reflecting the kernel — which would require redoing the three-window analysis —
apply the maximal estimate to the reflected function:

- `lintegral_enorm_comp_neg`: `∫⁻ ‖H (-z)‖ₑ^q = ∫⁻ ‖H z‖ₑ^q`, so reflection
  costs nothing in any `L^q` norm;
- `hasDerivAt_comp_neg`: `(F ∘ neg)' (z) = -(F' (-z))`;
- `lintegral_iSup_translate_le_of_bounds`: the localized maximal estimate for
  an *abstract* differentiable pair `(F, F')` with `L^q` bounds `B`, `B'` —
  this is the form that accepts the reflected pair, whereas `brs_5_9_core` is
  tied to the specific convolution.

## Addendum — the near part, identified

`brsANearLeftAt_eq`: for `0 < c ≤ r` and continuous `g`,

```
brsANearLeftAt c E g r
  = ofReal (r^{-1/2}) * ⨆ t ∈ E ∩ Ici (3r/2), ‖brsRefl F (t - r)‖ₑ
```

where `brsRefl g z = g (-z)` and

```
F z = ∫ y, brsTruncKernelAt c y · brsRefl g (z - y)
```

is the convolution of the truncated kernel with the reflected input.  So the
near part *is* the weight `r^{-1/2}` times a localized maximal function of the
shape `⨆ t ∈ E, ‖(·) (t - r)‖ₑ` — exactly the shape
`lintegral_iSup_translate_le_of_bounds` accepts.

The proof chains `integral_nearPart_eq_conv` (translation `s = a + u`) with the
reflection identity `g (a + u) = brsRefl g (-a - u)`, then pulls the constant
weight out of the supremum with `ENNReal.mul_iSup`.

**What is left to close the Proposition 5.4 row.**

1. `‖brsRefl F‖_q = ‖F‖_q` and the same for the derivative
   (`lintegral_enorm_comp_neg`, `hasDerivAt_comp_neg`), so the abstract maximal
   estimate applies to `brsRefl F`.
2. Bound `‖F‖_q` and `‖F'‖_q` by Young against `‖brsTruncKernelAt c‖_r` — for
   `c = 2^{-k-11}` this is the kernel bound already proved, since
   `brsTruncKernelAt (2^{-j}) = brsTruncKernel j`.
3. Sum over the windows `I_k` (disjoint, as in `brs_5_8` / `lintegral_tsum_brsAmMax_rpow`)
   and over `m`, which is `brs_5_4_interior`.
4. Add the far part (`prop56_brsBFarLeft`, `q < 2p`) and the low-frequency part
   (`brs_5_8`) to get `R₂^±` via `brsRemTwoTwoLeft_le_add_at`.

## Addendum — reflection handled; the remaining analytic step

`lintegral_iSup_translate_refl_le` is the localized maximal estimate applied to
`brsRefl F`: reflection costs nothing, since `lintegral_enorm_comp_neg` gives
`‖brsRefl F‖_q = ‖F‖_q` and `hasDerivAt_comp_neg` gives the derivative
`z ↦ -(F' (-z))`, whose `L^q` norm is again `‖F'‖_q`.  Combined with
`brsANearLeftAt_eq` this reduces the near part to the two `L^q` bounds on `F`
and `F'`.

**The one analytic step still missing.**  `F = K_c ⋆ ǧ` is not differentiable
(the truncated kernel `K_c` is not smooth), so the maximal estimate cannot be
applied to `F` directly — it has to be applied to the pieces of the resolution,
whose kernels `K_c * Ψ_j` are smooth.  That needs

```
((K_c * Ψ_j) ⋆ h) (x) = (K_c ⋆ (Ψ_j ⋆ h)) (x)
```

(associativity, provable by Fubini with the substitution `z ↦ z + y`; Mathlib's
`convolution_assoc` also applies but carries three bilinear maps and several
integrability side conditions), together with the passage to the limit

```
(K_c ⋆ h) (x) = lim_M (K_c ⋆ (φ_{k+M} ⋆ h)) (x)
```

by dominated convergence.  The latter needs `h` bounded — harmless in the
continuous-profile setting the rest of this file uses, but it must be carried as
a hypothesis.  Once these two are in place the chain

`brsANearLeftAt_eq` → `lintegral_iSup_translate_refl_le` → Young →
`brs_5_4_interior`

closes the near part, and adding `prop56_brsBFarLeft` and `brs_5_8` through
`brsRemTwoTwoLeft_le_add_at` closes the Proposition 5.4 row.

## Addendum — the convolution-existence side conditions

`integrable_mul_shift_of_bounded` and `integrable_mul_shift_of_bounded'`:
an `L¹` function against a bounded (continuous, resp. measurable) one is
integrable after an arbitrary shift.  Every convolution appearing in the
associativity step is of this shape, so these discharge the three side
conditions of Mathlib's `convolution_assoc`:

- `hfg`: `h_k ⋆ Ψ` exists — `h_k ∈ L¹` (`integrable_brsTruncKernel`), `Ψ` bounded;
- `hgk`: `|Ψ| ⋆ |h|` exists — `Ψ ∈ L¹`, `h` bounded;
- `hfgk`: `|h_k| ⋆ (|Ψ| ⋆ |h|)` exists — `h_k ∈ L¹` and `|Ψ| ⋆ |h| ≤ ‖Ψ‖₁ · C`.

Instantiate `convolution_assoc` with `L = mul ℝ ℝ` and
`L₂ = L₃ = L₄ = lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ`; the compatibility hypothesis
`L₂ (L x y) z = L₃ x (L₄ y z)` is `mul_smul`.  Note
`brsTruncConvReal_eq_convolution` already identifies `brsTruncConvReal k Ψ` with
`Ψ ⋆[mul] h_k`, so `convolution_comm` supplies the remaining orientation.

## MILESTONE — associativity is proved

`brs_conv_assoc`:

```
((h_k ⋆[mul] Ψ) ⋆[lsmul] h) x = (h_k ⋆[lsmul] (Ψ ⋆[lsmul] h)) x
```

for `Ψ` continuous with compact support and `h` continuous and bounded, with
clean axioms.  This was the last structural gap for the near part: it is what
lets the resolution of the identity be applied to the (non-smooth) convolution
`h_k ⋆ h`, while each individual piece keeps the smooth kernel `h_k * Ψ_j`.

The proof instantiates Mathlib's `convolution_assoc` with `L = mul ℝ ℝ` and
`L₂ = L₃ = L₄ = lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ` (compatibility is `mul_smul`),
and discharges its three `ConvolutionExistsAt` hypotheses with
`integrable_mul_shift_of_bounded'`, using

- `integrable_brsTruncKernel` for `h_k ∈ L¹`;
- `Continuous.bounded_above_of_compact_support` for `Ψ` bounded;
- `convolution_norm_le_of_bounded` and `continuous_convolution_norm` for the
  third condition, which needs `‖Ψ‖ ⋆ ‖h‖` bounded (by `C ‖Ψ‖₁`) and
  continuous.

**Remaining for the near part.**  Only the assembly is left:

1. apply `brs_lp_resolution_shift_tendsto` to `F = h_k ⋆ ǧ` (continuous, since
   `h_k ∈ L¹` and `ǧ` is continuous and bounded) at base `k + 3`;
2. rewrite each piece `Ψ_j ⋆ F` as `(h_k * Ψ_j) ⋆ ǧ` by `brs_conv_assoc` and
   `convolution_comm`;
3. feed the resulting maximal functions into `lintegral_iSup_translate_refl_le`
   and then `brs_5_4_interior`.

## Addendum — associativity in the orientation the resolution produces

The resolution of the identity produces the pieces as `Ψ ⋆ (h_k ⋆ h)`, so the
associativity is needed with `Ψ` on the *outside*:

`brs_conv_assoc'`: `((Ψ ⋆[mul] h_k) ⋆[lsmul] h) x = (Ψ ⋆[lsmul] (h_k ⋆[lsmul] h)) x`.

Note the side conditions differ from `brs_conv_assoc`: with `Ψ` as the first
factor, the inner convolution pairs the *bounded* `Ψ` against the shifted `L¹`
kernel, which needs the new `integrable_bounded_mul_shift` (`h_k` is unbounded
near the origin, so `integrable_mul_shift_of_bounded'` does not apply in this
orientation).  The auxiliary `‖h_k‖ ⋆ ‖h‖` is again bounded by `C ‖h_k‖₁` and
continuous, this time by `BddAbove.continuous_convolution_right_of_integrable`
rather than the compact-support lemma, since `h_k` is not continuous.

Also new: `continuous_brsTruncKernel_convolution` — `h_k ⋆ h` is continuous for
bounded continuous `h`, again by
`BddAbove.continuous_convolution_right_of_integrable` — and
`brs_resolution_truncConv`, the resolution of the identity applied to it at base
`k + s`.

## Cycle note — the near part of `R₂^-`, reflected form

`brsANearLeftAt_le_pieces` bounds the near part (with the dyadic truncation
`2^{-k}`) by `r^{-1/2}` times the low-frequency piece at scale `k+s` plus the
sum of the high-frequency pieces, each carrying the smooth kernel `h_k * Ψ`.

The pieces come out in **reflected** form: the near-part integral is
`∫ h_k(u) g((t-r)+u) du`, i.e. `(ȟ_k ⋆ g)(t-r)`, whereas `brsAmMax` is built on
`(h_k ⋆ g)(t-r)`.  Reflecting the *function* rather than the kernel keeps the
kernel estimates intact, so the reflected family is
`brsNearFullMax k Ψ g E r = ⨆_{t∈E} ‖(ȟ_k * Ψ ⋆ g)(t-r)‖ₑ`, estimated by
`lintegral_brsNearFullMax_rpow_le` — the exact analogue of `brs_5_9_core`, using
`lintegral_iSup_translate_refl_le` in place of
`lintegral_iSup_enorm_translate_rpow_le`.  `brsNearMax` adds the window and the
radial weight, and `lintegral_window_weight_rpow_le` supplies the
`(2^{-k})^{1-q/2}` factor for an arbitrary maximal function.

Two gaps had to be filled:

* **Young `L¹ ∗ L^r ⊆ L^r`** (`lintegral_shift_mul_rpow_le`).  Mathlib's Young
  inequality needs strict exponent inequalities, so this endpoint case is
  proved from Hölder (splitting the weight as `w^{1/r} · w^{1-1/r}`) and
  Tonelli.  It is needed for the lowest-frequency piece `h_k * φ_{k+s}`, which
  carries no cancellation and so is outside the scope of (5.12).
* **Generic window aggregation** (`tsum_window_rpow`,
  `lintegral_tsum_window_rpow`, `window_double_sum_le`).  The `k`-aggregation
  only uses disjointness of the windows `I_k`; stating it for an arbitrary
  family lets the same argument serve both `𝒜_{k,m}` and the reflected pieces.

### Kernel bounds for the two kinds of piece

* High-frequency pieces `Ψ_j` have mean zero, so (5.12)
  (`lintegral_enorm_brsTruncConvReal_dilate_le`) applies with `N = 0`; the
  bracket is now isolated as `brs_5_9_bracket` and fed into `brs_5_9_near`.
* The lowest-frequency piece `φ_{k+s}` has `∫ φ = 1`, so (5.12) does not apply.
  `lintegral_enorm_brsTruncConvReal_dilate_le_L1` uses Young instead, giving
  `A · ‖h_k‖_r`; the derivative costs `2^j`, exactly cancelled by the `δ = 2^{-j}`
  in front of the derivative term (`brs_5_9_near_low`).  The resulting `2^{-k}`
  exponent is `(1/q - 1/2) + (1/r - 1/2) = 2/q - 1/p`, i.e. the `m = 0` term of
  `ω_m^{p,q}(E,k)`, summable in `k` under the same condition `q/p < 2 - β`.

### The window index and the truncation index must be kept apart

On `I_k = (2^{-k-1}, 2^{-k}]` the cutoff in the (5.5) split has to be at most
the radius, and `2^{-k} ≤ r` fails there.  So the truncation is taken at
`2^{-(k+1)}`, one dyadic scale finer than the window: `brsNearMax kw kt`
carries the window index `kw` and the truncation index `kt` separately, and the
near part on `I_k` uses `kw = k`, `kt = k + 1` (`brsCut_le_of_mem_window`).

### The family, and the aggregation

`brsNearFamily s φ g E m k` is the `(m, k)`-family: `m = 0` is the
lowest-frequency piece at scale `2^{-(k+1+s)}`, `m + 1` the Littlewood--Paley
piece at `2^{-(k+1+s+m)}`.  Every member vanishes off `I_k`, so
`window_double_sum_le` applies, giving `brsNear_aggregate`.  The pieces are all
dilates of a single bump: `brsLPKernel φ j = brsDilate (brsLPKernel φ 0) j`
(`brsLPKernel_eq_dilate`), and `exists_brsLPBumpPackage` supplies the (5.9)
hypotheses for `brsLPKernel φ 0` from any smooth unit-mass profile supported in
the unit ball (`exists_brsUnitBump`).  Only one vanishing moment is needed
(`N = 0`): the gain `(2^{-j})^{1/r - 1/2}` does not depend on `N`, which enters
only the constant `brsKernelConst`.

Mathlib note: `Summable.tsum_eq_zero_add` times out on `ℝ≥0∞` (unification
pathology); `tsum_eq_zero_add' ENNReal.summable` works and is wrapped as
`ennreal_tsum_eq_zero_add`.

### The near part is closed (`brs_near_interior`)

With `s = 3` the family offsets are `a = n + 4` for family index `n` (the
low-frequency piece at `n = 0` and the LP piece at `n = m + 1` both sit at
`j = k + (n + 3)` shifted by one), so the term estimate had to be restated with
the offset free: `brs_term_exponent_identity_gen` / `brs_term_le_gen` /
`brs_term_le_gen'`.  Since `brsSumExpM < 0`, replacing the true offset `a` by
the smaller family index `n` only increases the term
(`ofReal_geometric_offset_le`), so both kinds of term land on the common
geometric shape `c · 2^{ExpK·k + ExpM·n}` and
`tsum_tsum_ofReal_geometric_rpow` finishes the double sum exactly as in
`brs_5_4_interior`.

The low-frequency constant is put in dyadic form by `brsLowConst_rpow_inv`
(`brsLowConst kt r ^ (1/r) = (1 - r/2)^{-1/r} (2^{-kt})^{1/r - 1/2}`) and
`dyadic_shift_three_rpow`.

`brs_near_interior` is the near half of Proposition 5.4(i): the `L^q(r dr)`
norm of `∑_k 1_{I_k} 𝒜^{near}_k` is bounded by the geometric constant times
`‖g‖_p`, on the open range where both `brsSumExpK` and `brsSumExpM` are
negative.

### Proposition 5.4(i) for `R₂^-` is proved

Three things had to be arranged to add the two halves of (5.5):

1. **The windows must cover `(0, 4/3]`, not just `(0, 1]`.**  `R₂` vanishes for
   `r > 4/3` but the dyadic windows stop at `1`.  `brsWindowExt` enlarges the top
   window to `(1/2, 4/3]`; it is still comparable to `2^{-0} = 1`, so
   `rpow_le_of_mem_brsWindowExt` holds with the same constant, disjointness and
   `2^{-(k+1)} ≤ r` are unchanged, and the whole near-part chain went through
   verbatim after renaming.
2. **The far part must be available at the truncation cutoff `2^{-(k+1)}`, not
   `brsCutScale r = r/2048`.**  Only `0 < brsCutScale r ≤ c` is used in the
   proof of the pointwise far bound, so `brsBFarLeftAt_le` is the same argument
   at an arbitrary larger cutoff, and `brsCutScale_le_of_mem_windowExt` supplies
   the hypothesis on each window.
3. **Both halves must be measured against the same norm.**  Young's inequality
   gives the near part the plain `L^p` norm of the profile, so the far part is
   restated against that too (`brsBFarLeftAt_le'`, `prop56_brsBFarWindow'`); on
   the region that actually contributes, `s ≥ 1/3`, so the two norms are
   comparable once the profile's support is known.

Additivity of the integral needs a measurable summand, and the maximal functions
are indexed by a set depending on `r`, so they are not obviously measurable.
The fix is to integrate only the **measurable majorants**: the family
`∑'_m ∑'_k brsNearFamily` for the near part (`brs_near_interior_family`) and the
explicit indicator majorant for the far part.  The elementary convexity bound
`(a+b)^q ≤ 2^{q-1}(a^q+b^q)` replaces Minkowski, costing only a constant.

`prop54_brsRemTwoTwoLeft_interior` is the result.  `R₂^+` is the mirror image
and is the next item.

### `R₂^+`: the plan, and the far half

`R₂^+` is not the reflection of `R₂^-` in any naive sense — reflecting `s ↦ -s`
sends `E ⊆ [1,2]` to `[-2,-1]` and flips the constraint `t ≥ 3r/2`.  The right
map is `σ(x) = 3 - x`, which preserves `[1,2]`.

Computing the near part directly: substituting `u = t + r - s` turns
`∫_t^{t+r} 1_{|t+r-s|<c} |t+r-s|^{-1/2} g(s) ds` into `(h_c ⋆ g)(t+r)` — a
genuine convolution with `g` (no reflection), evaluated at `t + r`.  Writing
`t + r = 3 - (σt - r)` and `G(x) := (h_c ⋆ g)(3 - x)` gives
`⨆_{t∈E} ‖(h_c ⋆ g)(t+r)‖ₑ = ⨆_{t'∈σE} ‖G(t' - r)‖ₑ`, and `G` is exactly the
function inside `brsNearFullMax` for the profile `g̃ := g ∘ σ`.  So the whole
near chain applies verbatim with `E ↦ σE ⊆ [1,2]` and `g ↦ g̃`; `g̃` has the same
sup bound and the same `L^p` norm as `g`.  The constraint `t ≥ 3r/2` becomes
`t' ≤ 3 - 3r/2`, which is discarded when the supremum is enlarged to all of
`σE` — exactly as on the left.

The far half is done: `brsANearRightAt` / `brsBFarRightAt` (arbitrary cutoff),
`brsRemTwoTwoRight_le_add_at`, `brsBFarRightAt_eq_zero`, `brsBFarRightAt_le'`
(unweighted, any cutoff above `brsCutScale r`), `brsFarWindowSumRight` and
`prop56_brsBFarWindowRight'`.

### `R₂^+` is done, via the reflection `x ↦ 3 - x`

`integral_nearPartRight_eq_conv` (substituting `u = b - s`) puts the right near
part in the form `∫ h_c(u) g(t+r-u) du`, and `brsANearRightAt_eq` rewrites that
as the *left* reflected convolution evaluated at `3 - t - r`, for the reflected
profile `g̃ = g ∘ (3 - ·)`.  `image_three_sub_subset_Icc` keeps the index set
inside `[1,2]`, and `lintegral_enorm_comp_three_sub` says the reflection does
not change `‖g‖_p`.  So the whole near chain is reused verbatim with
`E ↦ 3 - E`, `g ↦ g̃`: `brsANearRightAt_le_pieces`,
`brsANearRightWindow_le_tsum(_family)`, then the same assembly as on the left.

`enorm_brsRefl_conv_le_pieces` was factored out of the left proof: it is the
decomposition of a *single* value of the smoothed near part into the pieces of
the resolution, and both halves of (5.5) use it.

`prop54_brsRemTwoTwoRight_interior` completes Proposition 5.4(i) for `R₂^±` on
the open range (both dyadic exponents negative).  The endpoint `q = 2p` remains
open, as for (5.6); the row records that.

### Proposition 5.4 in usable form; (i) and (ii) are one statement here

`exists_brsResolutionData` discharges the resolution of the identity once and
for all — the bump `φ` (`exists_brsUnitBump`), the mean-zero bump
`υ = brsLPKernel φ 0` with its package (`exists_brsLPBumpPackage`, `N = 0`), the
`L¹` constants, and a single `Cs` dominating both the low- and high-frequency
kernel constants.  That turns the twenty-odd bump hypotheses of
`prop54_brsRemTwoTwo{Left,Right}_interior` into nothing:
`prop54_brsRemTwoTwo{Left,Right}_of_exponents` takes only the exponents and the
covering estimate.

`brs_exponent_data` then eliminates `r`: it is `(1 + 1/q - 1/p)⁻¹`, and

* `1 < r`  ⟺ `p < q`,
* `r < q`  ⟺ `p > 1`,
* `r < 2`  ⟺ `1/p - 1/q < 1/2`   (intrinsic: `|u|^{-1/2} ∈ L^r_loc` iff `r < 2`),
* `brsSumExpK = β - 2 + q/p`,
* `brsSumExpM = β - 1 - q + q/p + q/2`.

So `prop54_brsRemTwoTwo{Left,Right}_pq` reads: for `1 < p < q < 2p` with
`1/p - 1/q < 1/2`, `q/p < 2 - β` and `q/p < 1 + q/2 - β`, `R₂^±` maps `L^p` to
`L^q(r dr)`.  Nothing in the argument distinguishes `q < 2` from `q ≥ 2`, so
this single statement covers both parts (i) and (ii) of Proposition 5.4 — the
`ℓ^{2q/(2-q)}` refinement the paper uses for `q < 2` is only needed at the
endpoint, which remains open in both rows.

## Proposition 5.5: the plan for `𝔐_p^±`

`𝔐_p^- E p g r = ⨆_{t ∈ E ∩ (r/2, 3r/2)} r^{-1} ‖∫_{|r-t|}^{r+t}
s^{1/2-1/p}(s-|r-t|)^{-1/2} g(s) ds‖`, so relative to `R₂^-`:

* the prefactor is `r^{-1}`, not `r^{-1/2}` — handled by
  `lintegral_window_weight_rpow_le_gen`, the window computation with the power
  left free (`r^e` costs `(2^{-k})^{eq+1}` on `I_k`);
* the profile carries the extra weight `s^{1/2-1/p}`, so the substitution
  `u = s - a` gives `(ȟ_c ⋆ G)(a)` with `G(s) = s^{1/2-1/p} g(s)`;
* the singular point is `a = |r - t|`, not `t - r`.  Splitting the window at
  `t = r` puts each half into a shape the existing machinery already handles:
  on `t ≤ r`, `a = r - t` gives `⨆_t ‖brsRefl F (t-r)‖ₑ` — literally
  `brsNearFullMax`; on `t > r`, `a = t - r` gives the unreflected shape, which
  the `x ↦ 3 - x` trick of `R₂^+` converts.

The two singularities `s^{1/2-1/p}` and `(s-a)^{-1/2}` collide when `a = 0`
(i.e. `t = r`); their product is then exactly `s^{-1/p}`, still integrable for
`p > 1`.  `intervalIntegrable_mainWeight_complex` covers both cases and is what
the near/far split of `𝔐_p^±` will rest on.

### Proposition 5.5: the radius is compact, so there is no `k`-sum

A crude far-part bound for `𝔐_p^-` gives `r^{-1}·r^{1/2-1/p}·c^{-1/2}·|W|^{1-1/p}
≈ r^{-2/p}`, and `∫ (r^{-2/p})^q r dr` converges at the origin only for `q < p`
— useless, since Proposition 5.5 is about `p ≤ q`.  That is not a defect of the
estimate: `𝔐_p^±` only sees dilations comparable to the radius, so with
`E ⊆ [1,2]` the constraint `t ∈ (r/2, 3r/2)` forces `r ∈ (2/3, 4)`
(`brsMainWindow_empty`, `brsMainTwoLeft_eq_zero`, and the same for the near/far
pieces and for `𝔐_p^+`).  There is no small-radius divergence to control and
**no dyadic decomposition of the radius at all** — unlike `R₂^±`, where the
`k`-sum was the whole difficulty.

So the architecture of Proposition 5.5 is the `R₂` one with the `k`-sum
deleted: substituting `u = s - a` writes the operator as
`⨆_{t} ‖(ȟ_c ⋆ G)(a)‖` with `G(s) = s^{1/2-1/p} g(s)` and `a = |r - t|`;
splitting the window at `t = r` puts each half into the `brsNearFullMax` shape;
the resolution of the identity contributes `(2^{-m})^{1/r' - 1/2}` per piece
against `N(E, 2^{-m})^{1/q} ≲ 2^{βm/q}`, and the single geometric series in `m`
converges exactly when `β < q/2 + 1 - q/p`, i.e. when `brsSumExpM < 0`.  No
`brsSumExpK` condition appears, because there is no `k`-sum.

### The main term's near part, identified

`integral_mainNearPart_eq_conv` (and its right-endpoint twin) is the analogue of
`integral_nearPart_eq_conv` with the extra weight `s^e` left free: the near part
of `𝔐_p^±` is the truncated kernel against `s ↦ s^e g(s)`.  Keeping `e` free
matters — the natural profile in the application is the *substituted* one, for
which `brsMainTwoLeft_integrand` turns `s^{1/2-1/p}·(substituted profile)` into
`s^{1/2}·f₀`, and only that version has a continuous, bounded weighted profile
(`s^{1/2-1/p}` alone is singular at the origin when `p < 2`, and the origin is
attained: `a = |r-t| = 0` at `t = r`, which is inside the window).

`brsWeightedProfile e g z = z^e · g z` absorbs the weight, and
`brsMainNearLeftAt_eq` then reads exactly like `brsANearLeftAt_eq`:

    𝔐-near = ofReal r⁻¹ · ⨆_{t ∈ E ∩ (r/2, 3r/2)}
               ‖brsRefl (h_c ⋆ (brsWeightedProfile e g)ˇ) |r - t|‖ₑ

so the resolution machinery applies once the window is split at `t = r`:
`|r - t| = r - t` gives the `brsNearFullMax` shape handled by
`lintegral_iSup_translate_refl_le`, and `|r - t| = t - r` gives the unreflected
shape handled by `lintegral_iSup_enorm_translate_rpow_le`.  Both already exist.

### The main term's near part is decomposed; the truncation index is fixed

Because the radius is confined to `(2/3, 4)`, the cutoff can be taken to be the
single scale `2^{-1} = 1/2` — it satisfies `c ≤ r` for every admissible `r`, and
`brsTruncKernelAt (2^{-1}) = brsTruncKernel 1` definitionally.  So the existing
decomposition lemmas apply with the truncation index frozen at `k = 1`, and no
`k`-sum ever appears.

`iSup_abs_translate_le` splits the window at `t = r`:

    ⨆_{t∈S} ‖brsRefl F |r-t|‖ₑ ≤ (⨆_{t∈E} ‖F (t-r)‖ₑ) + ⨆_{t∈E} ‖brsRefl F (t-r)‖ₑ

`enorm_conv_le_pieces` is the unreflected form of
`enorm_brsRefl_conv_le_pieces`, obtained by evaluating it at `-a`.  Together
they give `brsMainNearLeftAt_le_pieces`: the near part of `𝔐_p^-` at cutoff
`1/2` is bounded by `ofReal r⁻¹` times two copies of (low-frequency piece plus
`∑'_m` high-frequency pieces) — one copy in the `brsMainMaxU` (unreflected)
family, one in the `brsNearFullMax` (reflected) family.  Both families already
have localized maximal estimates: `brs_5_9_dilate` for the first (with profile
`Ǧ`) and `lintegral_brsNearFullMax_rpow_le` for the second.

### The main term's radial weight, and the single family

`lintegral_main_weight_le`: on `(2/3, 4)` the weight `(r^{-1})^q · r` is bounded
by `(3/2)^q · 4`, so the whole radial bookkeeping for `𝔐_p^±` is one constant —
compare the dyadic `lintegral_window_weight_rpow_le` needed for `R₂^±`.
`brsMainNearLeftAt_le_indicator` puts the radial cutoff into the statement, and
`lintegral_brsMainNearLeftAt_rpow_le` is the resulting `L^q(r dr)` bound.

`brsMainFamily` collects the four families (unreflected/reflected ×
low-frequency/Littlewood--Paley) into a single sequence: index `0` is the
unreflected low piece, `1` the reflected low piece, and `m + 2` the sum of the
two `m`-th Littlewood--Paley pieces.  `brsMainFamily_tsum` is the identity that
lets the whole near part be written as `∑'_n brsMainFamily … n r`, ready for the
countable Minkowski inequality `lintegral_Lp_tsum_le` and then the per-piece
estimates (`brs_5_9_dilate` for the unreflected family with profile `Ǧ`,
`lintegral_brsNearFullMax_rpow_le` for the reflected one).

### The main term's pieces are now reduced to existing maximal estimates

`measurable_brsMainMaxU` / `measurable_brsMainFamily` supply what the countable
Minkowski inequality needs, and `lintegral_brsMainNear_Lp_le` is the result: the
`L^q(r dr)` norm of the near part of `𝔐_p^-` is at most
`((3/2)^q · 4)^{1/q}` times `∑'_n (∫⁻ (brsMainFamily … n)^q)^{1/q}`.

Each term of that sum is already covered:

* `lintegral_brsMainMaxU_rpow_le` — the unreflected family.  `brsMainMaxU` is
  literally `brs_5_9_core`'s maximal function with the profile reflected, and
  reflecting does not change the `L^p` norm (`lintegral_enorm_comp_neg`), so the
  same bracket comes out.
* `lintegral_brsNearFullMax_rpow_le` — the reflected family, unchanged from the
  `R₂` work.

What remains for Proposition 5.5 is arithmetic that has all been done once
before for `R₂`: substitute the kernel bounds ((5.12) for the Littlewood--Paley
pieces, Young for the low-frequency one), replace `ι.card` by
`N(E, 2^{-m})`, and sum the single geometric series in `m` — convergent exactly
when `brsSumExpM < 0`.

### The low-frequency bracket, extracted

`brs_low_bracket` is the counterpart of `brs_5_9_bracket` for the piece with no
cancellation: the two Young bounds
(`lintegral_enorm_brsTruncConvReal_dilate_le_L1` and its derivative version)
combine to `(A + A') · brsLowConst k r ^{1/r}`, the `2^j` from differentiating
the dilate being cancelled by the `δ = 2^{-j}` in front of the derivative term.
It was previously inlined in `brs_5_9_near_low`; the main term needs it too.

With it, `lintegral_brsMainFamily_zero_le` and `lintegral_brsMainFamily_one_le`
bound the two low-frequency pieces of `𝔐_p^-` (unreflected and reflected) by
`ι.card · ((A+A')·brsLowConst 1 r^{1/r} · ‖G‖_p)^q`, at cover scale
`2^{-(1+s)}`.  `brsDilate_deriv_data` packages the four smoothness facts about a
dilated profile that both of them need.

Remaining for Proposition 5.5: the same bound for the index-`m+2` pieces (via
`brs_5_9_bracket` with `k = 1`, `j = 1+s+m`, whose scale gap `5·2^{-(1+s+m)} ≤
2^{-1}` holds for every `m` once `s = 3`), then replacing `ι.card` by
`N(E, 2^{-j})` and summing the geometric series in `m`.

### All three kinds of main-term piece are now bounded

`lintegral_brsMainFamily_succ_succ_le` handles index `m + 2`, which is the
*sum* of the two `m`-th Littlewood--Paley pieces, so the convexity bound
`(a+b)^q ≤ 2^{q-1}(a^q+b^q)` costs a factor `2^q` (the `2^{q-1}·2 = 2^q` step is
`ennreal_rpow_sub_one_mul`).  Both summands go through `brs_5_9_bracket` with
`k = 1`, `j = 1+3+m`; the scale gap `5·2^{-(1+3+m)} ≤ 2^{-1}` is `brs_scale_gap
1 m` after `1 + (m+3) = 1+3+m`.

So with `s = 3` every term of `∑'_n (∫⁻ (brsMainFamily 3 φ e g E n)^q)^{1/q}` is
bounded:

* `n = 0, 1` by `lintegral_brsMainFamily_{zero,one}_le` at cover scale `2^{-4}`;
* `n = m+2` by `lintegral_brsMainFamily_succ_succ_le` at cover scale
  `2^{-(4+m)}`, with the dyadic gain `(2^{-(4+m)})^{1/r - 1/2}`.

What is left is to replace `ι.card` by `N(E, 2^{-(4+m)}) ≤ Cβ 2^{β(4+m)}` and
sum `∑_m 2^{βm/q} 2^{-m(1/r - 1/2)}`, a single geometric series, convergent iff
`β/q < 1/r - 1/2`, i.e. iff `brsSumExpM < 0`.

### The main-term pieces, with covering numbers and in geometric form

`lintegral_brsMainFamily_{zero,one,succ_succ}_covering` replace `ι.card` by
`intervalCoveringNumber E (2^{-j})` (minimal cover, `hE : E ⊆ [1,2]`).

`brsMain_geometric_term` is the arithmetic that turns one such term into a
single dyadic power: for `N(E,2^{-j}) ≤ Cβ 2^{βj}`,

    (N(E,2^{-j}) · (ofReal (C·(2^{-j})^s) · G)^q)^{1/q}
      ≤ ofReal (Cβ^{1/q} · C · 2^{(β/q − s)·j}) · G

so the ratio of consecutive terms is `2^{β/q − s}`, and with `s = 1/r − 1/2`
that exponent is `brsSumExpM β s q / q`.  The `m`-sum is therefore geometric
with ratio `< 1` exactly when `brsSumExpM < 0`, and `tsum_ofReal_geometric`
evaluates it.

### The near half of Proposition 5.5 is proved

`tsum_geometric_shift` evaluates `∑'_m ofReal(c · 2^{a(d+m)})` as
`ofReal(c · 2^{ad} / (1 - 2^a))` for `a < 0`, and
`brsMainFamily_{zero,one,succ_succ}_term_le` put the three kinds of term into
that form.  `brsMainFamily_tsum_le` adds them:

    ∑'_n (∫⁻ (brsMainFamily 3 φ e g E n)^q)^{1/q}
      ≤ (K + K + c·2^{4a}/(1-2^a)) · ‖G‖_p

with `a = β/q - (1/r - 1/2) = brsSumExpM β (1/r-1/2) q / q`, so the hypothesis is
exactly `brsSumExpM < 0`, as predicted — and no `brsSumExpK` condition appears.

`lintegral_brsMainNearLeftAt_final` composes that with
`lintegral_brsMainNear_Lp_le`, giving the near half of Proposition 5.5 for
`𝔐_p^-`.  What remains for the row: the far part `brsMainFarLeftAt`, and the
right-endpoint versions.

### The far part of `𝔐_p^-` is bounded

`enorm_mainWeight_eq` is the observation that makes the far part easy: the
integrand of `𝔐_p^-` is `(s-a)^{-1/2}` against `G = brsWeightedProfile e g`
*exactly* — the weight `s^{1/2-1/p}` is not an extra factor to estimate, it is
the definition of `G`.  So `brsMainFarLeftAt_le` is a plain Hölder estimate:
`(s-a)^{-1/2} ≤ c^{-1/2}` on the far region, `|W| ≤ b - a ≤ 8`, and `r⁻¹ ≤ 3/2`.

`lintegral_brsMainFarLeftAt_le` then integrates: the bound is uniform in `r` and
the far part vanishes off `(2/3, 4)`, so the radial integral contributes only
the constant `16`.

To finish Proposition 5.5 for `𝔐_p^-` the two halves must be added.  The
maximal functions are again not obviously measurable (the index set depends on
`r`), so the same device as for `R₂^±` applies: integrate the measurable
majorants — `(Ioo (2/3) 4).indicator (r ↦ r⁻¹ · ∑'_n brsMainFamily … n r)` for
the near half and `(Ioo (2/3) 4).indicator (const)` for the far half — and feed
them to `lintegral_rpow_le_of_two_bounds`.

### `𝔐_p^-` is split into two measurable majorants

`brsMainNearMaj` and `brsMainFarMaj` are the two majorants, both supported on
`(2/3, 4)` and both manifestly measurable.  `brsMainTwoLeft_le_maj` is the
pointwise domination (using `brsMainTwoLeft_le_add_at` at the fixed cutoff
`2^{-1}` inside the window, and `brsMainTwoLeft_eq_zero` outside), and
`brsMainTwoLeft_rpow_le` adds the convexity factor, in exactly the shape
`lintegral_rpow_le_of_two_bounds` consumes.

Their `L^q(r dr)` bounds are `lintegral_brsMainNearMaj_Lp_le` (weight constant,
then countable Minkowski, then `brsMainFamily_tsum_le`) and
`lintegral_brsMainFarMaj_le` (a constant on a bounded window, via
`lintegral_indicator_const_weight_le`).  Assembling these three with
`lintegral_rpow_le_of_two_bounds` gives Proposition 5.5 for `𝔐_p^-`; the
remaining work is folding the constants into a single `ENNReal.ofReal`.

### Proposition 5.5 for `𝔐_p^-` is proved

`lintegral_rpow_le_of_two_bounds'` is the two-majorant lemma with the constants
left in `ℝ≥0∞` — the real-valued version forced `ENNReal.ofReal` juggling that
buys nothing here.  With it, `prop55_brsMainTwoLeft` follows from the three
inputs already in place: the pointwise split `brsMainTwoLeft_rpow_le`, the near
bound `lintegral_brsMainNearMaj_Lp_le` ∘ `brsMainFamily_tsum_le`, and the far
bound `lintegral_brsMainFarMaj_le`.

The constant is exhibited explicitly and shown finite, which is the usable
content; its exact value is
`2^{(q-1)/q} · (C₁·(K + K + C_geo) + 16^{1/q}·C_far)`.

Remaining for the row: the right-endpoint operator `𝔐_p^+`, which should follow
the `R₂^+` pattern (the reflection `x ↦ 3 - x` preserves `[1,2]` and the window
`(r/2, 3r/2)` is symmetric about `r`, so the substitution `u = b - s` of
`integral_mainNearPartRight_eq_conv` puts it in the same shape).

### `𝔐_p^+`: the near part is simpler than the left one

`brsMainNearRightAt_eq`: substituting `u = b - s` gives the *plain* convolution
evaluated at `b = r + t`; writing `r + t = -((3-t) - r) + 3` and reflecting the
profile about `3/2` turns it into the left-endpoint shape with index set
`3 - E ⊆ [1,2]` and profile `w ↦ G(3 - w)`.

Notably the singular point is now *always* `3 - t - r`, with no absolute value,
so there is **no window split at `t = r`** — only the reflected family occurs.
`brsMainNearRightAt_le_pieces` therefore has half as many terms as
`brsMainNearLeftAt_le_pieces`, and no `brsMainMaxU` family appears.

### The right-endpoint family

`brsMainFamilyR` is the family for `𝔐_p^+`: since no window split occurs there,
it is a single sequence — index `0` the low-frequency piece, `m + 1` the `m`-th
Littlewood--Paley piece — and the profile is left as a free function `H`,
because at the right endpoint it is the *reflection* `w ↦ G(3 - w)` of the
weighted profile rather than a weighted profile itself.

(That is why `brsMainFamily` could not simply be reused: it hard-codes
`brsWeightedProfile e g`, and `w ↦ G(3-w)` is not of that form for any natural
`g`.  Generalising `brsMainFamily` over the profile would have meant editing a
dozen already-proved lemmas; the two-case family is shorter than that refactor
would be, since the right endpoint needs only the reflected half.)

`brsMainNearRightAt_le_tsum` puts the near part of `𝔐_p^+` in the form
`ofReal r⁻¹ · ∑'_n brsMainFamilyR …`, ready for the same weight-then-Minkowski
chain used on the left.

### The right-endpoint sum is done

`lintegral_brsMainFamilyR_{zero,succ}_le`, their covering versions, and
`brsMainFamilyR_tsum_le` mirror the left-endpoint chain with one family instead
of four — and with no convexity factor, since the index-`m+1` term is a single
maximal function rather than a sum of two.  The geometric ratio is again
`2^{β/q - (1/r - 1/2)}`, so the same hypothesis `brsSumExpM < 0` governs both
endpoints.

What remains for the row: the majorants for `𝔐_p^+` (`brsMainNearMajR`,
reusing `brsMainFarMaj` with the right-endpoint constant), the pointwise split,
and `prop55_brsMainTwoRight` — each a direct copy of the left-endpoint version.

### Proposition 5.5 is complete

`prop55_brsMainTwoLeft` and `prop55_brsMainTwoRight` both hold, so the row is
done.  The hypothesis is `β/q < 1/r - 1/2`, i.e. `β < q/2 + 1 - q/p`, which is
exactly "below the critical exponent"; equality is the critical case and is not
covered, as the row's wording anticipates.

The two proofs are structurally identical, but the right endpoint is shorter:
no window split at `t = r` means one piece family instead of four, and no
convexity factor in the Littlewood--Paley terms.  The far halves are the same
Hölder estimate at opposite endpoints, and `lintegral_enorm_comp_three_sub`
reconciles the two `L^p` norms (`w ↦ G(3-w)` versus `G`).

Next row: Proposition 5.6, the endpoint bound for `𝔐_p^±` via `ν♯`.

## Proposition 5.6: the endpoint, via `ν♯`

The row is now in progress.  The situation: at the critical exponent the
geometric series in `m` that proves Proposition 5.5 diverges logarithmically,
because the Minkowski bound `N(E, 2^{-m}) ≲ 2^{βm}` is exactly borderline.  BRS
recover the endpoint by using the *localized* Assouad-spectrum bound (2.2)
instead — `N(E ∩ J, δ) ≲ (|J|/δ)^{σ(θ)}` whenever `δ^θ ≤ |J|` — and optimizing
over `θ`, which is what produces the Legendre transform `ν♯`
(`brrsLegendreAssouadFunction`, with its two-sided bounds already proved as
`lemma21_brs`).

The combinatorial step that makes a *local* bound usable globally is the
two-scale inequality

    N(E, δ) ≤ ∑_{a ∈ ι} N(E ∩ [a - Δ/2, a + Δ/2], δ)   for any Δ-cover ι of E

(`intervalCoveringNumber_le_sum`): refine each coarse interval separately and
take the union of the fine covers.  Combined with (2.2) at `Δ = δ^θ` this gives
`N(E, δ) ≲ N(E, δ^θ) · δ^{-(1-θ)σ(θ)}`, the sub-multiplicativity whose
optimization over `θ` is the Legendre transform.

Already available for this row: `brsOmegaTwo` (the localized quantity (5.2)) and
its comparison with the global covering number, the three covering bounds
(2.1)-(2.3), and `lemma21_brs`.

## Addendum (2026-09-06): §5 checked against the arXiv source — there is no Proposition 5.6

The HTML source of arXiv:2412.09390v2 was downloaded and read directly.  §5 of
BRS contains exactly:

* **Lemma 5.1** — the pointwise reduction
  `M_E f(x) ≲ 𝔐_p^+ g(r) + 𝔐_p^- g(r) + Σ_± Σ_{i=1,2} R_i^± f₀(r)`,
  with `g(s) = f₀(s) s^{1/p}`;
* **Proposition 5.2** — the `R_1^±` bounds;
* **Lemma 5.3** — `‖R_2^± f‖_{L^p(r dr)} ≤ Σ_{m≥0} N(E,2^{-m})^{1/p} 2^{-m/2} ‖f‖_{L^p(s ds)}`;
* **Proposition 5.4 (i), (ii)** — the `R_2^±` bounds, in terms of the
  *localized* quantity
  `ω_m^{p,q}(E,k) := sup_{|J| = 2^{-k}} 2^{-k(2/q - 1/p)} N(E ∩ J, 2^{-m-k})^{1/q}`
  (BRS (5.2)), with `‖·‖_{ℓ^∞_k}` for `2 ≤ q ≤ 2p` (5.3) and
  `‖·‖_{ℓ^{2q/(2-q)}_k}` for `1 < q < 2` (5.4);
* **Proposition 5.5 (i), (ii), (iii)** — the `𝔐_p^±` bounds, see below.

There is **no Proposition 5.6**.  The Status row that named one was a phantom;
the repo's `prop56_*` lemmas are named after *equation* (5.6), not a
proposition, which is what created the confusion.  The row has been retitled to
the real remaining item.

**`ν♯` enters through Proposition 5.4, not through `𝔐_p^±`.**  It is the
exponential rate of `sup_{δ ≤ |J| ≤ 1} |J|^{-α} N(E ∩ J, δ)` (BRS (1.2)), so it
needs *both* scales — the interval length `2^{-k}` and the fine scale
`2^{-m-k}`.  The `𝔐_p^±` estimate has no `k`-sum at all (the constraint
`t ∈ E ⊆ [1,2]` with `r/2 < t < 3r/2` confines `r` to `(2/3,4)`), so `ν♯` cannot
arise there.  Theorem 1.2 reads

    𝒯^rad_E (closure) = Δ_β ∩ {(1/p,1/q) : (1/q)·ν♯(q/2 - 1) + 1/p - 1/q ≤ 1/2},

and the `ν♯` half of that constraint comes from Proposition 5.4 (i) via
`ω_m^{p,q}`.  Any further work on the `ν♯` side belongs to rows 87/88, not to
the `𝔐_p^±` rows.

### Proposition 5.5, verbatim

Let `E ⊆ [1,2]` and `1 ≤ p ≤ q < ∞`.

* (i) for `p > 2`:   `‖𝔐_p^± g‖_{L^q(r dr)} ≲ ‖g‖_p`;
* (ii) for `p < 2`:  `‖𝔐_p^± g‖_{L^q(r dr)} ≲_p sup_{0<δ<1} N(E,δ)^{1/q} δ^{1 - 2/p + 1/q} ‖g‖_p`  (5.15);
* (iii) for `p = 2`: `‖𝔐_p^± g‖_{L^q(r dr)} ≲ Σ_{ℓ≥0} (1+ℓ) sup_{n≥ℓ} N(E,2^{-n})^{1/q} 2^{-n/q} ‖g‖_2`  (5.16).

The proof splits `𝔐_p^± ≲ 𝔐_{p,0}^± + 𝔐_{p,∞}^±`, where for the `-` sign

    𝔐_{p,0}^- g(r) := sup_{t ∈ E, r/2<t<3r/2} r^{-1} ∫_{|r-t|}^{2|r-t|} s^{1/2-1/p} (s-|r-t|)^{-1/2} |g(s)| ds,
    𝔐_{p,∞}^- g(r) := sup_{t ∈ E, r/2<t<3r/2} r^{-1} ∫_{2|r-t|}^{r+t} s^{-1/p} |g(s)| ds,

and the `+` sign breaks the `s`-domain at `(r+t)/2` instead.  `𝔐_{p,∞}^±` is
pointwise dominated by the two-dimensional `𝔐_p` of (4.3), so §4 (Propositions
4.4, 4.5, 4.6 — all already formalized here) covers it.  Everything new is in
`𝔐_{p,0}^±`.

### Proposition 5.5 (i) is `E`-free and elementary

For `p > 2` the proof drops `E` entirely, taking the supremum over all
`t ∈ [1,2]` with `r/2 < t < 3r/2`.  Split the `s`-integral into the dyadic
pieces `|r-t|(1 + 2^{-m-1}) ≤ s ≤ |r-t|(1 + 2^{-m})`, on which
`(s - |r-t|)^{-1/2} ≲ (|r-t| 2^{-m-1})^{-1/2}` and `s ∼ |r-t|`, so

    𝔐_{p,0} g(r) ≲ Σ_{m≥0} 2^{m/2} sup_t |r-t|^{-1/p} ∫_{|r-t|(1+2^{-m-1})}^{|r-t|(1+2^{-m})} |g|.

Hölder on an interval of length `|r-t| 2^{-m-1}` gives
`≲ Σ_m 2^{m/2} |r-t|^{-1/p} (|r-t| 2^{-m})^{1/p'} ‖g‖_p
   = Σ_m 2^{-m(1/2 - 1/p)} |r-t|^{1-2/p} ‖g‖_p ≲ ‖g‖_p`,
the `m`-sum converging **exactly because `p > 2`**, and `|r-t|^{1-2/p} ≲ 1`
because `|r-t| ≤ 4`.  The `L^q(r dr)` bound is then trivial integration, since
`𝔐_{p,0} g` vanishes off `[2/3,4]`.

Note this is genuinely stronger than what `prop55_brsMainTwoLeft` gives: that
theorem's right-hand side is `‖s^{1/2-1/p} g‖_p`, not `‖g‖_p`.  The two agree up
to a constant only when `g` is supported in a fixed bounded set and `p > 2`.

### Proposition 5.5(i), as formalized

The chain, all in `BRSRadial.lean`:

* `lintegral_shifted_rpow_Ioc` — `∫_a^{2a}(s-a)^c ds = a^{c+1}/(c+1)` (`c > -1`);
  `lintegral_reflected_rpow_Ioc` — the mirror image `∫_0^b (b-s)^c ds`;
  `lintegral_rpow_Icc_zero_eq` — `∫_0^b s^c ds`.
* `brsZeroConst p := 2^{1/2-1/p} · (1/(1 - p'/2))^{1/p'}` and
  `lintegral_mainZero_weight_le` / `lintegral_mainZeroRight_weight_le` — the two
  Hölder estimates.  **The dyadic decomposition in BRS's proof is unnecessary**:
  plain Hölder with the weight in `L^{p'}` of the near window gives the same
  bound, because `p > 2 ⟺ p' < 2 ⟺ -p'/2 > -1`, which is exactly the
  convergence the `m`-sum was encoding.  The exponent bookkeeping is
  `κ + 1/p' - 1/2 = 1 - 2/p` with `κ = 1/2 - 1/p`.
* `brsMainZeroLeft` / `brsMainInfLeft` (cut at `s = 2|r-t|`) and
  `brsMainZeroRight` / `brsMainInfRight` (cut at `s = (r+t)/2`), with
  `brsMainTwoLeft_le_split` (a factor `2^{1/2}` on the far half) and
  `brsMainTwoRight_le_split` (no factor at all, since `r+t-s ≥ s` there).
* `brsMainInfConst p := (6^{1-p'/p}/(1-p'/p))^{1/p'}` and
  `lintegral_mainInf_weight_le` — the far halves, where the weight is the plain
  power `s^{-1/p}`, in `L^{p'}(0,6)` exactly when `p' < p`, i.e. `p > 2`.  So
  **the far halves need no appeal to §4** and the whole proposition is
  self-contained.
* `lintegral_radial_indicator_rpow_le` — the radial integration, factored out:
  a maximal function supported in `(2/3,4)` and bounded there by `C·G` has
  `‖·‖_{L^q(r dr)} ≤ C · 14^{1/q} · G`.
* `prop55i_brsMainTwoLeft`, `prop55i_brsMainTwoRight` — the proposition.

Note the hypotheses are only `E ⊆ [1,2]`, `2 < p`, `0 < q`, `Measurable g`.  In
particular `p ≤ q` is *not* needed: the `r`-support is a fixed compact interval
away from the origin, so every `q` works.

## Proposition 5.5(ii)–(iii): the `p ≤ 2` case

BRS's proof of (5.15)/(5.16) is the one place in §5 that genuinely needs the
shell decomposition and a convolution inequality.  The scheme:

1. `D_n := {r : 2^{-n} ≤ dist(r,E) < 2^{-n+1}}`, so on `D_n` every admissible
   dilation has `a := |r-t| > 2^{-n}`; `|D_n| ≲ N(E,2^{-n})·2^{-n}`.
2. `ℓ` records the size of `a`: `2^{-n+ℓ-1} ≤ a < 2^{-n+ℓ}`, `0 ≤ ℓ ≤ n+1`.
3. `m` indexes the dyadic pieces `(a(1+2^{-m-1}), a(1+2^{-m})]` of the near
   window `(a, 2a]`, on which the weight is `≲ 2^{(m+1)/2} a^{-1/p}`.
4. For `m ≤ ℓ`: plain Hölder on the piece.  For `m > ℓ`: the `t`-supremum is
   discretized at scale `2^{-n+ℓ-m}` into `O(2^m)` intervals `Q`, and each term
   becomes `|g|1_J ∗ 1_{Q̃}`, estimated by Young.

**Mathlib has no general Young convolution inequality** (checked against the
pinned copy: nothing matching `eLpNorm_convolution`/`young_convolution`).  It is
not needed: the second factor here is always an *indicator*, and for an
indicator Young reduces to Hölder plus the `L^1 ∗ L^s → L^s` case, which the
repo already has as `lintegral_shift_mul_rpow_le`.  With `s = q/p`,

    (1_Q ∗ F)(x) ≤ |Q|^{1-1/p} · ((1_Q ∗ F^p)(x))^{1/p}      (Hölder)
    ‖1_Q ∗ F^p‖_s ≤ |Q|^{1/s} ‖F^p‖_1                        (L^1 ∗ L^s)

and multiplying out gives exactly `‖1_Q ∗ F‖_q ≤ |Q|^{1-1/p+1/q} ‖F‖_p`.  This
is `lintegral_indicator_conv_rpow_le`, with `lintegral_indicator_shift`,
`volume_preimage_sub_left` and `lintegral_indicator_conv_le_pointwise` as steps.

Pieces already in place for the row: `brsNearPieceSet` and its exhaustion of the
near window (`Ioc_subset_iUnion_brsNearPieceSet`, `lintegral_near_le_tsum_pieces`,
`volume_brsNearPieceSet`), the per-piece weight bound `mainWeight_piece_le`
(note the sign flip: for `p ≤ 2` the factor `s^{1/2-1/p}` is *decreasing*, so
both factors are largest at the left end of the piece), the per-piece Hölder
bound `lintegral_nearPiece_le` (giving `2^{(m+1)(1/p-1/2)} a^{1-2/p} ‖g‖_p`,
whose growth in `m` is what forces the `m > ℓ` refinement), the shell cover
`exists_cover_brsU` and the shell measure bound `volume_brsD_le`.

### A simplification: Proposition 5.5(ii)–(iii) needs no interval family `I_n^ν`

BRS organize the `p ≤ 2` proof around a decomposition of each shell `D_n` into
`≈ N(E,2^{-n})` disjoint intervals `I_n^ν`, with the dilations `t` sorted by
`dist(t, I_n^ν)`.  That family is **not needed**.  The only two things it
provides are (a) disjointness of the `r`-supports, which the shells `D_n`
already have, and (b) a count of the fine intervals `Q`, which is cleaner as a
single global cover of `E` at the fine scale.  Reparametrized:

Fix `ℓ ≥ 1` (the size of `a = |r-t|`, via `A := 2^{-n+ℓ}` with `A/2 ≤ a < A`)
and `m ≥ 0` (the dyadic piece of the near window).  For `r ∈ D_n` the whole
`s`-window lies in `J_A := (A/2, 2A]`, so `g` may be replaced by `g·1_{J_A}`.
Then, with `c₁ = A·2^{-m-2}`, `c₂ = A·2^{-m}` (so that
`brsNearPieceSet_subset_shift` applies):

* **`m > ℓ`.**  Cover `E` by `N(E, A2^{-m})` intervals `Q` of length `A2^{-m}`.
  For each `Q`, `lintegral_abs_window_rpow_le` gives
  `‖⨆_{t∈Q} ∫_{|r-t|+c₁}^{|r-t|+c₂}|g|‖_{L^q_r} ≤ 2·(A2^{-m}·(1+3/4))^{1+1/q-1/p}‖g1_{J_A}‖_p`,
  and `⨆_Q ≤ (Σ_Q (·)^q)^{1/q}` turns the cover into a factor
  `N(E, A2^{-m})^{1/q}`.  With the weight factor `2^{(m+1)/2}(A/2)^{-1/p}` and
  the hypothesis `N(E,δ)^{1/q} δ^{1-2/p+1/q} ≤ A_E` at `δ = A2^{-m}`, the whole
  thing is `≲ 2^{m(1/2-1/p)} A_E ‖g1_{J_A}‖_p`, *independent of `ℓ`* — and the
  constraint `ℓ < m` means the `ℓ`-sum contributes only a factor `m`, so
  `Σ_m m·2^{m(1/2-1/p)} < ∞` for `p < 2`.
* **`m ≤ ℓ`.**  No cover: the per-piece Hölder bound `lintegral_nearPiece_le`
  is uniform in `r`, so the `L^q` norm costs only `|D_n|^{1/q}`, and
  `volume_brsD_le` plus the hypothesis at `δ = 2^{-n}` turns
  `|D_n|^{1/q}·A^{1-2/p}` into `A_E·2^{-ℓ(2/p-1)}`.  Summing `m ≤ ℓ` gives
  `2^{ℓ(1/2-1/p)}`, and the `ℓ`-sum converges for `p < 2`.

In both halves the `n`-sum is handled by the **disjointness of the shells**
(`brsD_disjoint`) together with the bounded overlap of the windows `J_A`, using
`p ≤ q` to pass from `ℓ^p` to `ℓ^q`.  Nothing else about `D_n` is used.

The `p = 2` case (5.16) is the same computation with `1/2 - 1/p = 0`: the
geometric sums become the counting factors `(1+ℓ)` and `(1+m)` of (5.16).

### The exponent bookkeeping for (5.15), in the `(n, j, m)` parametrization

Blocks: `A_j := 2^{1-j}` (`j ≥ 0`) with `A_j/2 ≤ |r-t| < A_j`, shells `D_n`, and
`ℓ := n + 1 - j` (so `A_j = 2^{-n+ℓ}` and `j ≤ n` is forced by
`|r-t| ≥ dist(r,E) > 2^{-n}`).  Writing `A_E := sup_{0<δ<1} N(E,δ)^{1/q}δ^{1-2/p+1/q}`,
the two per-`(n,j,m)` bounds are

* Hölder (`m ≤ ℓ`): `H_m ≲ 2^{m(1/p-1/2)} · A_j^{1-2/p} · |D_n|^{1/q} ≲ A_E · 2^{m(1/p-1/2)} · 2^{-ℓ(2/p-1)}`,
  using `volume_brsD_le` and `A_E` at `δ = 2^{-n}`;
* Young (`m > ℓ`): `Y_m ≲ 2^{m/2} A_j^{-1/p} · N(E, A_j 2^{-m})^{1/q} · (A_j 2^{-m})^{1+1/q-1/p} ≲ A_E · 2^{m(1/2-1/p)}`,
  using `A_E` at `δ = A_j 2^{-m}`.  **`Y_m` does not depend on `n` or `j` at all.**

Summing: `Σ_{m≤ℓ} H_m ≲ A_E 2^{ℓ(1/2-1/p)}` and `Σ_{m>ℓ} Y_m ≲ A_E 2^{ℓ(1/2-1/p)}`,
so each `(n,ℓ)` contributes `A_E 2^{-ℓ(1/p-1/2)}`; the `ℓ`-sum is geometric
(convergent exactly for `p < 2`) and the `n`-sum is handled by the disjointness
of the shells plus the bounded overlap of the `s`-windows `J_{A} = (A/2, 2A]`,
using `p ≤ q` for `ℓ^p ↪ ℓ^q`.  For `p = 2` the `ℓ`-sum diverges — which is
exactly why (5.16) is stated with `Σ_ℓ (1+ℓ) sup_{n≥ℓ}(…)` instead.

Measurability discipline for this row: the supremum over `t ∈ E` is over an
uncountable index and is *not* measurable, and Minkowski over `m`
(`lintegral_rpow_tsum_le`) needs measurable summands.  So the supremum is
replaced once and for all by `brsCoverMaj E δ c₁ c₂ q F`, the `ℓ^q` sum over a
chosen cover (`brsCoverFinset`) of the window majorants `brsWindowMaj`, which is
measurable, dominates the supremum pointwise (`iSup_le_brsCoverMaj`), and
carries the bound `N(E,δ)^{1/q}·2·(2δ)^{1-1/p+1/q}·‖F‖_p`
(`lintegral_brsCoverMaj_rpow_le`).

### The order of summation matters: reindex `(n, j)` as `(k, n)` with `j = n - k`

A trap worth recording.  With blocks `A_j := 2·2^{-j}` and shells `2^{-n}`, it is
tempting to sum over `j` outside and `n` inside.  That fails: for fixed `j` the
`s`-window `J_{A_j} = (A_j/2, 2A_j]` does **not** move with `n`, so the
`ℓ^p ↪ ℓ^q` step has nothing to work with and one is left with
`Σ_j ‖g 1_{J_j}‖_p`, which diverges.

The correct outer index is BRS's `ℓ = n + 1 - j`, i.e. `k := ℓ - 1 = n - j`:

    Σ_n 1_{D_n} Σ_j B_j  =  Σ_k Σ_n 1_{D_n} B_{n-k},

where on `D_n` only `j ≤ n` contributes (for `j > n` the block is empty, since
`|r-t| ≥ dist(r,E) > 2^{-n}` forces `A_j > 2^{-n}`).  With this indexing:

* `x = 2^{-n}/A_{n-k} = 2^{-k-1}` depends only on `k`, so the block estimate
  contributes the constant factor `2^{-(k+1)β/2}` — the `ℓ`-decay;
* for fixed `k`, as `n` varies the window `J_{A_{n-k}}` runs through *distinct*
  dyadic scales, so the windows have bounded overlap and `ℓ^p ↪ ℓ^q` gives
  `(Σ_n ‖g 1_{J_{A_{n-k}}}‖_p^q)^{1/q} ≤ (Σ_n ‖·‖_p^p)^{1/p} ≲ ‖g‖_p`;
* the `n`-sum for fixed `k` uses the **disjointness of the shells**
  (`‖Σ_n 1_{D_n} F_n‖_q^q = Σ_n ‖1_{D_n} F_n‖_q^q`), not Minkowski;
* only the `k`-sum uses Minkowski, and it is geometric.

Measurability discipline again: `brsBlockMax` is a supremum over an
`r`-dependent uncountable set, so Minkowski over `k` cannot be applied to it
directly.  The `Σ_m`-majorant built inside `lintegral_brsBlockMax_shell_le`
must be exposed as its own definition (`brsBlockMaj`), measurable and
dominating `1_{D_n}·brsBlockMax`, before the outer sums can be taken.

### `prop55ii_brsMainZeroLeft` is proved

The hard half of BRS Proposition 5.5(ii) — `𝔐_{p,0}^-` for `1 ≤ p < 2 ≤ q`, `p ≤ q` — is
complete.  Hypotheses: `E ⊆ [1,2]` nonempty with `|closure E| = 0`, and
`HasBRSCoveringBound E p q AE`, i.e. `N(E,δ)^{1/q} ≤ AE·δ^{-(1-2/p+1/q)}` for
`0 < δ ≤ 2` — which is (5.15)'s supremum in dyadic form.  Conclusion:

    ‖𝔐_{p,0}^- g‖_{L^q(r dr)} ≤ brsMainZeroConst p q · AE · ‖g‖_p.

The chain, in dependency order:

1. `brsNearPieceSet` / `mainWeight_piece_le` / `lintegral_nearPiece_le` — the
   dyadic pieces of the near window and the per-piece Hölder bound;
2. `brsWindowMaj`, `brsCoverMaj` (with `brsCoverFinset`) — measurable majorants
   for the `t`-supremum, and `lintegral_indicator_conv_rpow_le`, Young against
   an indicator;
3. `brsBlockMax` / `brsBlockMaj` / `lintegral_brsBlockMaj_rpow_le` — one shell,
   one block, with the `m`-sum done by Minkowski on the majorants;
4. `brs_holder_arm_le` / `brs_cover_arm_le` / `brs_interp_term_le` /
   `lintegral_brsBlockMaj_bound` — the two arms evaluated and interpolated;
5. `brsShellMaj` / `lintegral_brsShellMaj_bound` — the `(k, i)` reindexing;
6. `lintegral_rpow_tsum_disjoint` + `tsum_lintegral_block_windows_le` +
   `tsum_rpow_le_rpow_tsum` — the `i`-sum, via disjoint shells, bounded overlap
   of the `s`-windows, and `ℓ^p ↪ ℓ^q`;
7. `prop55ii_brsMainZeroLeft` — the `k`-sum, geometric, the only place
   Minkowski is applied to the outer index and the only place `p < 2` is used
   for convergence.

Still open for the row: the far half `𝔐_{p,∞}^-` (this is §4 territory:
Proposition 4.5 with `d = 2`), and the `+` sign, which should go through the
`x ↦ 3 - x` reflection exactly as for Proposition 5.5(i).

### Proposition 5.5(ii) is complete, both signs

`prop55ii_brsMainTwoLeft` and `prop55ii_brsMainTwoRight`.  Hypotheses:
`E ⊆ [1,2]` nonempty with `|closure E| = 0`, `1 ≤ p < 2 ≤ q` with `p ≤ q`,
`0 < AE`, and `HasBRSCoveringBound E p q AE` (now stated for `0 < δ ≤ 6`, the
range the right endpoint needs).

The two signs are genuinely different in difficulty, and it is worth recording
why:

* For `𝔐_{p,0}^-` the singularity is at `s = |r-t|`, which can be arbitrarily
  small, so the estimate needs the block decomposition of `|r-t|`, the shells
  `D_n`, the `(k,i)` reindexing, and two competing bounds interpolated.
* For `𝔐_{p,0}^+` the singularity is at `s = r+t ∈ (1,6)`, **bounded away from
  zero**.  So the weight bound on the `m`-th piece is uniform, there is no
  block and no shell structure, and a single Young estimate plus one geometric
  series in `m` suffices (`brsRightPieceSet`, `brsRightWeight`,
  `brsWindowMajAdd`, `brsCoverMajAdd`, `brs_right_term_identity`).
* Both far halves `𝔐_{p,∞}^±` have the *same* shell majorant as `𝔐_p` in
  dimension two, so `prop45_of_maj` — Proposition 4.5 restated for any function
  with that majorant and vanishing off `U_0` — covers them with no new
  analysis.

Adding the halves cannot use Minkowski (the supremum defining `𝔐_p^±` is not
measurable).  `lintegral_radial_rpow_add_le` uses the convexity bound instead,
which needs measurability of only one summand, and the near halves supply it
through `brsMainZeroMaj` / `brsMainZeroRightMaj`.

## Row 45 (Proposition 4.3 at `q = pd`) is not blocked after all

The earlier note said this endpoint needs Marcinkiewicz interpolation, which
Mathlib lacks.  That is true of the *general* off-diagonal theorem, but not of
what this operator needs.  Write `G(λ) := ∫_{|f₀|>λ}|f₀| dμ_d` and
`N := ‖f₀‖_{L^p(μ_d)}`.  Two elementary facts:

* splitting `f₀` at height `λ` gives, for **every** `λ > 0` and every `r`,
  `R₂f₀(r) ≤ C r^{-1} G(λ) + 2λ`
  (the big part by (4.5) at `p = 1`, the small part by the trivial `L^∞` bound
  `r^{-1}∫_{t-r}^{t+r}|f₀| ≤ 2λ`);
* hence, taking `λ = s/4`, `{r : R₂f₀(r) > s} ⊆ (0, 2CG(s/4)/s)`, so
  `μ_d({R₂f₀ > s}) ≤ (2C G(s/4)/s)^d / d`.

Feeding that into the layer-cake formula and substituting `λ = s/4` turns
`‖R₂f₀‖_{L^{pd}}^{pd}` into a constant times

    I := ∫_0^∞ λ^{d(p-1)-1} G(λ)^d dλ,

and `I ≤ (d(p-1))^{-1} N^{pd}` follows from **Minkowski's integral
inequality** — which the repo already has as `lintegral_rpow_lintegral_le`.
Explicitly, with `F(λ,x) := λ^{(d(p-1)-1)/d} · 1_{|f₀(x)|>λ} |f₀(x)|`,

    I^{1/d} = ‖∫_x F(·,x)‖_{L^d(dλ)} ≤ ∫_x ‖F(·,x)‖_{L^d(dλ)} dμ
            = (d(p-1))^{-1/d} ∫ |f₀|^p dμ,

because `∫_0^{|f₀(x)|} λ^{d(p-1)-1} dλ = |f₀(x)|^{d(p-1)}/(d(p-1))`.  The
hypothesis `p > 1` is exactly what makes that inner integral converge — and it
is exactly the paper's hypothesis for the endpoint (`p = 1` is excluded there).

So no interpolation theorem is needed: one pointwise splitting, the layer cake,
and Minkowski.  The same remark should be checked against row 80 ((5.6) at
`q = 2p`) before assuming that one needs interpolation either.

## Row 45 closed: Proposition 4.3 at `q = pd`

`prop43_brsRemainderTwo_endpoint` proves the endpoint for every `p > 1`, by the
route sketched in the previous section.  The machinery added for it is generic
and should be reused for the other endpoint rows:

* `brsTail μ f lam` — the tail `∫_{f>λ} f dμ`; `antitone_brsTail` /
  `measurable_brsTail` give measurability in the level for free.
* `lintegral_tail_kernel_eq` — `∫_0^∞ (λ^{(a-1)/m} 1_{λ<c} c)^m dλ = a^{-1}c^{m+a}`.
* `lintegral_brsTail_rpow_le_subset` — Minkowski's integral inequality on any
  measurable `S ⊆ (0,∞)`; it still carries the finiteness hypothesis that
  `lintegral_rpow_lintegral_le` needs.
* `brsTail_le_lintegral_rpow` — the Chebyshev bound `G(λ) ≤ λ^{1-p}‖f‖_p^p`,
  which is exactly what makes that hypothesis checkable on a bounded window.
* `lintegral_brsTail_rpow_le_total` — monotone convergence over
  `S n = (1/(n+1), n+1]` removes the finiteness hypothesis altogether:
  `∫_0^∞ λ^{a-1}G(λ)^m dλ ≤ a^{-1}‖f‖_p^{pm}` whenever `1 + a/m = p`.
* `brsWeightMeasure d = s^{d-1} ds`, with `lintegral_brsWeightMeasure` and
  `brsWeightMeasure_Ioo`.  (The pre-existing `brsRadialMeasure` is the `d = 2`
  case with density `ofReal r`; the new one takes `d` as a parameter.)
* `lintegral_ennreal_rpow_eq_meas_lt` — the layer cake for `ℝ≥0∞`-valued
  functions, needed because the repo's `lintegral_enorm_rpow_eq_distribution`
  is stated for `ℂ`-valued ones.
* `brsRemainderTwo_le_tail` — the splitting `R₂f₀(r) ≤ 3^{d-1}r^{-1}G(λ) + 2λ`,
  and `measure_brsRemainderTwo_gt_le` — the resulting level-set bound
  `μ_d{R₂f₀ > u} ≤ (2·3^{d-1}/u)^d G(u/4)^d / d`.

Two traps worth recording.

1. **No change of variables is needed** for the `λ = u/4` substitution.
   `brsTail_smul` says `G_{cf}(u) = c·G_f(u/c)`, so applying the tail estimate
   to `4|f₀|` instead of `|f₀|` absorbs the scaling into the constant.  Trying
   to push a factor of `4` through `∫_0^∞ … du` directly would need
   `Real.map_volume_mul_left`, which is avoidable.
2. **`p = 1` is genuinely excluded.**  The level integral is
   `∫_0^∞ λ^{d(p-1)-1}G(λ)^d dλ`, and `a = d(p-1) > 0` is what makes the inner
   integral `∫_0^{|f₀|} λ^{a-1} dλ` converge.  At `p = 1` the estimate is only
   of weak type, which is also the paper's hypothesis.

## Row 77 closed: Lemma 5.3 for `p > 2`

BRS state Lemma 5.3 for all `1 ≤ p < ∞` but give no proof — they cite
[21, Prop. 5.3].  The elementary Hölder+Tonelli argument used here for
`p ≤ 2` really does break at `p > 2`, and not for want of cleverness: the
per-piece claim

    ∫ r^{1-p/2} P_a(r)^p dr ≤ C δ^p ∫ s|g|^p ds

is **false** for `p > 2`.  Take `E = {1}`, `g = 1_{[1-2δ,1-δ]}`: the left side
is `≍ δ^{p+2-p/2}` and the right `≍ δ^{p+1}`, so the ratio is `δ^{1-p/2} → ∞`.
The same computation shows the dyadic route can only give the weaker
coefficient `N(E,2^{-m})^{1/p}2^{-m/p}`.

The fix is to abandon the dyadic decomposition for `p > 2` and use Hölder
*directly on the half-power kernel*:

    |∫_{t-r}^{t} (s-(t-r))^{-1/2} f(s) ds|
        ≤ ‖(·)^{-1/2}‖_{L^{p'}(0,r)} ‖f‖_{L^p[t-r,t]}
        = ((p-2)/(2(p-1)))^{-1/p'} r^{1/p'-1/2} ‖f‖_{L^p[t-r,t]},

which converges precisely because `p' < 2`, i.e. `p > 2`.  Multiplying by
`r^{-1/2}` gives `R₂^± f(r) ≤ C_p r^{-1/p}‖f‖_{L^p}` **uniformly in the
dilation `t`**, so the supremum over `t ∈ E` costs nothing, and
`∫_0^{4/3} r · r^{-1} dr = 4/3` finishes.  The conclusion,
`lemma53_brsRemTwoTwo{Left,Right}_of_two_lt`, is therefore *stronger* than the
paper's Lemma 5.3 in this range: no covering number of `E` appears at all.

New machinery: `lintegral_kernel_shift_left` / `lintegral_kernel_shift_right`
(the `L^{p'}` norm of `|s-a|^c` on a window with an endpoint at `a`, via
`lintegral_sub_right_eq_self` and `lintegral_comp_neg`), `brsR2LargeConst`
and `brsR2LargeConst_pos`, `conjExponent_pos_of_two_lt`, and the pointwise
bounds `brsRemTwoTwo{Left,Right}_le_of_two_lt`.

Note for the assembly rows: BRS only ever invoke Lemma 5.3 at `p ≤ 2`
(`p = 1+β ≤ 2` for `P_{2,β}`, and `max{1,2β} < p₀ < 1+β` for the endpoint of
Theorem 1.2(ii)), so the covering-number form is what the downstream argument
actually consumes.

## Row 80 closed: (5.6) at the endpoint `q = 2p`

The suspicion recorded above was right — no interpolation is needed — but the
route is even shorter than the layer cake.  On the far piece the kernel obeys
`|s-(t-r)|^{-1/2} ≤ (r/2048)^{-1/2}`, so

    ℬ^± g(r) ≤ r^{-1/2}(r/2048)^{-1/2} ∫_{t-r}^{t+r}|g| = 2048^{1/2} r^{-1}∫_{t-r}^{t+r}|g|,

and the right-hand side is *exactly* `2048^{1/2}` times the §4 remainder
`R₂(absProfile g)(r)` in dimension two — same dilation constraint `t ≥ 3r/2`,
same window `[t-r, t+r]`, and `E ⊆ [1,2]` so the supremum only shrinks
(`brsBFar{Left,Right}_le_brsRemainderTwo`).  The endpoint of (5.6) is therefore
`prop43_brsRemainderTwo_endpoint` at `d = 2`, where `q = pd = 2p`.

Two things to know when using `prop56_brsBFar{Left,Right}_endpoint`:

* it needs `Continuous g`, not just `Measurable g`, because the layer cake
  behind Proposition 4.3 needs `measurable_brsRemainderTwo`, which is proved
  by a rational-supremum argument that uses continuity;
* it needs `1 < p`, again because `a = d(p-1) > 0` is what makes the level
  integral converge.  Both hypotheses already hold wherever §5 uses (5.6).

Instantiating the `d = 2` statement takes
`simp only [Nat.cast_ofNat, show (2:ℕ) - 1 = 1 from rfl, pow_one, ofReal_norm,
show p * (2:ℝ) = 2 * p from mul_comm p 2]`.

## Rows 87/88: the diagonal is closed; only `q = 2p` of 5.4(i) is left

`prop54_brsRemTwoTwo{Left,Right}_pq` needs `p < q` strictly, because
`brs_exponent_data` gives `1 < r` only then.  The missing diagonal `q = p` is
exactly Lemma 5.3, and the two hypotheses match:

* at `q = p` the condition `q/p < 1 + q/2 - β` reads `β < p/2`, which is
  precisely when `∑_m N(E,2^{-m})^{1/p}2^{-m/2}` converges
  (`tsum_brsLemma53Coeff_ne_top`, via `brsLemma53Coeff_le_geom` and
  `brsDyadic_eq_rpow`);
* the other condition `q/p < 2 - β` reads `β < 1`, implied by `β < p/2 ≤ 1`
  when `p ≤ 2`, and irrelevant when `p > 2` because there the `E`-free bound of
  row 77 applies with no condition on `β` at all.

`prop54_brsRemTwoTwo{Left,Right}_diag` packages both cases.  Note it is stated
against the *weighted* norm `(∫ s‖g‖^p)^{1/p}` (Lemma 5.3's normalisation),
whereas `_pq` uses the plain `L^p` norm; on the region the operator actually
sees, `s ∈ [1/3,2]`, the two differ by at most a factor `3^{1/p}`.

**Row 88 (Proposition 5.4(ii), `1 < q < 2`) is therefore closed**: `p < q` by
`_pq`, `p = q` by `_diag`, and `q < 2 ≤ 2p` holds automatically for `p > 1`, so
the `q = 2p` endpoint never occurs in this part.

**Row 87 still lacks `q = 2p`, and this is not a bookkeeping gap.**  Both the
paper's argument and ours produce, for the `k`-sum, the exponent
`brsSumExpK = β - 2 + q/p`, which at `q = 2p` equals `β`.  With only the
*global* covering bound `N(E,2^{-j}) ≲ 2^{βj}` the sum diverges for every
`β ≥ 0`, and `β ≥ 0` is forced whenever `E ≠ ∅`.  What makes the endpoint work
in BRS is that (5.2) uses the *localized* covering numbers
`ω_m^{p,q}(E,k) = sup_{|J|=2^{-k}} 2^{-k(2/q-1/p)}N(E∩J,2^{-m-k})^{1/q}`:
for a `β`-regular set `N(E∩J,2^{-m-k}) ≈ 2^{mβ}` with no `k`-growth, so the
`ℓ^∞_k` norm is finite exactly when `q ≤ 2p`.  Closing row 87 therefore means
re-deriving the §5 chain with a localized covering hypothesis in place of `hN`
— a refactor of `prop54_*_of_exponents`, not a new estimate.  Interpolating
from the interior cannot reach it (the endpoint is a vertex of the family), and
neither the `p > 2` `E`-free bound of row 77 nor the `ℬ`-endpoint of row 80
covers the near part `𝒜` there.

## Next: row 92, Proposition 5.5(iii) at `p = 2`

(5.16) reads

    ‖𝔐_2^± g‖_{L^q(r dr)} ≲ Σ_{ℓ≥0}(1+ℓ) sup_{n≥ℓ} N(E,2^{-n})^{1/q}2^{-n/q} ‖g‖_2.

The reason it is a separate case: `prop55ii_*` runs the `m`-summation on the
geometric factor `2^{-m(1/p-1/2)}`, and its hypothesis `a = 1 - 2/p < 0` is
exactly `p < 2`.  At `p = 2` that factor is `1` and the sum over `m` diverges
logarithmically — hence the `(1+ℓ)` weight and the `sup_{n≥ℓ}` grading in the
paper's coefficient.  `HasBRSCoveringBound E p q AE` already specialises
correctly (`1 - 2/p + 1/q = 1/q` at `p = 2`), so what is needed is a graded
version of the block/shell summation of `prop55ii_brsMainTwoLeft`, not new
analysis.

## Row 87: what the localized refactor actually involves

`hN` reaches the estimate through exactly one place —
`brs_5_9_near{,_low}_covering`, which picks a single cover `ι` of `E` at scale
`2^{-j}` and sums `ι.card` copies of a bound that uses the **global** `‖g‖_p`.
Localizing means a two-level cover: blocks `J ⊆ [1,2]` of length `2^{-k}` (the
radius scale), then cover points at scale `2^{-j}` inside each block, with

* the per-point bound restated against `‖g·1_{W_J}‖_p` rather than `‖g‖_p`
  (`brs_5_9_near` and everything it rests on),
* bounded overlap of the windows `W_J` (for `a ∈ J` and `r ∈ I_k`, `a - r`
  ranges over an interval of length `≈ 2^{-k}`, and adjacent blocks overlap by
  a bounded amount),
* the `ℓ^p ↪ ℓ^q` embedding (valid since `p ≤ q`) to turn `Σ_J ‖g‖_{L^p(W_J)}^q`
  into `‖g‖_p^q`.

That replaces `Σ_J N(E∩J, 2^{-j})` by `sup_J N(E∩J,2^{-j})`, which is exactly
BRS's `ω_m^{p,q}(E,k)`, and the `k`-sum becomes a `k`-supremum — finite at
`q = 2p`.  This is a redevelopment of the §5 near-part chain, not a local
patch; budget accordingly.

## Row 87: the localized chain, bottom layers built (2026-09-06)

The `q = 2p` endpoint needs `sup_J N(E ∩ J, δ)` in place of `N(E, δ)`.  Tracing
`hN` shows it reaches the estimate through exactly one place,
`brs_5_9_near{,_low}_covering`, so the whole localization is a matter of
rebuilding that one branch of the chain and re-plumbing.  The bottom layers are
now in place, each proved and building:

* `lintegral_convolution_rpow_le_young_local` — Young on a window `V`, seeing
  `g` only on a `W ⊇ V + supp K`.  The trick throughout is to replace the data
  by `W.indicator g` and then quote the *global* lemma; no Tonelli is redone.
* `tsum_setLIntegral_le_of_overlap` — a boundedly overlapping family costs only
  the overlap constant.
* `lintegral_enorm_indicator_rpow`, `setLIntegral_comp_neg` (via
  `MeasurePreserving.setLIntegral_comp_preimage_emb`, so no measurability
  hypothesis is needed), and `lintegral_reflconv_rpow_le_young_local` — the
  same for the reflected convolution `brsRefl (K ⋆ ǧ)`, which is the shape the
  near part actually has.
* `lintegral_brsWindowMax_rpow_le_local` — the window maximal estimate with the
  radius confined to `V`.
* `iSup_enorm_translate_rpow_le_sum` (the pointwise covering bound, factored out
  of the old proof) and `lintegral_iSup_enorm_translate_rpow_le_local` — the
  maximal estimate with a two-level cover: a block index `bl`, a per-block count
  `Nloc`, and per-block windows `A i`.  This is where `#ι` becomes `Nloc`.
* `lintegral_window_weight_rpow_le_local`, `lintegral_brsNearMax_rpow_le_local`,
  `brs_5_9_near_local` — the radial weight extracted *without* discarding the
  restriction to `brsWindowExt kw`, which is what makes localization possible at
  all (the old chain drops it before the covering step).
* `finset_sum_rpow_le_rpow_sum` — the `ℓ^p ↪ ℓ^q` step that turns
  `Σ_J ‖g‖_{L^p(W_J)}^q` into `‖g‖_p^q`.
* `exists_blockIndex`, `card_filter_blockIndex_le`, `card_le_of_pairwise_close`,
  `brsBlockWindow`, `card_filter_brsBlockWindow_le` (overlap ≤ 9),
  `sum_setLIntegral_brsBlockWindow_le`, `brsDilBlock`, `exists_brsDilBlock_mem`,
  `exists_twoLevelCover` — the geometry: blocks of length `2^{-kw}` tiling
  `[1,2]`, their nine-fold overlapping `g`-windows, and the assembly of
  per-block covers into one cover with a block index.

**What remains.**  In order:

1. `brs_5_9_near_low_local` — the same for the lowest-frequency piece
   (`brs_5_9_near_low` has the identical shape, with `brsLowConst` in place of
   `brsKernelConst`).
2. `brs_5_9_near_covering_local` — feed `exists_twoLevelCover` in, collapse the
   block sum with `finset_sum_rpow_le_rpow_sum` and
   `sum_setLIntegral_brsBlockWindow_le`, and land on
   `sup_i N(E ∩ brsDilBlock kw i, 2^{-j})` in place of `#ι`.  The geometric
   side conditions to discharge are `hVA` (for `a` within `δ/2` of block `i`,
   `s ∈ [a-δ/2,a+δ/2]` and `x ∈ brsWindowExt kw` give `s - x ∈ A i`) and `hAW`
   (thickening by `2^{-kt} + 2^{-j} ≤ 2^{-kw}`), both routine once
   `kt = kw + 1` and `j = kw + a` with `a ≥ 3` are fixed.
3. `brsNearFamily_{zero,succ}_term_le_local`, `brsNearFamily_term_le_local`.
4. `brs_term_le_gen_local` — **the structural change**: the hypothesis becomes
   `ω`-shaped, `∀ k m J, N(E ∩ J, 2^{-(m+k)}) ≤ Cβ 2^{βm}` for `|J| = 2^{-k}`,
   and the `k`-sum becomes a `k`-supremum.  `brsSumExpK` disappears; only
   `brsSumExpM` survives.
5. `brs_near_interior_family_local` — the `(k,m)` assembly with `sup_k` instead
   of `Σ_k`; this is the one place where the summation *architecture* changes.
6. `prop54_brsRemTwoTwo{Left,Right}_interior_local`, `_of_exponents_local`,
   `_pq_local`, and finally the `q = 2p` statement.

The far half needs nothing: row 80 already gives `ℬ^±` at `q = 2p`, `E`-free.

## Correction: the repo *does* have Littlewood--Paley

The "Blocker analysis (2026-09-06)" section above says the pinned Mathlib has
"no Littlewood--Paley".  That is true of Mathlib, but **not of this repo**:
`LeanSpherical/Auto/LittlewoodPaley.lean` and
`LeanSpherical/Auto/MikhlinHormander.lean` contain a complete, axiom-clean

    theorem littlewoodPaley_of_mikhlin {d : Nat} [NeZero d] (C : lpCutoffs d) :
      littlewoodPaley C

with `littlewoodPaley C` unfolding to: for every `p > 1` there is `A > 0` with
`∫ (Σ_{k ∈ K} |P_k f|²)^{p/2} ≤ A ∫ ‖f‖^p` for every finite set of scales `K`
and every Schwartz `f` (`#print axioms` shows only
propext/Classical.choice/Quot.sound).  `mikhlin` is there too.  Any future
statement that §5 is blocked for want of Littlewood--Paley is wrong.

## Row 87, revised: what the endpoint really needs

Reading BRS (5.9)--(5.10) carefully settles how the `k`-summation works, and it
is **not** a geometric series.  The paper's per-term estimate is

    ‖sup_{t∈E}|𝒜_{k,m}f₀|‖_{L^q(r dr)}
        ≲ 2^{-m(1/2+1/q-1/p)} ω_m^{p,q}(E,k) ‖ψ_{k+m} ∗ f₀‖_p,

with the **Littlewood--Paley piece** `ψ_{k+m} ∗ f₀` on the right, not `‖f₀‖_p`.
Then, for `q ≥ 2`,

    (Σ_k ω(k)^q ‖ψ_{k+m}∗f₀‖_p^q)^{1/q}
        ≤ (sup_k ω(k)) (Σ_k ‖ψ_{k+m}∗f₀‖_p^q)^{1/q}
        ≲ (sup_k ω(k)) ‖(Σ_k |ψ_{k+m}∗f₀|²)^{1/2}‖_p
        ≲ (sup_k ω(k)) ‖f₀‖_p,

the last step being exactly the square-function theorem.  So the `k`-variable is
summed by Littlewood--Paley, and only then does `ℓ^∞_k` (i.e. `q ≤ 2p`) appear.
The repo's chain instead puts the *whole* `‖g‖_p` in every term and sums a
geometric series in `k`, which forces `brsSumExpK < 0`, i.e. `q < 2p`.  That is
the real reason the endpoint is out of reach, and localizing the covering
numbers alone does **not** fix it: with the localized bound the `k`-exponent
becomes `q/p - 2`, which is `0` at `q = 2p` — a divergent sum, a finite
supremum.

Consequently row 87 needs, on top of the localized covering chain now in place:

1. a **two-factor resolution** `Ψ_j = υ_j ∗ ψ_j` in place of the repo's
   one-factor `brsLPKernel φ j`, so that the LP piece can be split off.  The
   Fourier-side "fat multiplier" trick is already in the repo
   (`fatDyadicBandpassMultiplier`,
   `dyadicBandpassMultiplier_mul_fatDyadicBandpassMultiplier`);
2. transferring `littlewoodPaley_of_mikhlin` from `lpCutoffs`-multipliers on
   `Euclidean d` to the convolution family `{ψ_j}` on `ℝ = Euclidean 1` used
   here, for the repo's non-Schwartz `g` (a density argument);
3. the elementary `ℓ^q ↪ ℓ²` (valid for `q ≥ 2`) and `ℓ^q`-valued Minkowski
   steps;
4. re-deriving (5.9) against `ψ_{k+m} ∗ f₀` and assembling with `sup_k`.

Steps 3 and 4 are routine given 1 and 2.  Nothing here is a missing foundation.

## Row 87: the two sequence-space steps are done; what the LP transfer needs

`tsum_rpow_le_rpow_tsum_sq` (`ℓ² ↪ ℓ^q` for `q ≥ 2`) and
`tsum_lintegral_rpow_le_lintegral_tsum` (the `ℓ^r`-valued Minkowski inequality,
obtained from `lintegral_rpow_lintegral_le` with the counting measure on `ℕ`)
are proved and spliced.  Together they reduce (5.10) to the square-function
bound for the family `{ψ_j}`.

Two facts about that transfer, established by reading the argument rather than
guessing:

* **`ψ` must stay compactly supported.**  It is tempting to take
  `ψ_j = 𝓕⁻¹(band_j)`, which would make `ψ_j ∗ f` literally the repo's
  `integerDyadicProjection` and the square function immediate from
  `littlewoodPaley_of_mikhlin`.  That fails: BRS take `u, υ₁, ψ₁ ∈ C_c^∞`
  supported in `(-2^{-10}, 2^{-10})`, and compact support of *both* factors is
  what gives (5.14) — the localization `h_k ∗ υ_{k+m} ∗ g(t-r) =
  h_k ∗ υ_{k+m} ∗ [g 1_{J*}](t-r)` — which is exactly the step the localized
  chain built here relies on (`hAW` in `brs_5_9_near_covering_local`).
  A band-limited `ψ` is not compactly supported, so the localization would
  break.
* Hence what is needed is Littlewood--Paley for a **compactly supported**
  mean-zero bump family.  The route through the repo is: `ψ̂(ξ) = O(|ξ|^N)` at
  the origin (from the vanishing moments) and `O(|ξ|^{-M})` at infinity (from
  smoothness), so `Σ_j ε_j ψ̂(2^{-j}ξ)` satisfies `MikhlinCondition` uniformly
  in the finite set of scales and the signs; `mikhlin` then gives uniform `L^p`
  bounds on the signed sums, and the Rademacher argument of
  `littlewoodPaley_of_uniform_signed` converts those into the square function.
  That last lemma is currently stated for `lpCutoffs`-projections and would
  have to be generalized to an arbitrary family — its proof uses the
  projections only through `rademacherSignedSum` and `finiteSquareEnergy`, so
  the generalization is mechanical.

Remaining for row 87, in order: (a) generalize `littlewoodPaley_of_uniform_signed`
to an arbitrary family of operators; (b) verify the Mikhlin condition for
`Σ_j ε_j ψ̂(2^{-j}·)`; (c) transfer between `Euclidean 1` and `ℝ` and from
Schwartz data to the `L^p` functions used here; (d) restate (5.9) against
`ψ_{k+m} ∗ f₀` and assemble with `sup_k` using the two lemmas above.

## Row 87 step (a) is done: the Rademacher bridge, for an arbitrary family

`brs_squareEnergy_le_of_uniform_signed` is `littlewoodPaley_of_uniform_signed`
with the dyadic projections replaced by an arbitrary family `g : I → X → ℂ`:
uniform `L^p` bounds on the Rademacher signed sums give

    ∫ (Σ_{i ∈ s} ‖g i x‖²)^{p/2} dμ ≤ 12 · 2^{p/2} · B.

`#print axioms` is clean.

**Why it was restated rather than reused.**  The generic core of that argument
(`integral_rademacher_lower_moment` and the four private lemmas it rests on)
is `private` in `Auto/LittlewoodPaley.lean`.  Removing `private` is a
one-character change, but `LittlewoodPaley.lean` sits below
`MikhlinHormander.lean` (10k lines), `Bourgain.lean`, `BRRS.lean` (56k) and
`AHRSUpperBounds.lean` (80k) in the import graph, so it would trigger a rebuild
of essentially the whole project after every edit.  The five lemmas were
therefore copied into `BRSRadial.lean` with a `brs_` prefix and the
`Auto.LittlewoodPaley` identifiers fully qualified — the proofs are unchanged.
If the import graph is ever reorganized, delete `brs_rademacher_*` and
`brs_integral_rademacher_lower_moment` and use the originals.

Watch out: renaming with a plain substring substitution turns
`integral_rademacher_lower_moment` into `brs_integral_brs_rademacher_lower_moment`,
because `rademacher_lower_moment` is a substring of it.

Remaining for row 87: (b) the Mikhlin condition for `Σ_j ε_j ψ̂(2^{-j}·)` with
`ψ ∈ C_c^∞` mean-zero, which feeds `mikhlin` and then (a); (c) the
`Euclidean 1`/`ℝ` and Schwartz/`L^p` transfers; (d) restating (5.9) against
`ψ_{k+m} ∗ f₀` and assembling with `sup_k`, for which
`tsum_rpow_le_rpow_tsum_sq` and `tsum_lintegral_rpow_le_lintegral_tsum` are
already in place.

## Row 87 step (b), first half: the two ends of the decay of `𝓕ψ`

The Mikhlin condition for `Σ_j ε_j ψ̂(2^{-j}·)` needs `ψ̂` (and its first two
derivatives) to decay at both ends.  Both ends are now available:

* **at the origin** — `norm_fourierBump_le_of_moments`: if `ψ` is continuous,
  supported in `[-δ, δ]`, and has vanishing moments below `N`, then for
  `2π|η|δ ≤ 1`,
  `‖∫ ψ(y) e^{-2πiηy} dy‖ ≤ (2π|η|)^N (N+1)/(N!·N) · δ^N · ∫|ψ|`.
  This is `brs_cancellation_of_taylor` — already in the file for (5.11) — with
  the character `brsChar η` in place of the singular kernel, and
  `Complex.exp_bound` supplying the Taylor remainder.  The hypothesis
  `2π|η|δ ≤ 1` is what `Complex.exp_bound` needs; on the complementary range
  the trivial bound `‖𝓕ψ‖ ≤ ∫|ψ|` already has the right form.
* **at infinity** — `fourierBump_deriv_eq`: for `ψ ∈ C¹` with compact support,
  `∫ ψ'(y) e^{-2πiηy} dy = 2πiη ∫ ψ(y) e^{-2πiηy} dy`, so
  `|η|·|𝓕ψ(η)| ≤ (2π)^{-1}∫|ψ'|`; iterating gives `|𝓕ψ(η)| ≲_M |η|^{-M}`.
  Proved by the fundamental theorem of calculus on `[-R, R]` together with
  `exists_radius_of_hasCompactSupport`, which supplies a radius outside which
  both `ψ` and `deriv ψ` vanish (the derivative because `ψ` vanishes on a
  neighbourhood there).

Still to do for (b): iterate `fourierBump_deriv_eq` to order `M`; identify
`(𝓕ψ)^{(k)}` with `𝓕((-2πix)^k ψ)` so that the origin estimate applies to the
derivatives too (note `x^k ψ` still has vanishing moments below `N - k`);
assemble `Σ_j G_k(2^{-j}ξ) ≤ C` from the two-sided decay
`G_k(η) = |η|^k|ψ̂^{(k)}(η)| ≲ min(|η|^N, |η|^{k-M})`; and transfer the result
from `ℝ` to `Euclidean 1` in the form `MikhlinCondition 2`.

## Row 87 step (b), continued: decay at infinity and the dyadic sum

Two more pieces landed:

* `norm_fourierBump_pow_le_iteratedDeriv` — iterating `fourierBump_deriv_eq`:
  for `ψ ∈ C^M` with compact support,
  `(2π|η|)^M ‖𝓕ψ(η)‖ ≤ ∫ |ψ^{(M)}|`.  The induction is on `M` with
  `iteratedDeriv_succ'` (`iteratedDeriv (M+1) ψ = iteratedDeriv M (deriv ψ)`),
  applying the inductive hypothesis to `deriv ψ`; the base case is
  `norm_fourierBump_le_integral`, which needs `‖e^{-2πiηy}‖ = 1`
  (`norm_brsCharExp`, via `Complex.norm_exp_ofReal_mul_I`).
* `sum_min_geometric_le` — the two-sided geometric sum:
  `Σ_{k ∈ K} min((ρ^k c)^a, (ρ^k c)^{-b}) ≤ (1-ρ^a)⁻¹ + (1-ρ^b)⁻¹`,
  for any finite `K ⊆ ℕ` and any `c > 0`, i.e. **uniformly in the starting
  point** — which is exactly the uniformity in `ξ` that the Mikhlin condition
  demands.  The proof splits `K` at the crossing index
  `k₀ = Nat.find {k | ρ^k c ≤ 1}`, bounds each half by a geometric series after
  reindexing (`Finset.sum_image` with the injections `k ↦ k - k₀` and
  `k ↦ k₀ - 1 - k`), and compares with `tsum_geometric_of_lt_one`.

With these, the remaining Fourier work for (b) is: identify `(𝓕ψ)^{(k)}` with
`𝓕((-2πix)^k ψ)` (differentiation under the integral) so the origin estimate
`norm_fourierBump_le_of_moments` applies to the derivatives — note `x^k ψ`
still has vanishing moments below `N - k` — and then feed
`G_k(η) = |η|^k |ψ̂^{(k)}(η)| ≲ min(|η|^N, |η|^{k-M})` into
`sum_min_geometric_le`.  What is left after that is bookkeeping: assembling
`MikhlinCondition 2` on `Euclidean 1` and the `ℝ`/`Euclidean 1` transfer.

## Row 87 step (b): Mathlib already has the infinity side, on `Euclidean 1`

`sum_dyadic_dilate_le` is landed: if `G η ≤ A|η|^a` and `G η ≤ B|η|^{-b}` with
`a, b > 0`, then for every `ξ ≠ 0`, every `m` and every finite `K ⊆ ℕ`,

    Σ_{k ∈ K} G((1/2)^{k+m} ξ) ≤ (A+B)((1-2^{-a})⁻¹ + (1-2^{-b})⁻¹),

a bound independent of `ξ` — the uniformity the Mikhlin condition needs.  It is
`sum_min_geometric_le` plus `min_mul_le_add_mul_min`.

**Verified by direct probe:** `Real.pow_mul_norm_iteratedFDeriv_fourier_le`
applies verbatim with `V := Euclidean 1` (all `PiLp`/`WithLp` instances resolve;
the only care needed is giving `K` and `N` explicitly as `ℕ∞` and writing the
integrability hypothesis with `(↑k ≤ K)` coercions).  It gives

    ‖w‖^n ‖D^k(𝓕f)(w)‖ ≤ (2π)^k (2k+2)^n Σ_{p} ∫ ‖v‖^{p.1}‖D^{p.2} f(v)‖,

which is exactly the infinity side of the Mikhlin bound for every derivative
order — so `norm_fourierBump_pow_le_iteratedDeriv` (proved here for the
`k = 0` case on `ℝ`) is not needed for the derivatives, and no new work is
required at infinity.  Taking `n = k + 1` gives `G_k(η) ≲ |η|^{-1}`, i.e.
`b = 1` in `sum_dyadic_dilate_le`.

That leaves, for (b): the **origin side for the derivatives**.  Mathlib's
`Real.iteratedFDeriv_fourier` identifies `D^k(𝓕f)` with
`𝓕 (fun v ↦ fourierPowSMulRight (innerSL ℝ) f v k)`; in dimension one that
multilinear map is scalar multiplication by `(-2πi)^k v^k f v`, so the origin
estimate `norm_fourierBump_le_of_moments` applies to `x^k ψ`, which retains
vanishing moments below `N - k`.  This gives `a = N` in `sum_dyadic_dilate_le`.
The remaining bookkeeping is the `ContDiffOn ℝ N m ({0}ᶜ)` clause of
`MikhlinCondition` (from `Real.contDiff_fourier` and finiteness of the sum) and
the passage between the kernels on `ℝ` and their avatars on `Euclidean 1`.

## Row 87: correction — the Mikhlin-for-bumps route is avoidable

`norm_fourierBump_mul_pow_le_of_moments` is landed (with `moments_mul_pow` and
`vanishing_mul_pow`): multiplying by `y^k` shifts the vanishing moments down by
`k`, so the origin estimate applies to `y^k ψ` and loses exactly `k` orders.
That completes the analytic inputs I had been assembling for a Mikhlin
condition on `Σ_j ε_j ψ̂(2^{-j}·)`.

**But that whole route is not the right one, and the file already says so.**
The section "What is left before Proposition 5.4" above records the correct
plan, which I had lost sight of: BRS's factorization `υ_{k+m} * ψ_{k+m}` puts
the compact support on `υ` *only*.  `υ` is the factor that meets the singular
kernel `h_k`, so it is what (5.11) and the localization (5.14) need to be
compactly supported; `ψ` is the *Fourier-localized* factor, and it is the only
one fed to the square-function theorem.  Choosing `ψ̂` supported in an annulus
makes `ψ_j ∗ f` interact with only `O(1)` of the dyadic bands, so

    Σ_j ‖ψ_j ∗ f‖_p^p ≲ Σ_j Σ_{|i-j| ≤ 1} ‖P_i f‖_p^p ≲ Σ_i ‖P_i f‖_p^p ≲ ‖f‖_p^p

follows from `sum_integral_norm_rpow_dyadic_le_line`, **which is already proved
in this file** (it transports `littlewoodPaley_of_mikhlin` to `ℝ` through
`brsLineEquiv`).  No Mikhlin condition for a compactly supported bump family is
needed, and my last two stretches over-scoped that path.

What the factorization actually needs is the existence half: a compactly
supported `υ` with vanishing moments below `N` **and** `υ̂` non-vanishing on the
annulus `1/2 ≤ |ξ| ≤ 2`, after which `ψ̂ := θ̂ / υ̂` for a standard annulus
partition `θ̂` is smooth and annulus-supported, and `Σ_j υ̂(2^{-j}ξ)ψ̂(2^{-j}ξ)
= Σ_j θ̂(2^{-j}ξ) = 1` away from the origin.  That existence statement is the
single remaining obstacle in (b), and it is where the Fourier estimates landed
in the last three stretches are actually useful: `norm_fourierBump_le_of_moments`
controls `υ̂` near the origin and `norm_fourierBump_pow_le_iteratedDeriv`
controls it at infinity, which is what pins down where `υ̂` can be forced to be
non-zero.  `sum_dyadic_dilate_le` and `sum_min_geometric_le` remain generally
useful for any two-sided dyadic summation.

## Row 87: the non-vanishing bump — construction and progress

The one remaining obstacle in (b) is a compactly supported `υ` with vanishing
moments below `N + 1` **and** `𝓕υ` non-vanishing on the annulus.  The
construction is `υ := χ^{(N+1)}` for a suitably dilated bump `χ`:

* `∫ y^i υ(y) dy = 0` for `i < N + 1` — this is
  `integral_pow_mul_iteratedDeriv_eq_zero`, proved by induction on the order
  using the file's own `integral_pow_mul_deriv_eq` (integration by parts against
  a monomial, already present at line ~21448).  Note that the `i = 0` case needs
  no separate treatment: `integral_pow_mul_deriv_eq` at `i = 0` already returns
  `-(0 : ℝ) * …`.  Helpers: `hasCompactSupport_iteratedDeriv`,
  `contDiff_iteratedDeriv_of_top`.
* `𝓕υ(ξ) = (2πiξ)^{N+1} 𝓕χ(ξ)` — this is `fourierBump_iteratedDeriv_eq`,
  iterating `fourierBump_deriv_eq`.  So `𝓕υ(ξ) ≠ 0` exactly when `ξ ≠ 0` and
  `𝓕χ(ξ) ≠ 0`.

What remains is to force `𝓕χ ≠ 0` on `1/2 ≤ |ξ| ≤ 2`.  Rescaling does it: for
`χ_λ(x) = λχ(λx)` one has `𝓕χ_λ(ξ) = 𝓕χ(ξ/λ)`, and `𝓕χ(0) = ∫χ = 1` with `𝓕χ`
continuous, so choosing `δ` with `|𝓕χ(η) - 1| < 1/2` for `|η| ≤ δ` and then
`λ := 2/δ` gives `|𝓕χ_λ(ξ) - 1| < 1/2`, hence `𝓕χ_λ(ξ) ≠ 0`, for all `|ξ| ≤ 2`.
The two Lean ingredients still to supply are the identification of the explicit
integral used here with Mathlib's `Real.fourierIntegral` (so that
`Real.fourierIntegral_continuous` applies) and the dilation identity
`𝓕χ_λ(ξ) = 𝓕χ(ξ/λ)`, which is a change of variables.

## Row 87: the bump exists, and the `k`-sum is now closed in `ENNReal`

Two blocks landed.

**(b) is finished.** `exists_brsBumpNonvanishing N` produces a compactly
supported smooth `υ` with `∫ y^i υ = 0` for `i < N + 1` **and** `𝓕υ(ξ) ≠ 0`
for `1/2 ≤ |ξ| ≤ 2`.  The construction is `υ = χ_λ^{(N+1)}` with
`χ_λ(y) = λχ(λy)` for a `ContDiffBump` of unit mass, `λ` chosen from continuity
of `𝓕χ` at the origin.  The three Fourier facts this needed are now in the
file: `brsFourier_eq` identifies the explicit integral used throughout the
kernel estimates with Mathlib's `𝓕` (via `Real.fourier_eq'`), whence
`continuous_brsFourier` (through `VectorFourier.fourierIntegral_continuous`)
and `brsFourier_zero` (`𝓕ψ(0) = ∫ψ`); `brsFourier_dilate` is the change of
variables `𝓕(λψ(λ·))(η) = 𝓕ψ(η/λ)`, proved with
`MeasureTheory.Measure.integral_comp_mul_left`.

Traps met here: `fourier_eq'` needs the `Real.` prefix (the file does not
`open Real`); `𝓕` needs `open scoped FourierTransform in` before the theorem;
`(lam : ℝ) • (z : ℂ)` is `Complex.real_smul`, not `smul_eq_mul`.

**The `k`-summation is now available.**  The chain that closes BRS (5.10) is
`sum_lintegral_rpow_dyadic_lq_le_line`: for `1 < p`, `q ≥ 2` and `q ≥ p`,

    Σ_k (∫⁻ ‖Δ_k f‖ₑ^p)^{q/p} ≤ A (∫⁻ ‖f‖ₑ^p)^{q/p},

stated on `ℝ` and in `ENNReal`, which is exactly the shape the BRS chain
consumes.  It splits at `p = 2`:

* `p ≥ 2` — `sum_lintegral_rpow_dyadic_le_line`, the `ENNReal` transcription of
  the repo's `sum_integral_norm_rpow_dyadic_le` (`ℓ^p(L^p) ≲ L^p`), then
  `ℓ^p ↪ ℓ^q` (`finset_sum_rpow_le_rpow_sum`, needs `q ≥ p`);
* `p ≤ 2` — `sum_lintegral_rpow_dyadic_sq_le_line`, then `ℓ² ↪ ℓ^q`
  (needs `q ≥ 2`).

**The `p < 2` half is not a variant of the `p ≥ 2` one; it is a different
inequality.**  `Σ_k ‖Δ_k f‖_p^p ≲ ‖f‖_p^p` is *false* for `p < 2`: take `N`
bands each of size `1` on the same unit interval, so that `‖f‖_p ≈ N^{1/2}`
while the left side is `≈ N`.  What survives below `2` is the `ℓ²` statement
`Σ_k ‖Δ_k f‖_p² ≲ ‖f‖_p²`, and it comes from Minkowski's integral inequality
run in the direction valid for `p ≤ 2`:

    (Σ_k (∫ h_k)^{2/p})^{p/2} ≤ ∫ (Σ_k h_k^{2/p})^{p/2},   h_k = |Δ_k f|^p,

whose right side is `∫ (Σ_k |Δ_k f|²)^{p/2}`, i.e. the square function.  So the
`p < 2` half needs the *full* square-function theorem
(`littlewoodPaley_of_mikhlin C p`, valid for every `p > 1`), not the `ℓ^p`
corollary.  New lemmas: `tsum_lintegral_rpow_le_lintegral_tsum'` (Minkowski
against the counting measure on an arbitrary countable index — the earlier
version was fixed to `ℕ`, and the dyadic scales are indexed by `ℤ`),
`tsum_lintegral_rpow_le_lintegral_sq`, `real_finset_rpow_sum_le_sum_rpow`
(subadditivity of `t ↦ t^s` for `s ≤ 1`), `integrable_squareEnergy_rpow_le_two`
(the majorant below `2` is the plain sum `Σ_k ‖Δ_k f‖^p`, simpler than the
`card^{p/2-1}` majorant used above `2`), `enorm_squareEnergy_eq`,
`lintegral_squareEnergy_rpow_le_line`, `lintegral_enorm_rpow_symm_eq`,
`lintegral_enorm_rpow_dyadic_ne_top`, `continuous_integerDyadicProjection`,
`integrable_norm_rpow_schwartz`.

Both halves need `q ≥ max(2, p)`.  That is not a restriction here: the BRS type
set has `p ≤ q` throughout, and Proposition 5.4(i) assumes `q ≥ 2`.

**What is still missing for the endpoint.**  The `k`-sum is closed only for the
repo's `integerDyadicProjection`s of a *Schwartz* function.  Two gaps remain:

1. the factorization `Ψ_j = υ_j ∗ ψ_j` with `υ` compactly supported (so that
   `brs_5_9_near_covering_local`, which already takes an arbitrary `υ`, can be
   applied with `g := ψ_j ∗ g₀`), together with the resolution
   `Σ_j Ψ_j ∗ g₀ = g₀`.  Note the repo's telescoping resolution
   `brsLPKernel φ j` cannot be used for this: its `θ̂(ξ) = φ̂(ξ/2) − φ̂(ξ)` is
   analytic, hence not annulus-supported, so `ψ̂ := θ̂/υ̂` would not be
   compactly supported and `ψ_j ∗ g` would not meet only `O(1)` bands.  The
   resolution must be the Fourier one, which brings in the Calderón
   reproducing formula;
2. the passage from Schwartz `f` to the continuous `g` of the BRS chain.

## Row 87: the BRS band factorization `𝓕⁻θ = υ ∗ ψ` is proved

The factorization step of the plan is done, end to end and axiom-clean.
`exists_brsBandConvolution N hθ hθsupp` takes any smooth band symbol `θ`
supported in `1/2 ≤ |ξ| ≤ 2` and returns

* `υ : ℝ → ℝ`, smooth, `tsupport υ ⊆ closedBall 0 1`, with `∫ y^i υ = 0` and
  `∫ y^i υ' = 0` for `i < N + 1` — exactly the hypotheses of
  `brs_5_9_near_covering_local`;
* `S : SchwartzMap ℝ ℂ` (the factor `ψ`);
* the identity `(υ : ℝ → ℂ) ⋆[mul] ψ = 𝓕⁻θ`.

The chain of new lemmas, in order:

1. `exists_brsBump_fourier_ne_zero N B` — the bump of `exists_brsBump`
   strengthened so that `𝓕υ ξ ≠ 0` for every `0 < |ξ| ≤ B`, with `B` a
   parameter (the dilation `λ` is chosen from `B` and from the modulus of
   continuity of `𝓕χ` at the origin).  It also carries the unit-ball support
   and the derivative's vanishing moments.
2. `contDiff_brsFourierHat` — `𝓕υ` is smooth, because `υ` compactly supported
   and smooth is Schwartz (`HasCompactSupport.toSchwartzMap`) and
   `SchwartzMap.fourierTransformCLM` keeps it Schwartz.
3. `exists_brsAnnulusCutoff` — a smooth `ρ` with `0 ≤ ρ ≤ 1`, `ρ = 1` on
   `1/2 ≤ |ξ| ≤ 2`, and `ρ ξ ≠ 0 → ξ ≠ 0 ∧ |ξ| ≤ 3`.  Built as `ρ ξ = b(ξ²)`
   for a `ContDiffBump` centred at `17/8` with radii `15/8 < 2`; composing with
   the square removes every case split on the sign of `ξ`.
4. `exists_brsSmoothQuotient` — **the device that avoids gluing.**  The naive
   `ψ̂ := θ/𝓕υ` is smooth only where `𝓕υ ≠ 0`, and extending it by zero needs a
   locality argument.  Instead put

       ψ̂ := θ · conj(𝓕υ) · ρ / (𝓕υ · conj(𝓕υ) · ρ + (1 − ρ)).

   The denominator is the coercion of `|𝓕υ|²ρ + (1 − ρ)`, which is *strictly
   positive everywhere*: where `ρ = 0` it is `1`, and where `ρ ≠ 0` the first
   term is positive and the second non-negative.  So the quotient is smooth on
   all of `ℝ` by `ContDiff.inv`, with no gluing, and `𝓕υ · ψ̂ = θ` still holds
   pointwise — on `supp θ` because `ρ = 1` there, and off it because both sides
   vanish.  (`ContDiff.div` is unusable here: it wants the values in the
   *scalar* field, and these are `ℂ`-valued over `ℝ`.  Use `ContDiff.inv` and
   `div_eq_mul_inv`.)
5. `exists_brsBandFactorization` — `ψ̂` is compactly supported (its support sits
   inside that of `θ`), hence Schwartz, hence so is `ψ := 𝓕⁻ψ̂`.
6. `exists_brsBandConvolution` — `Real.fourier_mul_convolution_eq` turns
   `𝓕υ · 𝓕ψ = θ` into `𝓕(υ ∗ ψ) = θ`, and Fourier inversion on Schwartz maps
   (`FourierTransform.fourierInv_fourier_eq`, with
   `SchwartzMap.convolution_apply` identifying the Schwartz convolution with
   the function-level one) gives `υ ∗ ψ = 𝓕⁻θ`.

### What is left for the endpoint

With the factorization and the `k`-summation both in place, the remaining gaps
are the *plumbing*, not the analysis:

* the dyadic form: `υ_j ∗ ψ_j = Θ_j` where `f_j(x) = 2^j f(2^j x)`, by scaling;
* the resolution `Σ_j Θ_j ∗ g = g` for `Θ = 𝓕⁻θ` with `θ` a dyadic band symbol
  — the Calderón reproducing formula.  The repo's `lpCutoffs` already supplies
  such a `θ` (`intDyadicBandpassMultiplier C.cutoff 0` is supported in
  `1/2 ≤ ‖ξ‖ ≤ 2`) together with `homogeneousDyadicResolution`, but on
  `Euclidean d`; transporting to `ℝ` needs `brsLineEquiv` to be recognized as a
  linear isometry, so that `𝓕` commutes with it;
* associativity `(h_k ∗ υ_j) ∗ (ψ_j ∗ g) = (h_k ∗ Θ_j) ∗ g`;
* `Σ_j ‖ψ_j ∗ g‖_p^q ≲ ‖g‖_p^q` for the chain's continuous `g`.  `ψ̂` is
  supported in the annulus, so `ψ_j ∗ g = ψ_j ∗ (fat_j ∗ g)` and Young reduces
  this to `sum_lintegral_rpow_dyadic_lq_le_line`; the remaining step is the
  passage from Schwartz data to the `L^p` functions of the chain.

## Row 87: correction and the exact remaining plan (2026-09-06, late)

Two things I had wrong, both now checked against the arXiv source and against
the file.

**1. BRS's `ψ` is compactly supported, not band-limited.**  The paper's (5.7)
reads `δ = u_k + Σ_{m≥1} υ_{k+m} ∗ ψ_{k+m}` with `u, υ₁, ψ₁ ∈ C_c^∞` supported
in `(−2^{-10}, 2^{-10})` and `υ₁, ψ₁` carrying moment conditions up to order
`N` (they cite [18, Lemma 2.1]).  So the earlier "correction" claiming `ψ̂` is
annulus-supported does **not** describe the paper.  What that earlier note got
right is the *reason* compact support matters: the localization (5.14) needs
only `h_k ∗ υ_{k+m}` to be supported in `(−2^{-k}, 2^{-k})`, i.e. only `υ` must
be compactly supported.  `ψ`'s support plays no role in (5.14) — it is the
factor fed to the square function.  So a band-limited `ψ` is mathematically
legitimate, and it is the better choice *here*, because it puts the square
function inside the reach of the repo's `littlewoodPaley_of_mikhlin` instead of
requiring a fresh Mikhlin condition for a compactly supported bump family.

**2. The band-limited choice forces a Schwartz resolution profile, and that is
the real remaining obstacle.**  The chain's resolution is the telescoping one:
`υ := brsLPKernel φ 0 = φ₁ − φ₀`, so that `brsDilate υ j = brsLPKernel φ j` and
`Σ_j brsDilate υ j ∗ g + φ_k ∗ g = g`.  For the factorization `𝓕υ = 𝓕υ_new · ψ̂`
to have a compactly supported `ψ̂`, `𝓕υ` must be annulus-supported, i.e.
`𝓕φ` must be compactly supported — so `φ` cannot be compactly supported in
space.  Compact support in space and compact support in frequency are mutually
exclusive, and the repo's current `exists_brsBump` (which returns
`brsLPKernel φ 0` for a compactly supported `φ`) therefore cannot be fed to
`exists_brsBandConvolution`.

The resolution that does work is *the same telescoping resolution with a
Schwartz profile*: take `χ` smooth with `χ = 1` on `|ξ| ≤ 1` and `χ = 0` on
`|ξ| ≥ 2` (e.g. `χ ξ = b(ξ²)` for a `ContDiffBump` at `0` with radii `1 < 4`),
and put `p := 𝓕⁻χ`.  Then `𝓕p_j(ξ) = χ(2^{-j}ξ)`, so

    𝓕(p_{j+1} − p_j)(ξ) = χ(2^{-j-1}ξ) − χ(2^{-j}ξ) = θ(2^{-j}ξ),
    θ(ξ) := χ(ξ/2) − χ(ξ),  supp θ ⊆ {1 ≤ |ξ| ≤ 4}.

`p` is Schwartz, real and even (because `χ` is real and even), and `∫p = 𝓕p(0)
= χ(0) = 1`.  So the Calderón reproducing formula *is* the repo's telescoping
resolution, only with a Schwartz rather than compactly supported profile — the
convergence `p_J ∗ G → G` is the ordinary approximate identity for bounded
continuous `G`, no distributional limit needed.

### The remaining work for the endpoint, precisely

1. **Annulus constants.**  `exists_brsBandConvolution` currently assumes
   `supp θ ⊆ {1/2 ≤ |ξ| ≤ 2}`; with the profile above it is `{1 ≤ |ξ| ≤ 4}`.
   Reparametrize `exists_brsAnnulusCutoff` (and the ball radius `B` passed to
   `exists_brsBump_fourier_ne_zero`) by the two annulus radii.  Mechanical.
2. **The profile.**  Construct `χ`, prove `p := 𝓕⁻χ` is Schwartz, real-valued,
   and `∫p = 1`.  Real-valuedness needs `χ` even and real.
3. **Generalize the resolution layer from `HasCompactSupport φ` to a Schwartz
   profile.**  `brs_lp_resolution`, `brs_lp_resolution_shift`,
   `brs_lp_resolution_shift_tendsto`, `brs_resolution_truncConv` use compact
   support only for (a) integrability of `y ↦ φ_J(y) g(x−y)` against bounded
   continuous `g` — true for Schwartz `φ` — and (b) the approximate-identity
   convergence.  This is the largest single item.
4. **The `k`-sum.**  `Σ_j ‖ψ_j ∗ g‖_p^q ≲ ‖g‖_p^q` for the chain's continuous
   `g`.  `ψ̂` is annulus-supported, so `ψ_j ∗ g = ψ_j ∗ (fat_j ∗ g)` and Young
   reduces this to `sum_lintegral_rpow_dyadic_lq_le_line`, which is proved.
   What is not yet bridged is Schwartz data versus the `L^p` functions of the
   chain; `SchwartzMap.toLp` and the density statement near
   `SchwartzSpace/Basic.lean:1389` are the entry point.
5. **Associativity** `(h_k ∗ υ_j) ∗ (ψ_j ∗ g) = (h_k ∗ Θ_j) ∗ g`, from
   `convolution_mul_dilate` (proved) plus `convolution_assoc`.

Items 1, 2 and 5 are routine; item 3 is a contained but large refactor; item 4
is the only one whose shape is still not fully pinned down.

## Row 87: `exists_brsCalderonFactorization` — items 1, 2 and 5 of the plan are done

The capstone of the factorization programme is proved and axiom-clean:

    exists_brsCalderonFactorization (N : ℕ) :
      ∃ (p υ : ℝ → ℝ) (S : SchwartzMap ℝ ℂ),
        ContDiff ℝ ⊤ p ∧ Integrable p ∧ ∫ p = 1 ∧
        ContDiff ℝ ⊤ υ ∧ HasCompactSupport υ ∧
        tsupport υ ⊆ closedBall 0 1 ∧
        (∀ i < N + 1, ∫ y^i υ y = 0) ∧ (∀ i < N + 1, ∫ y^i υ' y = 0) ∧
        (υ : ℝ → ℂ) ⋆ (S : ℝ → ℂ) = fun x => (brsLPKernel p 0 x : ℂ)

so the telescoping piece of a *unit-mass resolution profile* factors as `υ ∗ ψ`
with `υ` meeting exactly the hypotheses of `brs_5_9_near_covering_local` and
`ψ = S` Schwartz with `𝓕ψ` supported in `1 ≤ |ξ| ≤ 4`.

Supporting lemmas landed in this block:

* `exists_brsFrequencyCutoff` — a real, even, smooth `χ` with `χ = 1` on
  `|ξ| ≤ 1` and `χ = 0` on `|ξ| ≥ 2`, again as `b(ξ²)` for a `ContDiffBump`.
* `fourier_apply_zero`, `integral_comp_neg_real`, `fourierInv_apply'`,
  `fourierInv_conj_eq_self` — the last is the reality of `𝓕⁻χ` for real even
  `χ`, proved by `conj ∘ 𝓕⁻ = 𝓕⁻ ∘ (reflection ∘ conj)`.  Mathlib has no
  `∫ f(-x) = ∫ f x` for `volume` on `ℝ`; use
  `Measure.integral_comp_mul_left f (-1)`.
* `exists_brsCalderonProfile` — `p := 𝓕⁻χ`, real (from the previous item),
  smooth, integrable, `∫p = 𝓕p(0) = χ(0) = 1`, with `𝓕p = χ`.
* `integrable_brsChar_mul`, `integrable_brsDilate`, `fourier_brsDilate`,
  `fourier_brsLPKernel` — `𝓕(p_{j}) (ξ) = χ(ξ/2^j)`, hence
  `𝓕(brsLPKernel p 0)(ξ) = χ(ξ/2) − χ(ξ) =: θ(ξ)`, supported in `1 ≤ |ξ| ≤ 4`.
* `exists_brsAnnulusCutoff'` and `exists_brsBandConvolution'` — the annulus
  radii as parameters, so the `1 ≤ |ξ| ≤ 4` band is covered.
* `convolution_mul_dilate` — `(f_λ) ∗ (g_λ) = (f ∗ g)_λ`, which promotes the
  factorization of one band to every dyadic band.

### The remaining gap, restated

Only two items of the plan are left, and they are both about the *chain*, not
about the construction:

* **Item 3 (the largest).**  `brs_lp_resolution`, `brs_lp_resolution_shift`,
  `brs_lp_resolution_shift_tendsto` and `brs_resolution_truncConv` assume
  `HasCompactSupport φ`.  The Calderón profile `p` is Schwartz, not compactly
  supported.  Compact support is used only for (a) integrability of
  `y ↦ φ_J(y) g(x−y)` against bounded continuous `g` — true for `p` as well,
  since `p` is integrable and `g` bounded — and (b) the approximate-identity
  convergence `p_J ∗ g → g`.  Redoing that layer for an integrable profile with
  an integrable radial majorant is the single biggest remaining piece.
* **Item 4.**  `Σ_j ‖ψ_j ∗ g‖_p^q ≲ ‖g‖_p^q` for the chain's continuous `g`.
  `𝓕ψ` is annulus-supported, so `ψ_j ∗ g` meets `O(1)` bands and Young reduces
  this to `sum_lintegral_rpow_dyadic_lq_le_line` (proved); what is missing is
  the passage from Schwartz data to the `L^p` functions of the chain.

## Row 87: item 3 is done — the resolution layer runs on an integrable profile

The compact-support hypothesis has been lifted from the whole resolution layer,
so the Calderón (Schwartz) profile can drive the decomposition.  New lemmas:

* `integral_brsDilate_convolution_eq` — the change of variables
  `∫ φ_J(y) g(x−y) dy = ∫ φ(u) g(x − 2^{-J}u) du`.
* `tendsto_brsDilate_convolution_bdd` — **the approximate identity for an
  integrable profile.**  The compact-support proof splits the integral at the
  support radius; without support the right tool is *dominated convergence*,
  and it is shorter: `φ(u)(g(x − 2^{-J}u) − g(x)) → 0` pointwise by continuity
  of `g` at `x`, dominated by `2C|φ(u)|`.  The price is that `g` must be
  **bounded** — which it is in the chain, since `h` carries `hbd` and
  `h_k ⋆ h` inherits a bound.
* `integrable_ofReal_mul_shift`, `integrable_brsLPKernel`,
  `integral_brsLPKernel_convolution`, `brs_lp_resolution_int`,
  `brs_lp_resolution_shift_int`, `brs_lp_resolution_shift_tendsto_int`,
  `brs_resolution_truncConv_int` — the telescoping identities and their limit.
* `abs_brsLPKernel_le`, `brs_conv_assoc'_int`, `brs_piece_eq_int`,
  `norm_brsTruncKernel_convolution_le` — associativity `Ψ ∗ (h_k ∗ h) =
  (h_k ∗ Ψ) ∗ h` uses compact support of `Ψ` *only* through integrability and
  a sup bound, so the hypotheses become `Integrable Ψ` and `∀ x, |Ψ x| ≤ MΨ`.
* `brsANearLeftAt_le_pieces_int` — the near part dominated by the pieces of the
  resolution, now for an integrable bounded profile.

So the profile `p` of `exists_brsCalderonProfile` (smooth, integrable, unit
mass, and bounded since it is Schwartz) can be fed to the decomposition, and
its telescoping pieces factor as `υ_j ∗ ψ_j` by
`exists_brsCalderonFactorization` together with `convolution_mul_dilate`.

### What is genuinely left

* **Item 4**, the only remaining piece of real content:
  `Σ_j ‖ψ_j ∗ g‖_p^q ≲ ‖g‖_p^q` for the chain's continuous `g`.  `𝓕ψ` is
  supported in `1 ≤ |ξ| ≤ 4`, so `ψ_j ∗ g` meets `O(1)` dyadic bands and Young
  reduces the claim to `sum_lintegral_rpow_dyadic_lq_le_line`, which is proved.
  The gap is the passage from Schwartz data (where the repo's Littlewood--Paley
  theorem lives) to the `L^p` functions of the chain; `SchwartzMap.toLp` and
  the density statement near `SchwartzSpace/Basic.lean:1389` are the entry
  point.
* **Wiring**: the right-endpoint analogue of `brsANearLeftAt_le_pieces_int`,
  threading `ψ_{k+m} ∗ g` through `brs_5_9_near_covering_local` in place of
  `g`, and the final `k`-sum assembly against `sup_k ω`.

## Row 87, item 4: the transport layer is built

The remaining content of row 87 is
`Σ_j ‖ψ_j ∗ g‖_p^q ≲ ‖g‖_p^q`, and the plan is the band comparison: `𝓕ψ` is
supported in `1 ≤ |ξ| ≤ 4`, so `𝓕ψ_j` lives in `2^j ≤ |ξ| ≤ 2^{j+2}`, an
annulus met by exactly three dyadic bands, whence
`ψ_j ∗ f = Σ_{k=j−1}^{j+1} ψ_j ∗ Δ_k f` and Young + the (already proved)
`sum_lintegral_rpow_dyadic_lq_le_line` finish it.  The pieces landed:

* `lintegral_comp_mul_left_ennreal`, `lintegral_enorm_brsDilate` — the `L¹`
  norm is dilation invariant, so `lintegral_convolution_brsDilate_rpow_le`
  gives **Young's inequality with a scale-independent constant** `‖ψ‖₁`.
* `intDyadicBandpass_index_mem_Icc`, `sum_intDyadicBandpass_Icc_eq_one` —
  a frequency in `2^j ≤ ‖ξ‖ ≤ 2^{j+2}` is seen only by the bands
  `k = j−1, j, j+1`, and the resolution restricted to those three is `1`
  there.  Both come straight out of the repo's
  `intDyadicBandpass_norm_bounds_of_ne_zero` and
  `homogeneousDyadicResolution`.
* `brsLineIso` — **the identification of `ℝ` with `Euclidean 1` as a linear
  isometry**, not merely a measurable equivalence.  `brsLineEquiv` transports
  integrals but *cannot* transport the Fourier transform, which needs the inner
  product preserved.  The isometry is `(OrthonormalBasis.singleton (Fin 1) ℝ).repr`,
  it agrees with `brsLineEquiv.symm`, and
  `Real.fourier_comp_linearIsometry` then gives `fourier_brsLineIso` and
  `fourier_brsLineEquiv_symm`.
* `brsSchwartzToLine`, `brsSchwartzOfLine` — Schwartz functions move between
  the two models by `SchwartzMap.compCLMOfContinuousLinearEquiv`.
* `fourier_dilate_complex` — `𝓕(λF(λ·))(w) = 𝓕F(w/λ)` for complex-valued `F`
  (the earlier `brsFourier_dilate` was stated for real-valued profiles).
* `fourier_brsDyadicSchwartz`, `fourier_dyadicProjection_line` — the dyadic
  projection *is* the Fourier multiplier with symbol
  `intDyadicBandpassMultiplier`, read on the line.
* `norm_brsLineIso`, `fourier_dilate_support_annulus` — the annulus carried by
  `𝓕ψ_j`, in the exact form `sum_intDyadicBandpass_Icc_eq_one` consumes.

**Next**: assemble `ψ_j ∗ G = Σ_{k ∈ Icc (j−1) (j+1)} ψ_j ∗ Δ_k G` for Schwartz
`G` by comparing Fourier transforms and inverting; then Young and
`sum_lintegral_rpow_dyadic_lq_le_line`; then the density passage from Schwartz
`G` to the chain's continuous `g` (`SchwartzMap.toLp` and the density statement
near `SchwartzSpace/Basic.lean:1389`, plus Fatou).

## Row 87, item 4: the `k`-sum is proved for Schwartz data

`sum_lintegral_psiDilate_conv_le` is landed and axiom-clean: for
`C : lpCutoffs 1`, a Schwartz `ψ` whose `𝓕ψ` is supported in `1 ≤ |ξ| ≤ 4`,
and `1 < p`, `2 ≤ q`, `p ≤ q`,

    ∃ A ≠ ⊤, ∀ (J : Finset ℕ) (G : 𝓢(ℝ,ℂ)),
      Σ_{j∈J} (∫⁻ ‖ψ_j ∗ G‖ₑ^p)^{q/p} ≤ A (∫⁻ ‖G‖ₑ^p)^{q/p}.

The proof in four moves, each now a named lemma:

1. `brsSchwartzDilate_conv_eq_sum` — **the three-band decomposition**
   `ψ_j ∗ G = Σ_{k=j−1}^{j+1} ψ_j ∗ Δ_k G`.  Proved by comparing Fourier
   transforms and inverting: `𝓕(ψ_j ∗ G) = 𝓕ψ_j · 𝓕G`, each `𝓕(ψ_j ∗ Δ_k G) =
   𝓕ψ_j · band_k(iso ·) · 𝓕G`, and the symbols agree because
   `sum_intDyadicBandpass_Icc_eq_one` makes the three bands sum to `1` wherever
   `𝓕ψ_j ≠ 0` (`fourier_dilate_support_annulus`).  Off that set both sides
   vanish.  Supporting: `fourier_finset_sum` (additivity of `𝓕` over a finite
   sum of integrable functions, by induction on the `Finset` from
   `VectorFourier.fourierIntegral_add`).
2. `lintegral_conv_schwartzDilate_rpow_le` — **Young with a scale-independent
   constant**, from `lintegral_enorm_schwartzDilate` (dilation invariance of the
   `L¹` norm) and `lintegral_convolution_rpow_le_complex`.  The repo's Young
   inequality is stated for a *real* kernel; `ψ` is complex, so the complex
   version had to be restated (the proof is the same — the only real-specific
   step was `Complex.norm_real`).
3. `ennreal_rpow_finset_sum_le_card_mul` — `(∑a)^r ≤ card^{r−1} ∑a^r`, the
   `ENNReal` companion of `real_finset_rpow_sum_ge`, from
   `ENNReal.rpow_arith_mean_le_arith_mean_rpow`.  Note the file already had
   `ennreal_finset_rpow_sum_le`, which is the *opposite* inequality.
4. `sum_window_le_three_mul` — **bounded overlap**: each `k` lies in at most
   three windows `{j−1,j,j+1}`, so `Σ_j Σ_{k∈K_j} c k ≤ 3 Σ_{k∈⋃K_j} c k`.
   Proved by splitting the window sum into the three shifts `j ↦ j+i` and
   bounding each by the union (injectivity of the shift + monotonicity of a
   `Finset` sum in `ENNReal`).

Then `sum_lintegral_rpow_dyadic_lq_le_line` finishes it, after identifying
`brsLineProjection C k G` with the repo's projection composed with
`brsLineEquiv.symm` (`brsLineIso_eq_symm`).

**What is left in item 4** is only the density passage: the chain's `g` is
continuous and in `L^p`, not Schwartz.  Take Schwartz `G_n → g` in `L^p`, note
`ψ_j ∗ G_n → ψ_j ∗ g` in `L^p` by Young, and pass to the limit with Fatou on
the (finite) `j`-sum.

## Row 87, item 4 is COMPLETE: the `k`-sum holds for the chain's input class

`sum_eLpNorm_psiDilate_conv_le_bdd` is proved and axiom-clean: for
`C : lpCutoffs 1`, Schwartz `ψ` with `𝓕ψ` supported in `1 ≤ |ξ| ≤ 4`, and
`1 < p`, `2 ≤ q`, `p ≤ q`,

    ∃ A ≠ ⊤, ∀ (J : Finset ℕ) (g : ℝ → ℂ) (Cg : ℝ),
      Continuous g → (∀ z, ‖g z‖ ≤ Cg) →
      Σ_{j∈J} ‖ψ_j ∗ g‖_{L^p}^q ≤ A ‖g‖_{L^p}^q

— exactly the hypotheses the chain carries on its input (`prop54_…_interior`
assumes `Continuous g` *and* `∀ z, ‖g z‖ ≤ Cg`).

The density passage turned out to be much lighter than feared, because the
chain's `g` is **bounded**: the integrand `y ↦ K(y) g(x−y)` is dominated by
`‖g‖_∞ |K|`, so no Hölder argument is needed to split the convolution over a
difference (`convolution_sub_bdd`, `integrable_kernel_mul_bdd_shift`).  The
steps:

* `eLpNorm_ofReal_eq`, `eLpNorm_convolution_le` — Young's inequality translated
  into `eLpNorm`, which is the language in which Mathlib has Minkowski.
* `sum_eLpNorm_psiDilate_conv_schwartz` — the Schwartz statement, restated for
  `eLpNorm` (`(eLpNorm h P)^q = (∫⁻ ‖h‖ₑ^p)^{q/p}`).
* `MemLp.exist_eLpNorm_sub_le` (Mathlib) gives a *smooth compactly supported*
  `G` with `‖g − G‖_p ≤ ε`; such a `G` is bounded and is Schwartz through
  `HasCompactSupport.toSchwartzMap`.
* `eLpNorm_add_le` + `eLpNorm_convolution_le` bound each scale by
  `‖ψ_j ∗ G‖_p + ‖ψ‖₁ ε`, with `‖ψ‖₁` independent of `j`.
* `ENNReal.Lp_add_le` (Minkowski in `ℓ^q` over the finite `J`) separates the
  error, which contributes `(card J)^{1/q} ‖ψ‖₁ ε`.
* `ennreal_le_of_forall_add_mul` — a small limiting device: `X ≤ B + c·ε` for
  every `ε > 0` with `c` finite gives `X ≤ B`, by `ge_of_tendsto` along
  `ε = 1/(n+1)`.

Also landed: `continuous_kernel_conv_bdd` (the convolution of an integrable
kernel with a bounded continuous function is continuous, in the explicit
integral form the chain uses).

### What is left in row 87

Only **wiring**, no new analysis:

1. transcribe `sum_eLpNorm_psiDilate_conv_le_bdd` into the `∫⁻ ‖·‖ₑ^p` form the
   chain consumes (one `eLpNorm_ofReal_eq` rewrite);
2. feed `brs_5_9_near_covering_local` with `g := ψ_{k+m} ∗ g₀` in place of `g₀`,
   using `exists_brsCalderonFactorization` + `convolution_mul_dilate` to see the
   resolution piece as `υ_j ∗ ψ_j`, and `brs_conv_assoc'_int` for the
   reassociation;
3. the right-endpoint mirror of `brsANearLeftAt_le_pieces_int`;
4. re-run the `k`-sum of `prop54_brsRemTwoTwoLeft_interior` with the new
   per-piece bound, where the exponent is now `0` rather than negative and the
   sum is closed by step 1 instead of a geometric series.

## Row 87: the wiring identities

The convolution algebra needed to insert the factorization into the chain is
now in place, all axiom-clean:

* `brs_conv_assoc_mul` — `(a ∗ b) ∗ G = a ∗ (b ∗ G)` for the complex
  convolution, with `a` integrable **and bounded**, `b` integrable, `G` bounded
  continuous.
* `brs_conv_assoc_mul'` — the same with the sup bound on the **middle** factor
  instead of the outer one.  Both forms are needed because the truncated kernel
  `h_k` is integrable but *unbounded* (it is `|s|^{-1/2}` near the origin), so
  it can never be the factor carrying the bound.
* `convolution_mul_comm` — commutativity, from `convolution_flip` plus
  `(mul ℂ ℂ).flip = mul ℂ ℂ`.
* `conv_swap_middle` — `ψ_j ∗ (h_k ∗ G) = h_k ∗ (ψ_j ∗ G)`, obtained by
  associating both sides to `(ψ_j ∗ h_k) ∗ G` from opposite ends and joining
  with commutativity.
* `convolution_lsmul_eq_mul` — the chain writes `h_k ⋆[lsmul ℝ ℝ] G` (real
  kernel, complex values) while the factorization is stated with
  `⋆[mul ℂ ℂ]`; this identifies the two.
* `brsDilate_brsDilate`, `brsDilate_brsLPKernel`, `brsLPKernel_eq_conv_dilate` —
  the factorization at scale `0` dilates to every scale:
  `Ψ_j = υ_j ∗ ψ_j` where `Ψ_j = brsLPKernel p j`.
* `brs_piece_factor` — `Ψ_j ∗ G = υ_j ∗ (ψ_j ∗ G)`, the identity that lets
  `brs_5_9_near_covering_local` be applied with `ψ_j ∗ G` in place of `G`.
* `exists_bound_schwartz` — a Schwartz function is bounded (from `decay 0 0`),
  needed to feed `ψ_j` to the associativity lemmas.

Remaining: assemble these into the per-piece bound with the Littlewood--Paley
factor, mirror it on the right endpoint, and re-run the `k`-sum with
`sum_lintegral_psiDilate_conv_le_bdd` in place of the geometric series.

## Row 87: the near part is decomposed with the Littlewood--Paley factor

`brsANearLeftAt_le_pieces_lp` is proved and axiom-clean.  It is
`brsANearLeftAt_le_pieces_int` with each piece rewritten so that its **kernel**
is the compactly supported bump `brsDilate υ j` and its **input** is the
Littlewood--Paley piece:

    brsANearLeftAt 2^{-k} E g r ≤ ofReal (r^{-1/2}) *
      (brsNearPieceMax k (brsDilate pf (k+s)) g E r +
        Σ'_m brsNearPieceMax k (brsDilate υ (k+s+m)) (brsLPInput S (k+s+m) g) E r)

The chain of rewrites behind it:

* `brs_piece_eq_lp` — `∫ Ψ_j · (h_k ∗ G) = ∫ (h_k ∗ υ_j) · (ψ_j ∗ G)`.  Proved
  by `brs_piece_factor` (to split `Ψ_j = υ_j ∗ ψ_j`), then `conv_swap_middle`
  (to move `ψ_j` past `h_k`), then `brs_piece_eq_int` (to put `h_k` back on the
  bump).  `norm_kernel_conv_bdd_le` supplies the sup bound on `ψ_j ∗ G` that
  the last step needs.
* `brsLPInput S j g := brsRefl (ψ_j ∗ brsRefl g)` — the chain's maximal
  functions test against `brsRefl g`, so the Littlewood--Paley piece has to be
  packaged with a reflection; `brsRefl_brsRefl` and `brsRefl_brsLPInput` undo
  it.
* `continuous_brsLPInput`, `norm_brsLPInput_le` — it is bounded and continuous,
  so it is an admissible input for `brs_5_9_near_covering_local`.
* `lintegral_enorm_rpow_neg`, `lintegral_enorm_rpow_brsRefl`,
  `lintegral_enorm_brsLPInput_eq` — its `L^p` norm is that of `ψ_j ∗ g`, so the
  `k`-sum bound `sum_lintegral_psiDilate_conv_le_bdd` applies to it verbatim.

Remaining: bound each `brsNearPieceMax k (brsDilate υ j) (brsLPInput S j g) E`
by `brs_5_9_near_covering_local`, sum in `k` with
`sum_lintegral_psiDilate_conv_le_bdd`, and mirror the whole thing on the right
endpoint.

## Row 87: the near part is aggregated with the Littlewood--Paley factor

`brsNear_aggregate_lp` is proved and axiom-clean.  It is `brsNear_aggregate`
with the `(m, k)`-family replaced by `brsNearFamilyLP`, whose `m ≥ 1` entries
are `brsNearMax k (k+1) (brsDilate υ (k+1+s+m)) (brsLPInput S (k+1+s+m) g) E`:
the compactly supported bump as kernel, the Littlewood--Paley piece as input.

Chain: `brsANearLeftAt_le_pieces_lp` → `brsANearWindow_le_tsum_lp` (window
form) → `brsANearWindow_le_tsum_family_lp` (packed as a family) →
`brsNear_aggregate_lp` (through the repo's `window_double_sum_le`, unchanged).
Supporting: `brsNearFamilyLP` with its `_zero`, `_succ`,
`_eq_zero_of_notMem` and `measurable_` lemmas.

The remaining step of row 87 is the `m`- and `k`-summation of

    Σ'_m (Σ'_k ∫⁻ brsNearFamilyLP … m k r ^ q · r dr)^{1/q},

where each `m ≥ 1` term is bounded by `brs_5_9_near_covering_local` with the
*localized* covering number, so that the `k`-exponent is `0` and the `k`-sum is
closed by `sum_lintegral_psiDilate_conv_le_bdd` applied to
`lintegral_enorm_brsLPInput_eq` — instead of by a geometric series.  Then the
same for the right endpoint.

## Row 87: the `k`-sum at the endpoint is proved

`tsum_brsNearMax_lp_le` is landed and axiom-clean.  For a fixed offset `a ≥ 4`,

    Σ'_k ∫⁻ brsNearMax k (k+1) (brsDilate υ (k+a)) (brsLPInput S (k+a) g) E ^q · r dr
      ≤ (2^{|1-q/2|} · N_loc · (KC · (2^{-a})^{1/r-1/2})^q · 9^{q/p})
          · A₀ · ‖ǧ‖_p^q

whenever `q ≤ 2p`.  This is the step the whole endpoint programme was for.

The mechanism, isolated in `brs_endpoint_exponent_sum` and
`brs_endpoint_factor_le`: the radial weight `(2^{-k})^{1-q/2}` and the kernel
factor `(2^{-(k+a)})^{q(1/r-1/2)}` combine, *using the Hölder relation
`1/p + 1/r = 1 + 1/q`*, into

    (2^{-k})^{(1-q/2) + q(1/r-1/2)} = (2^{-k})^{2 - q/p},

times a factor depending only on `a`.  The exponent `2 - q/p` is `≥ 0` exactly
when `q ≤ 2p` and is **`0` at the endpoint** — so the `k`-sum has no geometric
decay left and is closed instead by `tsum_lintegral_psiDilate_conv_le_bdd`,
the Littlewood--Paley bound along the arithmetic progression of scales
`j = k + a`.  `lintegral_enorm_brsLPInput_eq` identifies the `L^p` norm of the
piece with that of `ψ_{k+a} ∗ ǧ`.

Also landed: `brs_five_two_pow_le` (the separation hypothesis
`5·2^{-(k+a)} ≤ 2^{-(k+1)}` of (5.9), which holds uniformly in `k` once
`a ≥ 4`), and `tsum_lintegral_psiDilate_conv_le_bdd` (the finite-scale
Littlewood--Paley bound extended to the infinite sum along `j = k + offset`,
via `ENNReal.tsum_eq_iSup_sum` and `Finset.sum_image`).

Remaining for row 87: sum over `m` (the `m`-decay is
`(2^{-a})^{q(1/r-1/2)}` against the growth of `N_loc`, i.e. the existing
`brsSumExpM < 0` condition), then the far part and the right-endpoint mirror,
then assemble.

## Row 87: the `m`-sum apparatus

At the endpoint the `k`-sum is closed by Littlewood--Paley, not by a geometric
series, so the double geometric sum `tsum_tsum_ofReal_geometric_rpow` used in
the interior case no longer applies — the `m`-sum is a *single* geometric
series.  Landed:

* `rpow_inv_of_le_mul_rpow` — from `X ≤ K · G^q` to `X^{1/q} ≤ K^{1/q} · G`,
  the step that turns the `k`-sum bound into a term of the `m`-sum.
* `tsum_m_geometric_le` — `Σ'_n T n ≤ ofReal(c/(1-2^b)) · G` from
  `T n ≤ ofReal(c·2^{bn}) · G`, `b < 0`.
* `tsum_m_geometric_le'` — the same with the constant kept as an `ENNReal`
  factor, which is the form needed here because the endpoint constants (the
  Littlewood--Paley constant `A₀`, the factor `9^{q/p}`) are `ENNReal`s and not
  coercions of reals.

The decay in `m` is unchanged from the interior case: with `a = 4 + m` the
`m`-term carries `2^{a(γ/q - (1/r-1/2))}`, so the series converges exactly
under `brsSumExpM γ (1/r-1/2) q < 0`.

## Row 87: the endpoint `m`-sum is assembled

The constant chase from the `k`-sum bound to the geometric `m`-sum is done:

* `endpoint_const_le` — the constant produced at offset `a`,
  `E₁ · N_loc · (KC·2^{-aS})^q · B`, with `N_loc ≤ Cγ 2^{γa}`, has `q`-th root
  at most `(E₁ Cγ KC^q)^{1/q} · 2^{a(γ-Sq)/q} · B^{1/q}`.
* `rpow_div_eq_rpow_inv_rpow`, `endpoint_term_le` — glue: taking the `q`-th
  root of `T ≤ (…) · X^{q/p}` gives `T^{1/q} ≤ (…)^{1/q} · X^{1/p}`, with the
  `a`-dependence isolated as `2^{a(γ-Sq)/q}`.
* `two_rpow_mul_add_four`, `tsum_endpoint_m_le` — splitting
  `2^{b(4+n)} = 2^{4b}·2^{bn}` and summing the geometric series in `n`, which
  converges exactly when `γ < Sq`, i.e. `brsSumExpM γ S q < 0` — the same
  condition as the interior case.

So the near part of `R₂^-` at the endpoint is now reduced to: choosing the
Calderón profile and the factorization (`exists_brsCalderonFactorization`),
supplying the localized covering bound `N_loc ≤ Cγ 2^{γa}`, and reading off the
`m = 0` low-frequency term (which is `brs_5_9_near_low_covering_local`, already
proved, and carries no Littlewood--Paley factor).

## Row 87: correction — the `m = 0` term is NOT a covering-number estimate

Checked against the arXiv source (the paragraph introducing `𝒜_{k,0}`).  BRS
write:

> Consider first the `𝒜_{k,0}`.  Note that `h_k ∗ u_k` is supported in
> `[-2^{-k-10}, 2^{-k-20}]` and `‖h_k ∗ u_k‖_∞ ≤ ‖h_k‖₁‖u_k‖_∞ ≲ 2^{k/2}`.
> **Thus, one can argue exactly as for the `ℬ_k` terms** and deduce
> `‖sup_{1≤t≤2} Σ_k |𝒜_{k,0}f₀|‖_{L^q(r dr)} ≲ ‖f₀‖_{L^p(s ds)}`  (5.8)
> for `1 < p < ∞` and `q ≤ 2p`.

So the low-frequency term of the near part is **not** estimated through
`ω_m^{p,q}(E,k)` at all — it has no covering numbers, no supremum restricted to
`E`, and the `k`-sum sits *inside* the supremum.  This matters at the endpoint:

* Through the covering-number route the `m = 0` term would carry the same
  `k`-exponent `2 - q/p` as the high-frequency terms, which is `0` at `q = 2p`;
  the `k`-sum then diverges, since its input is `g` itself and carries no
  Littlewood--Paley factor to close the sum with.  Using the *global* covering
  number instead gives `brsSumExpK = β - 2 + q/p`, which at `q = 2p` is `β ≥ 0`
  — also divergent.  So neither covering-number route works for `m = 0`.
* The `ℬ_k` route is what works, and it is **already proved in this file**:
  row 80 is `complete`, and `prop56_brsBFarLeft_endpoint` /
  `prop56_brsBFarRight_endpoint` give the `L^p → L^{2p}` bound for exactly that
  kind of term, by pointwise domination
  (`brsBFarLeft_le_brsRemainderTwo`) followed by row 45's
  `prop43_brsRemainderTwo_endpoint`.

**Consequence for the assembly.**  `brsNearFamilyLP` should not send its `m = 0`
entry through `brs_5_9_near_low_covering_local` at the endpoint.  The `m = 0`
piece must instead be pulled out and bounded like `ℬ_k`, i.e. by a pointwise
domination

    Σ_k (low-frequency near piece at scale k) ≤ C · brsRemainderTwo (absProfile ǧ)

after which `prop43_brsRemainderTwo_endpoint` applies.  The domination is the
same computation as for `ℬ_k`: the kernel `h_{k+1} ∗ pf_{k+4}` has sup norm
`≲ 2^{k/2}` and support of length `≲ 2^{-k}`, so

    |h_{k+1} ∗ pf_{k+4} ∗ ǧ(x)| ≲ 2^{k/2} ∫_{|y| ≲ 2^{-k}} |ǧ(x-y)| dy,

and summing the geometric series in `k` recovers `∫ |y|^{-1/2}|ǧ(x-y)| dy`,
which is the kernel of `brsRemainderTwo`.

The `m ≥ 1` terms are unaffected: `tsum_endpoint_m_le` together with
`tsum_brsNearMax_lp_le` handles them, and their `k`-sum is closed by
Littlewood--Paley as designed.

## Row 87: a design fork at the `m = 0` term (2026-09-08)

Landed first: `integral_brsTruncKernel` (`‖h_k‖₁ = 2·2^{-k/2}`) and
`abs_brsTruncConvReal_le` (`‖h_k ∗ ψ‖_∞ ≤ ‖ψ‖_∞·2·2^{-k/2}`), which is the
`2^{k/2}` bound BRS quote for `𝒜_{k,0}`.

Then, working out the `ℬ_k`-style domination for `m = 0`, a real obstruction
appeared.  Recording it precisely, because it decides the shape of the rest.

**The obstruction.**  `brsRemainderTwo f₀ r = ⨆_{t ∈ [1,2] ∩ [3r/2,∞)}
ofReal(r⁻¹‖∫_{t-r}^{t+r} f₀‖)`, so a domination by it can only see `g` on
`[t-r, t+r]` for `t` in `[1,2]`.  The `ℬ_k` terms integrate `g` over `[t-r, t]`,
which sits inside that interval — which is exactly why
`brsBFarLeft_le_brsRemainderTwo` goes through.  The near piece instead samples
`g` at `t - r + y` over the support of `K = h_{k+1} ∗ pf_{k+4}`, i.e. slightly
*below* `t - r`.  With a bump supported in `[-1,1]` the overhang is
`2^{-(k+4)} ≈ r/16`, and at the edge case `t = 1` there is no admissible `t'`
whose interval `[t'-r, t'+r]` covers it.  **With the Calderón profile the
problem is worse**: `p = 𝓕⁻χ` is Schwartz, not compactly supported, so `K` has
full support and the containment argument is unavailable outright.

**Two ways out, neither cheap.**

1. *Maximal-function domination for `m = 0`.*  Keep the Calderón profile.
   `|K(y)| ≲ 2^{k/2}(1+2^k|y|)^{-M}`, so `|K ∗ g|` is dominated by the
   Hardy--Littlewood maximal function of `g` at scale `2^{-k}`; the `ℬ_k` route
   then runs against `M g` instead of against `brsRemainderTwo`.  The repo has
   `Auto.HardyLittlewoodMaximal`, so the maximal bound itself is available, but
   the `L^p → L^{2p}` endpoint estimate would have to be redone for it.

2. *Keep the compactly supported profile and pay with almost-orthogonality.*
   Use the repo's existing telescoping resolution (compactly supported `φ`) for
   **both** the low and the high pieces.  Then `m = 0` is exactly the situation
   `brsBFarLeft_le_brsRemainderTwo` handles (kernel supported in `[0, r]` if
   `φ` is supported in `[0,1]`, so `t-r+y ∈ [t-r, t]`), and row 45 applies
   unchanged.  The price is on the high pieces: `Ψ^c_j` is no longer exactly
   `υ_j ∗ ψ_j`, so one needs
   `‖Ψ^c_j ∗ Θ_i ∗ g‖_p ≲ 2^{-N|i-j|}‖Θ_i ∗ g‖_p` (from the vanishing moments
   of `Ψ^c` against the band-limitation of `Θ_i`) followed by a Schur/Young
   estimate `Σ_j (Σ_i 2^{-N|i-j|}a_i)^q ≲ Σ_i a_i^q`.

Route 2 leaves everything already proved for the `m ≥ 1` terms intact except
for replacing the *exact* factorization by an almost-orthogonal one; route 1
leaves the factorization intact but needs a new endpoint estimate.  Route 2
looks closer to BRS, who keep `u, υ₁, ψ₁` all compactly supported.

## Row 87: the `m = 0` piece, reduced to an interval average

Route 2 is under way (no objection raised to the fork; it is the branch closer
to BRS).  Landed, and route-independent:

* `integral_brsTruncKernel` — `‖h_k‖₁ = 2·2^{-k/2}`.
* `abs_brsTruncConvReal_le` — `‖h_k ∗ ψ‖_∞ ≤ ‖ψ‖_∞ · 2·2^{-k/2}`, the `2^{k/2}`
  bound BRS quote for `𝒜_{k,0}` (with `ψ = υ_j`, `‖υ_j‖_∞ ≤ 2^j Mu`).
* `norm_integral_truncConvDilate_mul_le` — the piece is at most
  `‖h_k ∗ υ_j‖_∞` times `∫_{Ioc(-2^{-j}, 2^{-k}+2^{-j})} ‖G(x-y)‖ dy`, using
  `brsTruncConvReal_eq_zero` for the support and
  `Measure.integrableOn_of_bounded` for the majorant.
* `setIntegral_norm_shift`, `norm_integral_truncConvDilate_mul_le_interval` —
  undoing the reflection `s = x - y` (via
  `intervalIntegral.integral_comp_sub_left`) puts it in the form

      ‖piece‖ ≤ C · ∫_{x - (2^{-k}+2^{-j})}^{x + 2^{-j}} ‖G‖,

  an average over an interval essentially to the *left* of `x = t - r`, of
  length `≈ 2^{-k} ≈ r`.  This is exactly the shape `brsRemainderTwo` compares
  with, modulo the `2^{-j}` overhang on the right of `x` and the requirement
  that the interval fit inside `[t' - r, t' + r]` for an admissible `t'`.

## Row 87: the fork is resolved — stay on route 1, shift the truncation index

Working the containment out quantitatively resolves the fork in favour of
**route 1** (keep the Calderón profile, so all the `m ≥ 1` work stands), with a
concrete fix for the `m = 0` term.

**The arithmetic.**  `brsRemainderTwo_le_tail` needs `s ≥ 1/3` for
`s ∈ [t-r, t+r]`, which it gets from `t ≥ 3r/2` and `t ≥ 1`:
`t - r ≥ t - 2t/3 = t/3 ≥ 1/3`.  For a *wider* interval `[t - c r, t + r]` the
same computation gives `t - c r ≥ t(1 - 2c/3)`, which is bounded below by a
positive constant **exactly when `c < 3/2`**.  So the layer-cake argument of
row 45 tolerates a widening factor up to `3/2`, no more.

**What the `m = 0` piece needs.**  Its interval is
`[t - r - R - δ, t - r + δ]` with `R = 2^{-kt}` and `δ = 2^{-j}`, i.e.
`c = 1 + R/r + δ/r`.  The chain currently takes `kt = kw + 1`, so `R ≈ r`,
giving `c ≈ 2.1 > 3/2` — which is precisely why the containment failed.

**The fix.**  `brs_5_9_near_covering_local` only requires `hkt : kw + 1 ≤ kt`,
so the truncation index is free to be taken *finer*.  With `kt = kw + 3` we get
`R ≈ r/8` and `δ ≈ r/64`, hence `c ≈ 1.14 < 3/2`, and

    [t - r - R - δ, t - r + δ] ⊆ [t - 1.14 r, t] ⊆ [t - 1.5 r, t + r],

with every point `≥ 0.24 t ≥ 0.24`.  The row-45 layer-cake argument then goes
through for the widened object with the constant `(1 - 2c/3)^{-(d-1)}` in place
of `3^{d-1}`.

**Consequences for the assembly.**  Moving the truncation from `kw + 1` to
`kw + 3` changes the near/far cut scale from `2^{-(k+1)}` to `2^{-(k+3)}`, so
the far part must be re-run at the new cut.  That is available: `brsBFarLeftAt`
already carries the cut scale as a parameter, and row 80's endpoint estimate is
stated for it.  Concretely the remaining steps are:

1. a widened remainder `brsRemTwoWide c f₀ r := ⨆_t ofReal(r⁻¹‖∫_{t-cr}^{t+r} f₀‖)`
   with `c < 3/2`, and the analogue of `brsRemainderTwo_le_tail` /
   `measure_brsRemainderTwo_gt_le` / `prop43_brsRemainderTwo_endpoint` for it
   (the proofs are the existing ones with `3^{d-1}` replaced by
   `(1 - 2c/3)^{-(d-1)}`);
2. the `m = 0` domination, now a clean containment via
   `norm_integral_truncConvDilate_mul_le_interval`;
3. re-running the near/far split and the `m ≥ 1` chain at `kt = kw + 3`
   (only the numerals `k+1` change; `brs_5_9_near_covering_local`,
   `tsum_brsNearMax_lp_le` and `tsum_endpoint_m_le` are all stated for general
   `kw, kt, a`);
4. the right-endpoint mirror, and assembly.

No new analysis is needed for any of these — the deep step (closing the `k`-sum
by Littlewood--Paley) is done.

## Row 87: the widened remainder is in place

`brsRemTwoWide c f₀ r := ⨆_{t ∈ [1,2] ∩ [3r/2,∞)} ofReal(r⁻¹‖∫_{t-cr}^{t+r} f₀‖)`
is defined, and `brsRemTwoWide_le_tail` is proved: for `0 ≤ c < 3/2`,

    brsRemTwoWide c (absProfile f₀) r
      ≤ ofReal((1-2c/3)^{-(d-1)} r⁻¹) · brsTail (brsWeightMeasure d) ‖f₀‖ lam
        + ofReal((1+c) lam).

It is `brsRemainderTwo_le_tail` with `3^{d-1}` replaced by `(1-2c/3)^{-(d-1)}`
and `2 lam` by `(1+c) lam`; the only substantive change is the lower bound on
the averaging interval, `t - c r ≥ t(1 - 2c/3) ≥ 1 - 2c/3 > 0`, which is where
`c < 3/2` enters.

Next: the level-set bound (`measure_brsRemainderTwo_gt_le`) and the endpoint
estimate (`prop43_brsRemainderTwo_endpoint`) for `brsRemTwoWide`, both of which
are the existing proofs with the two constants substituted.

## Row 87: the widened level-set bound, and a simplification of the plan

`measure_brsRemTwoWide_gt_le` is proved: for `0 ≤ c < 3/2`,

    brsWeightMeasure d {r | ofReal u < brsRemTwoWide c (absProfile f₀) r}
      ≤ ofReal((2 (1-2c/3)^{-(d-1)} / u)^d / d)
          · brsTail (brsWeightMeasure d) ‖f₀‖ (u/(2(1+c)))^d.

It is `measure_brsRemainderTwo_gt_le` with `3^{d-1} → (1-2c/3)^{-(d-1)}` and the
layer-cake cut `u/4 → u/(2(1+c))`, the latter chosen so that the `(1+c)·lam`
term of `brsRemTwoWide_le_tail` is again exactly `u/2`.

**Plan simplification.**  It is *not* necessary to duplicate the whole
Proposition 4.3 chain for `brsRemTwoWide` — that would require
`brsRemTwoWide_eq_rat_iSup`, `measurable_brsRemTwoWide` and
`brsRemTwoWide_le_local` as well.  Instead run the layer cake directly on the
`m = 0` maximal function itself, which the repo already knows is measurable
(`measurable_brsNearMax`):

* the layer-cake step `lintegral_ennreal_rpow_eq_meas_lt` needs measurability of
  the *function*, which `measurable_brsNearMax` supplies;
* the level-set step needs only `measure_mono`, which does **not** require the
  level set to be measurable: from the pointwise domination
  `brsNearMax … r ≤ ofReal C · brsRemTwoWide c (absProfile g) r` one gets
  `{r | ofReal u < brsNearMax … r} ⊆ {r | ofReal (u/C) < brsRemTwoWide c … r}`,
  and `measure_brsRemTwoWide_gt_le` at height `u/C` finishes;
* the remaining ingredient is finiteness of `brsNearMax … r`, which follows
  from `norm_integral_truncConvDilate_mul_le_interval`.

So `brsRemTwoWide` is needed only as an intermediate in the level-set estimate,
never as a measurable object in its own right, and the two lemmas already
proved about it are all that is required of it.

## Row 87: the `m = 0` term, resolved (2026-09-06)

Two corrections to the earlier plan, both from computing the support geometry
of the reflected piece carefully.

**1. The overhang is on the *right*, and `kt = kw + 1` is fine.**  The piece of
`brsNearFullMax` is `brsRefl(h_kt ∗ υ_j ∗ ǧ)(t-r)`.  Undoing *both* reflections
(`norm_low_piece_le_interval`) shows it samples `g` on

    [t - r - 2^{-j}, t - r + 2^{-kt} + 2^{-j}],

so the overhang to the *left* of `t - r` is only `2^{-j}`, not `2^{-kt}+2^{-j}`
as the earlier note said.  With `kt = k+1` and `j = k+1+s`, `r ∈ I_k` gives
`2^{-kt} ≤ r` and `2^{-j} ≤ 2^{-s} r ≤ r/8` for `s ≥ 3`, hence

    [t - r - 2^{-j}, t - r + 2^{-kt} + 2^{-j}] ⊆ [t - (9/8) r, t + r],

and `9/8 < 3/2`.  **The chain does not have to be re-run at `kt = kw + 3`.**
Take `s = 3` throughout, so that the `m`-th high-frequency term has offset
`a = 4 + m`, exactly the shape `tsum_endpoint_m_le` expects.

**2. The `t ≥ 3r/2` constraint must be kept.**  `brsNearMax` is built on
`brsNearFullMax`, whose supremum runs over all of `E`; the constraint
`t ≥ 3r/2` that `brsANearLeftAt` carries is dropped when passing to it.  For
the covering-number estimates that is harmless, but for the `m = 0` term it is
fatal: on `I_0` (where `r` may be as large as `4/3`) a `t ∈ [1,2]` with
`t < 3r/2` puts the averaging interval across the origin, and no widening
`c < 3/2` can repair that.  So the `m = 0` term uses

    brsNearMaxP kw kt Ψ g E r
      := 1_{I_kw}(r) · ofReal(r^{-1/2}) · brsNearPieceMax kt Ψ g E r,

which keeps the constraint, and `brsNearMaxP_low_le_brsRemTwoWide` gives, for
every `k` and every `r`,

    brsNearMaxP k (k+1) (brsDilate pf (k+1+s)) g E r
      ≤ ofReal(‖pf‖_∞ · 2^{s+2}) · brsRemTwoWide (9/8) (absProfile g) r.

The constant is `k`-free because `r^{1/2} ≤ 2^{1/2}·2^{-k/2}` on `I_k`
(`rpow_le_of_mem_brsWindowExt`) exactly cancels the kernel factor
`2^{j}·2·2^{-(k+1)/2}` — the same cancellation as for the `ℬ_k` terms.

**3. `brsRemTwoWide` *is* needed as a measurable object after all.**  The
earlier note said the layer cake could run on the `m = 0` maximal function
itself; that only works when that function is measurable, and
`brsNearMaxP` is not (its index set `E ∩ [3r/2,∞)` moves with `r`, and `E` is
arbitrary).  Proving `measurable_brsRemTwoWide` is cheap — the rational-supremum
argument of `measurable_brsRemainderTwo` verbatim, with
`continuous_wide_window_integral` in place of `continuous_window_integral` —
and `brsRemTwoWide_ne_top` follows from boundedness of a continuous `f₀` on the
compact `[1 - c r, 2 + r]`.  With those,

* `prop43_dominated_endpoint` — the layer cake for *any* measurable, finite `M`
  with `M ≤ ofReal C₀ · brsRemTwoWide c (absProfile f₀)`, obtained from
  `prop43_brsRemainderTwo_endpoint` by replacing `3^{d-1}` with
  `(1-2c/3)^{-(d-1)}` and `4` with `2 C₀ (1+c)`;
* `endpoint_of_le_brsRemTwoWide` — the `d = 2` corollary, with **no** hypothesis
  on `M` beyond the domination, since `ofReal C₀ · brsRemTwoWide` is itself an
  admissible `M` and `lintegral_mono` needs no measurability.

**Norms.**  The endpoint statement for row 87 uses the *weighted* right-hand
side `(∫⁻ s, ofReal s · ‖g s‖ₑ^p)^{1/p}`, matching `prop56_brsBFarLeft_endpoint`
(row 80).  The `m ≥ 1` chain produces the *unweighted* `(∫⁻ ‖g‖ₑ^p)^{1/p}`; the
two are reconciled by localizing `g` with a smooth cutoff supported in
`[1/4, 3]` before running the decomposition — legitimate because
`brsRemTwoTwoLeft E g r` only sees `g` on `[1/3, 2]` — after which
`‖χ g‖_p^p ≤ 4 ∫ s |g|^p`.

## Row 87: the `m = 0` term needs the Schwartz tail after all (2026-09-06)

Assembling the endpoint exposed a genuine gap in the plan above.
`brsNearMaxP_low_le_brsRemTwoWide` requires `tsupport pf ⊆ closedBall 0 1`, but
the profile that makes the `m ≥ 1` factorization *exact* is the Calderón
profile `pf = 𝓕⁻χ`, which is Schwartz, **not** compactly supported.  The two
requirements are incompatible:

* the repo's Littlewood--Paley bound (`sum_lintegral_psiDilate_conv_le_bdd`)
  needs `𝓕ψ` supported in an annulus;
* `LPKernel pf 0 = υ ∗ ψ` with `𝓕ψ` annulus-supported forces `𝓕pf` to be a
  cutoff, hence `pf` Schwartz;
* BRS's own (5.7) takes `u, υ₁, ψ₁` all in `C_c^∞`, which means their
  Littlewood--Paley step is the *general* (non-band-limited) one.

So either the general Littlewood--Paley theorem is proved (route 2), or the
Schwartz tail of the low-frequency term is estimated directly.  The second is
much cheaper, because the tail is summable against the layer cake:

**The tail estimate.**  `|h_{k+1} ∗ pf_{k+4}(v)| ≲ 2^{k/2}(1 + 2^k|v|)^{-2}`
(the `2^{-2}` decay is all that is needed).  Splitting `|v|` dyadically,

    r^{-1/2}|h_{k+1} ∗ pf_{k+4} ∗ ǧ(t-r)| ≲ Σ_{n ≥ 0} 2^{-n} · avg_{2^{n+2} r}(t-r),

where `avg_ρ(x)` is the mean of `|g|` over `[x-ρ, x+ρ]`.  Since `t - r ∈ [1/3,2]`
this is at most `brsRemTwoCent g (2^{n+2} r)`, where

    brsRemTwoCent f₀ ρ := ⨆_{x ∈ [1/3,2]} ofReal(ρ⁻¹ ‖∫_{x-ρ}^{x+ρ} f₀‖),

and rescaling `ρ = 2^{n+2} r` in `L^q(r dr)` costs only `2^{-2(n+2)/q} ≤ 1`, so
the `n`-sum converges.

**Why `brsRemTwoCent` still satisfies the layer cake.**  The constraint
`t ≥ 3r/2` was only ever used to keep the averaging interval away from the
origin.  Once the profile is *localized* (which BRS also do: "without loss of
generality `f₀` is supported on `[1/3,2]`"), the integrand vanishes for
`s < 1/4` and the bound `1 ≤ (4s)^{d-1}` is available for free on the support.
So the layer cake works for centers anywhere in `[1/3,2]` and for intervals of
any width — the restriction `c < 3/2` of `brsRemTwoWide` disappears.

**Consequences.**  `brsRemTwoWide` and `brsNearMaxP_low_le_brsRemTwoWide` remain
correct and are kept, but the endpoint assembly uses `brsRemTwoCent` instead,
together with:

* a decay bound for the Calderón profile (`exists_brsCalderonProfile`
  strengthened to return `∃ Cp, ∀ x, x² |p x| ≤ Cp`, available because the
  profile is built as `𝓕⁻` of a `SchwartzMap`);
* an *abstract* layer-cake lemma taking the level-set bound as a hypothesis, so
  that the Proposition 4.3 argument is written once and used for both
  `brsRemTwoWide` and `brsRemTwoCent`.
