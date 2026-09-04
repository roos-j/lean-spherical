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
