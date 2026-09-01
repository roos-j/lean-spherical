# BRRS formalization instructions

Work only in the authorized BRRS formalization components unless an existing
file must be adjusted to preserve a compiling import graph:

- `LeanSpherical/Auto/ConvexDuality.lean`
- `LeanSpherical/Auto/Spherical/LegendreAssouad.lean`
- `LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
- `LeanSpherical.lean` only for necessary imports

## Required logically ordered workflow

Use Beltran--Roos--Rutar--Seeger, *A fractal local smoothing problem for the
wave equation* (arXiv:2501.12805 / BLMS 57 (2025)), as the mathematical
reference for this formalization.  Order the work by the actual logical
dependencies of the argument, not by the paper's page or section order.  In
particular, prove prerequisites before every result which uses them; do not
accumulate unrelated auxiliary lemmas.  The Section 3 lower-bound and Section 5 upper-bound
arguments are logically disjoint after their shared prerequisites, so they
may be formalized concurrently; this permission does not relax the required
strict forward reasoning within either stream.

Treat the proof as a dependency DAG, not as a numbered reading list.  Source
labels and section headings identify statements but never determine which
statement comes next.  Render a strict forward topological order in the
ledger: a row may depend only on earlier rows, and genuinely independent rows
must be marked as such rather than being made to look serial merely because
of their order in the paper.  At a join, every incoming branch must be closed
before the dependent statement is started.  Such a dependency display does
not authorize extra concurrency inside one proof stream: retain the one-active
item rule there.

An existing declaration marked `complete with qualification` in the ledger is
evidence of a related closed theorem, not a licence to bypass an incomplete
literal source row. Do not use it to start a successor in the source-proof
DAG until that source prerequisite is closed, or the ledger explicitly
records a mathematically equivalent replacement and its proof.

At any time, select a concrete next logical item from the proof: a named
theorem, proposition, lemma, or substantial labelled displayed step whose
prerequisites have all been completed.  Formalize that item faithfully,
compile it, and only then start a result depending on it.  In particular:

1. Complete the Section 2 Theorem 1.2 development before relying on its
   Legendre--Assouad consequences.
2. For Theorem 1.1, preserve strict dependency order within each proof
   stream: Section 3's lower-bound test-function construction and Section 5's
   Proposition 5.1 upper-bound argument may be worked in parallel, but a
   numbered step may begin only after the numbered and unnumbered facts it
   actually uses are complete.  The fixed-time/interpolation step begins only
   after its logical inputs are complete.
3. Do not treat a representation identity, a local kernel estimate, an
   interface theorem, or a conditional wrapper as completion of a paper step
   unless it proves the corresponding source statement with all of its
   hypotheses and conclusion.
4. Within a single proof stream, do not work on several incomplete branches
   at once.  The only permitted parallelism is the disjoint Section 3
   lower-bound stream and Section 5 upper-bound stream described above.  A
   supporting lemma may be introduced only when it is immediately required to
   finish that stream's selected source item.

## Milestone reporting

Maintain `automation/Status-BRRS.md` as a dependency-ordered status ledger,
not as a narrative progress summary.  It must contain exactly one table row for
every numbered theorem, proposition, corollary, lemma, and displayed equation
in the proofs in scope (currently the proofs of BRRS Theorems 1.2 and 1.1).
Add a clearly labelled row for an unnumbered prerequisite whenever doing so is
needed to make the forward dependency order unambiguous.
List those rows in strict forward logical order: every row must precede each
row which depends on it, even when that differs from the paper's order.
Group independent branches visibly, but do not use section order to conceal a
dependency or silently collapse a sequence such as (3.4)--(3.7) into one row.
Use explicit dependency layers or an equivalently unambiguous DAG layout when
more than one branch is available. If a named result and a displayed equation
are literally the same assertion (as Proposition 5.1 and (5.1) are), retain
one row for each label but put them in the same layer and state explicitly
that there is no proof-dependency edge between them.

Each row must include all of the following:

- the exact source label and a short description of the source statement;
- a precise status (`not started`, `in progress`, `complete`, or `complete
  with qualification`);
- an ISO 8601 Eastern-time timestamp recording when that status last changed;
- the Lean declaration(s) which establish it, or the exact missing
  dependency if it is incomplete; and
- any qualification which prevents the Lean result from being the literal
  unqualified paper statement.

Update the applicable row immediately when work changes its status, before
starting the next source item.  An initial ledger entry may record the time
of the audit which established the current status; afterwards, retain the
previous timestamp until that row's status actually changes.  Record a fresh
direct module compilation check in the verification section whenever a row is
advanced.

A milestone is reached only when a significant statement or step from the
original paper has a complete Lean proof.  Do not label definitions, partial
estimates, source-side bridges, unproved `Prop` statements, or theorem
wrappers as completed paper milestones.  A helper may be mentioned only in
the evidence column for the source item it immediately helps close.

The main objectives, in logical dependency order, are:

1. Complete the literal BRRS Theorem 1.2 in `LegendreAssouad.lean`, including
   Rutar's open-interval realization theorem and the required endpoint repair.
2. Complete the literal BRRS Theorem 1.1 in `BRRS.lean`, including the sharp
   all-dimension radial estimate and its sharpness statement.

Proof standards:

- Do not use `sorry`, `admit`, new axioms, or a theorem wrapper that merely
  assumes the result being claimed.
- Preserve existing main results and namespace conventions.
- Keep reusable convex-analysis facts in `Auto.ConvexDuality`.
- Keep Rutar/Legendre--Assouad material in `Auto.Spherical.LegendreAssouad`.
- Keep BRRS analytic material in
  `Auto.Spherical.FractalDilations.BRRS`.
- Reuse existing repository developments only when their hypotheses and
  conclusions genuinely match; do not present a weaker MSS or auxiliary
  estimate as the sharp BRRS theorem.
- Compile each edited module and the repository entry point before reporting
  completion.

Current status must be read from `automation/Status-BRRS.md`, whose entries
are the authoritative dependency-by-dependency record.  Re-check that file
against the actual declarations and the original paper whenever resuming work.
