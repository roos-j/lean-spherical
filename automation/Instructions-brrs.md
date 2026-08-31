# BRRS formalization instructions

Work only in the authorized BRRS formalization components unless an existing
file must be adjusted to preserve a compiling import graph:

- `LeanSpherical/Auto/ConvexDuality.lean`
- `LeanSpherical/Auto/Spherical/LegendreAssouad.lean`
- `LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
- `LeanSpherical.lean` only for necessary imports

The main objectives, in order, are:

1. Complete the literal BRRS Theorem 1.2 in `LegendreAssouad.lean`.
   Its statements must faithfully model the paper, including Rutar's
   open-interval realization theorem and the required endpoint repair.
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

Current proved checkpoints:

- Reusable restricted-conjugacy and biconjugacy tools are in
  `Auto.ConvexDuality`.
- BRRS Theorem 1.2(i), the exact entropy/spectrum Legendre identity, is
  proved for nonempty bounded sets.
- The ``only if'' direction of Theorem 1.2(ii) is proved.
- The literal `p = 2` Schwartz-core endpoint of Theorem 1.1 is proved.

The remaining genuine developments are the variable-ratio Moran realization
behind Rutar's Corollary B and the sharp fractal-time `p > 2` BRRS analytic
estimate and sharpness construction.  These must be developed rather than
assumed.
