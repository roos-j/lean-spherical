# Duoandikoetxea--Vega planar formalization status

Last updated: 2026-08-25 01:43:42 -0400

Status values:

* `Proof completed` -- an unconditional Lean proof exists;
* `Reduction completed` -- the Lean proof is complete except that it invokes
  the single unproved placeholder
  `Codex.PowerWeights.DuoandikoetxeaVega.exists_planarNegativeRawBandRate`;
* `Statement completed` -- the target is correctly formulated but unproved;
* `ToDo` -- not formalized.

All declarations below live in
`LeanSpherical/Codex/PowerWeights/DuoandikoetxeaVega.lean`, namespace
`Codex.PowerWeights.DuoandikoetxeaVega`, unless a fully qualified name is
given.  Lean names are abbreviated to their final component.

## Public API

| Public name in `LeanSpherical/Theorems.lean` | Blueprint target | Status | Last update |
| --- | --- | --- | --- |
| `Spherical.PowerWeights.eLpNorm_circularMaximal_powerWeight_le_of_neg` | `thm:direct-missing` | Reduction completed | 2026-08-25 01:43:42 -0400 |
| `Spherical.PowerWeights.closure_typeSet_eq` (`2 <= d`) | Thm. 1.1 of arXiv:2602.17613 in dimension two | Reduction completed | 2026-08-25 01:43:42 -0400 |

## Blueprint ledger

This ledger records the labeled theorems and propositions and the `blueprint`
work items of `blueprints/duoandikoetxea_vega_planar_blueprint.tex`, in
blueprint order.  Items without a LaTeX label are identified by their
blueprint heading.  Helper declarations, scratch results, and convenience
wrappers are not status items here.

### 1. Executive conclusion

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `thm:direct-missing` | `eLpNorm_circularMaximal_powerWeight_le_of_neg` | Reduction completed | 2026-08-25 01:43:42 -0400 |
| `thm:minimal-local` | `eLpNorm_localCircularMaximal_powerWeight_le_of_neg` | Reduction completed | 2026-08-25 01:43:42 -0400 |
| `thm:dv-general` (planar range `-1 < a < p - 2`) | not formalized; only the `a < 0` subrange is needed | ToDo | 2026-08-25 01:43:42 -0400 |

### 2. Conventions and comparison with the Lean definitions

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Reflection invariance of normalized sphere measure | not needed: the project convention is already `x + t * omega` | Proof completed | 2026-08-25 01:43:42 -0400 |
| `ENNReal`-valued maximal-function adapter | `Codex.Spherical.PowerWeights.PowerWeightTheorem.restrictedSphericalMaximal_eq_restrictedNormalizedSphericalMaximal` | Proof completed | 2026-08-25 01:43:42 -0400 |

### 3. The complete `d = 2` reduction

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| The planar strict region lies above `a = -1` | `neg_one_lt_alpha_of_planar_strict` | Proof completed | 2026-08-25 01:43:42 -0400 |
| The high-`p` negative branch lies below `p - 2` | `alpha_lt_p_sub_two` | Proof completed | 2026-08-25 01:43:42 -0400 |
| `prop:high-p-branch` | `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_high_p_branch` | Reduction completed | 2026-08-25 01:43:42 -0400 |
| Proof using only the minimal local theorem | superseded: the all-radius reassembly of the repository is used instead | Proof completed | 2026-08-25 01:43:42 -0400 |
| Passage to the closure | `power_weight_spherical_maximal_main_planar`, `closure_typeSet_eq` | Reduction completed | 2026-08-25 01:43:42 -0400 |

### 4. Source audit

No Lean content.  The bibliographic identification and the
reconstruction note require no formalization.

### 5. Analytic proof blueprint

#### 5.1 Phase A: the local operator and a countable supremum

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Local operator, continuity in `t`, rational radii | `localCircularMaximal`, `restrictedSphericalMaximal_eq_of_subset_closure` | Proof completed | 2026-08-25 01:43:42 -0400 |
| Finite-grid approximants | `restrictedSphericalMaximal_iUnion` | Proof completed | 2026-08-25 01:43:42 -0400 |

#### 5.2 Phase B: Littlewood--Paley pieces

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Frequency projections `P_j`, `T_j`, `M_j` | `Codex.Spherical.PowerWeights.LocalizedUpper.restrictedRelativeBandpassSphericalMaximal` | Proof completed | 2026-08-25 01:43:42 -0400 |
| Reconstruction inequality | `Codex.Spherical.PowerWeights.GlobalRelativeReassembly` and the buffered raw-band assembly | Proof completed | 2026-08-25 01:43:42 -0400 |
| Low frequencies | `Codex.Spherical.PowerWeights.CentralLowpass` / `BufferedCentralLowpass` | Proof completed | 2026-08-25 01:43:42 -0400 |

#### 5.3 Phase C: unweighted frequency gain

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `bp:bourgain-piece` | `exists_relativeCircularBandGeometricDecay` | Proof completed | 2026-08-25 01:43:42 -0400 |

#### 5.4 Phase D: the critical-weight estimate with loss

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `prop:critical-loss` | folded into `HasPlanarNegativeRawBandRate`; unproved at `exists_planarNegativeRawBandRate` | ToDo | 2026-08-25 01:43:42 -0400 |
| Spatial annuli | not formalized | ToDo | 2026-08-25 01:43:42 -0400 |
| Near and far interactions | not formalized | ToDo | 2026-08-25 01:43:42 -0400 |
| Maximal parameter (Sobolev in `t` on `[1,2]`) | not formalized | ToDo | 2026-08-25 01:43:42 -0400 |
| Annular summation | not formalized | ToDo | 2026-08-25 01:43:42 -0400 |

#### 5.5 Phase E: from `p = 2` to `p > 2` at the critical weight

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Fixed-measure interpolation with the `L^inf` bound | folded into `HasPlanarNegativeRawBandRate` | ToDo | 2026-08-25 01:43:42 -0400 |

#### 5.6 Phase F: Stein--Weiss interpolation in the weight

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Change-of-measure interpolation at fixed `p` | not formalized; no Stein--Weiss theorem exists in the repository | ToDo | 2026-08-25 01:43:42 -0400 |
| Choice of the loss parameter and positivity of `eta` | `exists_pos_interpolated_gain` | Proof completed | 2026-08-25 01:43:42 -0400 |
| Packaged conclusion of Phases D--F | `HasPlanarNegativeRawBandRate`, `exists_planarNegativeRawBandRate` | Statement completed | 2026-08-25 01:43:42 -0400 |

#### 5.7 Phase G: summing the frequencies

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Geometric frequency summation | `Codex.Spherical.PowerWeights.StrictNegativeEndpoint.hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_uniform_buffered_raw_band_rate_and_unweighted` | Proof completed | 2026-08-25 01:43:42 -0400 |

#### 5.8 Phase H: extension to all `L^p` functions

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Schwartz-core to `MemLp` extension | `exists_powerWeight_bound_of_strongType` | Proof completed | 2026-08-25 01:43:42 -0400 |

#### 5.9 Phase I: globalization

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Local-to-global over all radii | `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_negative_of_gt_two` | Reduction completed | 2026-08-25 01:43:42 -0400 |

### 6. Interpolation interface for Lean

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Linearization by finite rational grids | `restrictedSphericalMaximal_eq_of_subset_closure`, `restrictedSphericalMaximal_iUnion` | Proof completed | 2026-08-25 01:43:42 -0400 |
| Fixed-measure interpolation `L^2 -> L^p` at the weight `|x|^-1` | not formalized | ToDo | 2026-08-25 01:43:42 -0400 |
| Stein--Weiss interpolation with change of measure | not formalized | ToDo | 2026-08-25 01:43:42 -0400 |

### 7. Proposed Lean API

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| The minimal local theorem | `eLpNorm_localCircularMaximal_powerWeight_le_of_neg` | Reduction completed | 2026-08-25 01:43:42 -0400 |
| The global direct corollary | `eLpNorm_circularMaximal_powerWeight_le_of_neg` | Reduction completed | 2026-08-25 01:43:42 -0400 |
| The full planar source range | not formalized | ToDo | 2026-08-25 01:43:42 -0400 |
| Set-monotonicity helpers | `restrictedSphericalMaximal_mono`, `eLpNorm_restrictedSphericalMaximal_mono`, `memLp_restrictedSphericalMaximal_of_le` | Proof completed | 2026-08-25 01:43:42 -0400 |
| The arithmetic bridge into the FRS branch | `neg_one_lt_alpha_of_planar_strict` | Proof completed | 2026-08-25 01:43:42 -0400 |
| Final `d = 2` branch | `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_of_strict_implicit` | Reduction completed | 2026-08-25 01:43:42 -0400 |

### Appendix A. Real-exponent variant

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Real-exponent formulation | `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_negative_of_gt_two` | Reduction completed | 2026-08-25 01:43:42 -0400 |

### Appendix B. Direct proof of the restricted transfer

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Restricted-radii transfer | `eLpNorm_restrictedCircularMaximal_powerWeight_le_of_neg` | Reduction completed | 2026-08-25 01:43:42 -0400 |

## Supporting inputs proved outside this project

These are recorded because the blueprint's dependency checklist lists them as
assumed, and the reduction relies on them.

| Input | Lean declaration | Status |
| --- | --- | --- |
| Bourgain's planar circular maximal theorem | `Codex.Spherical.Bourgain.bourgainCircularMaximal` | Proof completed |
| Seeger--Wainger--Wright restricted theorem | `Spherical.RestrictedDilations.eLpNorm_restrictedSphericalMaximal_le` | Proof completed |
| Planar unweighted input above the critical exponent | `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_zero_planar_of_sww` | Proof completed |
| FRS necessity, convexity and closure theory | `Codex.Spherical.PowerWeights.Assembly`, `NecessaryAssembly`, `ParameterClosure` | Proof completed |
| FRS nonnegative-weight branch | `Codex.Spherical.PowerWeights.StrictPositive` | Proof completed |
| FRS negative subquadratic branch | `Codex.Spherical.PowerWeights.StrictNegativeEndpoint` | Proof completed |
| Planar negative branch at `p = 2` | `Codex.Spherical.PowerWeights.StrictNegativeHigher` | Proof completed |
