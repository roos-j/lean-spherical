# Duoandikoetxea--Vega planar formalization status

Last updated: 2026-08-25 16:56:40 -0400

**The formalization is complete.**  Both public targets in
`LeanSpherical/Theorems.lean` are unconditional: `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for
`Spherical.PowerWeights.eLpNorm_circularMaximal_powerWeight_le_of_neg` and for
`Spherical.PowerWeights.closure_typeSet_eq`, and the project contains no
`sorry` outside the unrelated orphan module
`Codex/Spherical/FractalDilations/ProofSkeleton.lean` (which is not in the
import closure of `LeanSpherical.lean`).

Status values:

* `Proof completed` -- an unconditional Lean proof exists;
* `Statement completed` -- the target is correctly formulated but unproved;
* `ToDo` -- not formalized (not needed for the two public targets).

All declarations below live in
`LeanSpherical/Codex/PowerWeights/DuoandikoetxeaVega.lean`, namespace
`Codex.PowerWeights.DuoandikoetxeaVega`, unless a fully qualified name is
given.  Lean names are abbreviated to their final component.

## Public API

| Public name in `LeanSpherical/Theorems.lean` | Blueprint target | Status | Last update |
| --- | --- | --- | --- |
| `Spherical.PowerWeights.eLpNorm_circularMaximal_powerWeight_le_of_neg` | `thm:direct-missing` | Proof completed | 2026-08-25 16:56:40 -0400 |
| `Spherical.PowerWeights.closure_typeSet_eq` (`2 <= d`) | Thm. 1.1 of arXiv:2602.17613 for `d >= 2` | Proof completed | 2026-08-25 16:56:40 -0400 |

## Blueprint ledger

This ledger records the labeled theorems and propositions and the `blueprint`
work items of `blueprints/duoandikoetxea_vega_planar_blueprint.tex`, in
blueprint order.  Items without a LaTeX label are identified by their
blueprint heading.  Helper declarations, scratch results, and convenience
wrappers are not status items here.

### 1. Executive conclusion

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `thm:direct-missing` | `eLpNorm_circularMaximal_powerWeight_le_of_neg` | Proof completed | 2026-08-25 01:43:42 -0400 |
| `thm:minimal-local` | `eLpNorm_localCircularMaximal_powerWeight_le_of_neg` | Proof completed | 2026-08-25 01:43:42 -0400 |
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
| `prop:high-p-branch` | `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_high_p_branch` | Proof completed | 2026-08-25 01:43:42 -0400 |
| Proof using only the minimal local theorem | superseded: the all-radius reassembly of the repository is used instead | Proof completed | 2026-08-25 01:43:42 -0400 |
| Passage to the closure | `power_weight_spherical_maximal_main_planar`, `closure_typeSet_eq` | Proof completed | 2026-08-25 01:43:42 -0400 |

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

The whole phase is proved; the packaged output is `dvWeightedL2Core`, the
weighted `L^2` estimate on the ball `B(0, 1/32)` against `|x|^-1` with the
polynomial loss `C (j+1)^2`.

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `prop:critical-loss` | `HasCriticalWeightBandBound`, proved at `hasCriticalWeightBandBound` (via `dvCriticalWeightBandBound`) | Proof completed | 2026-08-25 16:56:40 -0400 |
| **Weighted `L^2` core** `int_{B(0,1/32)} \|x\|^-1 (M_j f)^2 <= C (j+1)^2 \|f\|_2^2` | `dvWeightedL2Core` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Radial weight vanishing at the endpoints | `dvWeight`, `hasDerivAt_dvWeight`, `one_le_dvWeight`, `dvWeight_le`, `abs_dvWeightDeriv_le` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Boundary-term-free radial integration by parts | `norm_integral_dvKernelIntegrand_ibp_le`, `norm_integral_dvKernelIntegrand_le` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Planar amplitude and derivative bounds | `exists_planarAmplitude_endpoint_bound`, `exists_planarAmplitude_middle_bound`, `exists_dvUniform_bound` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Nine-term normal-form expansion of the radial kernel | `dvKernel_eq_sum` | Proof completed | 2026-08-25 16:56:40 -0400 |
| **Oscillatory radial kernel decay** `abs K(s,t) <= C (s^-1 + t^-1)/(1 + abs (s-t))` | `exists_dvKernel_bound` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Pointwise Sobolev bound in the radius | `dvSobolev`, `dvSobolev2`, `dvSobolevPointwise`, `dvMaximal_le_of_pointwise` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Frequency cut-off matching the band support | `dvFreqCut`, `dvSig_mul_dvFreqCut`, `hasCompactSupport_dvFreqCut` | Proof completed | 2026-08-25 16:56:40 -0400 |
| `TT*` reduction to a frequency quadratic form | `dvTTStar_pointwise`, `dvWeightedSquare_le`, `dvWeightedSquare_lintegral_le` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Schur test with the polar row estimate | `dvRow_polar`, `exists_dvRow_bound`, `dvRowBound` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Spatial annuli (compactly supported Fourier profile) | `dvChi`, `dvTheta`, `dvGb`, `exists_dvProfile`, `dvGk`, `fourierInv_dvGk` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Near and far interactions (space-time multipliers) | `dvMulA`, `dvMulB`, `dvMulC`, `exists_dvMul_bound`, `dvKerA_bound`, `dvKerB_bound`, `dvKerC_bound` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Maximal parameter (Sobolev in `t` at scale `2^-j`) | `dvShellEnergy`, `dvShellBound` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Annular summation | `dvWeight_le_shells`, `dvBallWeight_le`, `dvSupBound`, `dvGeomSumLe`, `dvLogBound` | Proof completed | 2026-08-25 16:56:40 -0400 |

#### 5.5 Phase E: from `p = 2` to `p > 2` at the critical weight

Riesz--Thorin interpolation between the Phase D weighted `L^2` estimate and the
elementary `L^inf` bound, applied to the operator linearized by a measurable
choice of radii.  The two measures are different: Lebesgue measure on the
input side and `|x|^-1 dx` restricted to `B(0, 1/32)` on the output side, so
the interpolated bound is exactly `prop:critical-loss` with loss `(j+1)^2`.

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Physical (convolution) form of one band average | `dvPsiS`, `dvKerS`, `dvKerS_conv`, `dvOp`, `dvOp_schwartz` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Uniform `L^1` and `L^2` kernel sizes | `integral_norm_dvKerS`, `dvPsiL1`, `eLpNorm_dvKerS_le`, `dvPsiL2` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Linearization by a measurable selection of radii | `dvT`, `dvT_add`, `dvT_smul`, `measurable_dvT`, `dvSel`, `dvSel_disjoint`, `dvSel_exists`, `dvT_dvSel_eq` | Proof completed | 2026-08-25 16:56:40 -0400 |
| The `L^inf` endpoint | `norm_sphericalAverage_le`, `norm_convolution_le_of_ae_bound`, `dvOp_sup_bound`, `dvT_eLpNorm_top` | Proof completed | 2026-08-25 16:56:40 -0400 |
| The `L^2` endpoint on the Schwartz core | `dvNu`, `dvNu_lintegral`, `dvT_l2_schwartz` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Density: `L^2` endpoint for all `L^2` inputs | `enorm_convolution_le_l2`, `dvT_sub_bound`, `dvT_l2_general` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Fixed-exponent interpolation with the `L^inf` bound | `dvT_lp_simple` (via `Codex.riesz_thorin`) | Proof completed | 2026-08-25 16:56:40 -0400 |
| Density: back from simple functions to Schwartz data | `dvT_lp_schwartz` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Finite-radius weighted `L^p` band estimate | `dvMaximal_finset_lp` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Reduction of an arbitrary radius set to finite ones | `dvR`, `dvApprox`, `continuousAt_dvSlice`, `dvMaximal_Icc_le_iSup`, `dvMaximal_set_lp` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Small frequency indices `j <= 2` | `dvCrudeL2Core` | Proof completed | 2026-08-25 16:56:40 -0400 |
| Packaged conclusion of Phase E | `dvCriticalWeightBandBound` | Proof completed | 2026-08-25 16:56:40 -0400 |

#### 5.6 Phase F: Stein--Weiss interpolation in the weight

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Change-of-measure interpolation at fixed `p` | superseded: `hasPlanarNegativeRawBandRate_of_criticalWeight` needs only Hoelder, no Stein--Weiss theorem | Proof completed | 2026-08-25 07:56:33 -0400 |
| Pointwise weight splitting `\|x\|^{-θ} = (\|x\|^{-1})^θ` | `radialPowerWeight_mul_eq_holder_split` | Proof completed | 2026-08-25 07:56:33 -0400 |
| Hoelder interpolation in the weight | `lintegral_radialPowerWeight_le_holder` | Proof completed | 2026-08-25 07:56:33 -0400 |
| Choice of the loss parameter and positivity of `eta` | `exists_bound_pow_mul_geometric`, used inside `hasPlanarNegativeRawBandRate_of_criticalWeight` | Proof completed | 2026-08-25 07:56:33 -0400 |
| Packaged conclusion of Phases D--F | `HasPlanarNegativeRawBandRate`, `hasPlanarNegativeRawBandRate_of_criticalWeight` | Proof completed | 2026-08-25 07:56:33 -0400 |

#### 5.7 Phase G: summing the frequencies

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Geometric frequency summation | `Codex.Spherical.PowerWeights.StrictNegativeEndpoint.hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_of_uniform_buffered_raw_band_rate_and_unweighted` | Proof completed | 2026-08-25 07:56:33 -0400 |
| Unweighted endpoint in `lintegral` form | `lintegral_rpow_band_le_of_geometricDecay` | Proof completed | 2026-08-25 07:56:33 -0400 |
| Input-side weight comparison on the annulus | `lintegral_rpow_norm_le_powerWeighted_of_annulus_support` | Proof completed | 2026-08-25 07:56:33 -0400 |
| Radius-set monotonicity of the literal band | `restrictedRelativeBandpassSphericalMaximal_mono` | Proof completed | 2026-08-25 07:56:33 -0400 |

#### 5.8 Phase H: extension to all `L^p` functions

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Schwartz-core to `MemLp` extension | `exists_powerWeight_bound_of_strongType` | Proof completed | 2026-08-25 01:43:42 -0400 |

#### 5.9 Phase I: globalization

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Local-to-global over all radii | `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_negative_of_gt_two` | Proof completed | 2026-08-25 01:43:42 -0400 |

### 6. Interpolation interface for Lean

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Linearization by finite rational grids | `restrictedSphericalMaximal_eq_of_subset_closure`, `restrictedSphericalMaximal_iUnion` | Proof completed | 2026-08-25 01:43:42 -0400 |
| Fixed-measure interpolation `L^2 -> L^p` at the weight `|x|^-1` | `dvT_lp_simple`, `dvMaximal_finset_lp` (Riesz--Thorin with two measures, from `LeanSpherical/Codex/SteinInterpolation.lean`) | Proof completed | 2026-08-25 16:56:40 -0400 |
| Stein--Weiss interpolation with change of measure | not needed: the two-measure Riesz--Thorin theorem plus one Hoelder step replaces it | Proof completed | 2026-08-25 16:56:40 -0400 |

### 7. Proposed Lean API

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| The minimal local theorem | `eLpNorm_localCircularMaximal_powerWeight_le_of_neg` | Proof completed | 2026-08-25 01:43:42 -0400 |
| The global direct corollary | `eLpNorm_circularMaximal_powerWeight_le_of_neg` | Proof completed | 2026-08-25 01:43:42 -0400 |
| The full planar source range | not formalized | ToDo | 2026-08-25 01:43:42 -0400 |
| Set-monotonicity helpers | `restrictedSphericalMaximal_mono`, `eLpNorm_restrictedSphericalMaximal_mono`, `memLp_restrictedSphericalMaximal_of_le` | Proof completed | 2026-08-25 01:43:42 -0400 |
| The arithmetic bridge into the FRS branch | `neg_one_lt_alpha_of_planar_strict` | Proof completed | 2026-08-25 01:43:42 -0400 |
| Final `d = 2` branch | `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_of_strict_implicit` | Proof completed | 2026-08-25 01:43:42 -0400 |

### Appendix A. Real-exponent variant

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Real-exponent formulation | `hasRestrictedNormalizedSphericalMaximalPowerWeightStrongType_planar_negative_of_gt_two` | Proof completed | 2026-08-25 01:43:42 -0400 |

### Appendix B. Direct proof of the restricted transfer

| Blueprint item | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| Restricted-radii transfer | `eLpNorm_restrictedCircularMaximal_powerWeight_le_of_neg` | Proof completed | 2026-08-25 01:43:42 -0400 |

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
