# Bourgain circular maximal formalization status

Last updated: 2026-08-24 16:00:45 -04:00

Status values: `Proof completed`, `Statement completed`, `ToDo`.

## Main file targets

| File | Main blueprint target | Lean name | Status | Last update |
| --- | --- | --- | --- | --- |
| `MikhlinHormander.lean` | `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.mikhlin` | Proof completed | 2026-08-14 02:36:45 -04:00 |
| `LittlewoodPaley.lean` | `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.littlewoodPaley` | Proof completed | 2026-08-14 02:38:28 -04:00 |
| `OneDimStationaryPhase.lean` | `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.stationaryPhase` | ToDo | 2026-08-13 13:24:00 -04:00 |
| `RieszThorin.lean` | `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.rieszThorin` | Proof completed | 2026-08-13 22:06:39 -04:00 |
| `LpSpaceFacts.lean` | Reusable Lp-space facts | `Codex.Spherical.LpSpaceFacts.eLpNorm_power_interpolation_of_holder` | Proof completed | 2026-08-13 22:17:11 -04:00 |
| `MSSPhaseCalculus.lean` | Reusable radial phase calculus | `Codex.Spherical.MSSPhaseCalculus.laplacian_radial_phase_eq` | Proof completed | 2026-08-14 04:37:17 -04:00 |
| `SmoothDyadicPhysicalCore.lean` | Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.fourierCubeProjection_eq_sourceKernel` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| `MSS.lean` | `thm:intro-mss-local-smoothing` | `Codex.Spherical.MSS.localSmoothing_of_lpCutoffs` | Proof completed | 2026-08-24 13:48:00 -04:00 |
| `MSS.lean` | `thm:intro-discrete-local-smoothing` | `Codex.Spherical.MSS.discreteLocalSmoothing` | Statement completed | 2026-08-13 13:24:00 -04:00 |
| `Bourgain.lean` | `thm:intro-bourgain` | `Codex.Spherical.Bourgain.bourgainCircularMaximal` | Proof completed | 2026-08-24 13:57:41 -04:00 |
| `FractalDilations/DiagonalTheorem.lean` | Final requested integration | `Codex.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_sphericalMaximal_le` | Proof completed | 2026-08-24 16:00:45 -04:00 |

## Blueprint ledger

This ledger records only theorem, proposition, lemma, and corollary labels from
`blueprints/bourgain_circular_maximal_blueprint.tex`, in blueprint order.
The foundations above are intentionally preserved. Helper declarations, scratch
results, and convenience wrappers are not status items here.

### 1. Introduction and overview

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `thm:intro-bourgain` | `Codex.Spherical.Bourgain.bourgainCircularMaximal` | Proof completed | 2026-08-24 13:57:41 -04:00 |
| `thm:intro-mss-local-smoothing` | `Codex.Spherical.MSS.localSmoothing_of_lpCutoffs` | Proof completed | 2026-08-24 13:48:00 -04:00 |
| `thm:intro-discrete-local-smoothing` | `Codex.Spherical.MSS.discreteLocalSmoothing` | Statement completed | 2026-08-20 22:32:52 -04:00 |

### 2. From a positive local-smoothing gain to the circular maximal theorem

#### 2.1 Standard analytic inputs

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `thm:basic-analysis` | Imported repository and Mathlib interfaces | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `thm:plancherel` | Imported Mathlib Fourier interface | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.mikhlin` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.littlewoodPaley` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.homogeneousDyadicResolution` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `thm:hardy-littlewood` | Imported Mathlib maximal-function interface | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `lem:radial-majorant` | `Codex.Spherical.Bourgain.scaledSchwartzConvolution_radialMajorant` | Proof completed | 2026-08-20 22:32:52 -04:00 |

#### 2.2 One-dimensional control in the time variable

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `lem:time-sobolev` | `Codex.Spherical.Bourgain.timeSobolevL2` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `cor:time-sobolev-spacetime` | `Codex.Spherical.Bourgain.timeSobolevL2_spacetime` | Proof completed | 2026-08-20 22:32:52 -04:00 |

#### 2.3 Stationary phase and the wave decomposition of circular means

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.stationaryPhase` | ToDo | 2026-08-20 22:32:52 -04:00 |
| `lem:circle-stationary-phase` | `Codex.Spherical.Bourgain.circleStationaryPhase` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleWaveDecomposition` | ToDo | 2026-08-20 22:32:52 -04:00 |

#### 2.4 The conditional local maximal estimate

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `lem:annular-stability` | `Codex.Spherical.Bourgain.exists_circleAnnularEndpointWaveContribution_dyadicBall_stability` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `prop:annular-maximal` | `Codex.Spherical.Bourgain.annularCircularMaximal` | ToDo | 2026-08-20 22:32:52 -04:00 |

#### 2.5 Scaling and summation over all radii

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `lem:low-relative-frequency` | `Codex.Spherical.Bourgain.lowRelativeFrequencies` | ToDo | 2026-08-20 22:32:52 -04:00 |
| `lem:high-frequency-scaling` | `Codex.Spherical.Bourgain.highFrequencyScaling` | ToDo | 2026-08-20 22:32:52 -04:00 |
| `thm:conditional-bourgain` | `Codex.Spherical.Bourgain.conditionalCircularMaximal` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `cor:conditional-extension` | `Codex.Spherical.Bourgain.conditionalExtension` | ToDo | 2026-08-20 22:32:52 -04:00 |

### 3. The Mockenhaupt--Seeger--Sogge local-smoothing estimate

#### 3.1 Endpoint estimates

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.rieszThorin` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.l2Endpoint` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.waveKernelL1_sharp` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `prop:mss-linfty-endpoint` | `Codex.Spherical.MSS.mssLInfinityEndpoint` | Proof completed | 2026-08-20 22:32:52 -04:00 |

#### 3.2 Radial localization and vertical recombination

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.relevantRadialIndexEnumeration` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `prop:mss-radial-time-localization` | `Codex.Spherical.MSS.radialTimeLocalization` | Proof completed | 2026-08-21 11:59:52 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.verticalRecombination_of_MSSVerticalCutoff` | Proof completed | 2026-08-21 14:54:33 -04:00 |

#### 3.3 Angular wave-front localization and plate overlap

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `lem:mss-wavefront-localization` | `Codex.Spherical.MSS.wavefrontLocalization_of_MSSWavefrontKernelData` | Proof completed | 2026-08-21 17:29:49 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlap_of_angularSectorGeometry` | Proof completed | 2026-08-21 17:40:37 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.overlapSquareFunction_of_levelData` | Proof completed | 2026-08-21 18:58:10 -04:00 |
| `lem:mss-remove-vertical` | `Codex.Spherical.MSS.removeVerticalProjections_of_schwartz` | Proof completed | 2026-08-21 19:52:22 -04:00 |

#### 3.4 The fine square function and the light-ray maximal estimate

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `thm:fourier-cube-square-function` | `Codex.Spherical.MSS.latticeFourierCubeSquareFunction_lintegral_four` | Proof completed | 2026-08-24 04:18:42 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.hasLightRayMaximalEstimate` | Proof completed | 2026-08-22 14:52:07 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.sq_norm_continuumFineKernelTerm_le_lightRayEnergy` | Proof completed | 2026-08-20 22:32:52 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.mssFineSquareFunctionEstimate` | Proof completed | 2026-08-24 05:25:06 -04:00 |

#### 3.5 Completion of the endpoint estimate at p=4

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `prop:mss-recombination` | `Codex.Spherical.MSS.mssRecombination_of_structuredData` | Proof completed | 2026-08-24 06:40:01 -04:00 |
| `thm:mss-p4` | `Codex.Spherical.MSS.p4LocalSmoothing_of_lpCutoffs` | Proof completed | 2026-08-24 13:41:49 -04:00 |

#### 3.6 Interpolation, the MSS gain, and the discretized form

| Blueprint label | Lean declaration / interface | Status | Last reviewed |
| --- | --- | --- | --- |
| `thm:mss-local-smoothing` | `Codex.Spherical.MSS.localSmoothing_of_lpCutoffs` | Proof completed | 2026-08-24 13:48:00 -04:00 |
| `cor:mss-discrete` | `Codex.Spherical.MSS.discreteLocalSmoothing` | Statement completed | 2026-08-20 22:32:52 -04:00 |
| `cor:bourgain-final` | `Codex.Spherical.Bourgain.bourgainCircularMaximal` | Proof completed | 2026-08-24 13:57:41 -04:00 |
