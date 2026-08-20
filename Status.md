# Bourgain circular maximal formalization status

Last updated: 2026-08-14 12:33:00 -04:00

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
| `MSS.lean` | `thm:intro-mss-local-smoothing` | `Codex.Spherical.MSS.localSmoothing` | Statement completed | 2026-08-13 13:24:00 -04:00 |
| `MSS.lean` | `thm:intro-discrete-local-smoothing` | `Codex.Spherical.MSS.discreteLocalSmoothing` | Statement completed | 2026-08-13 13:24:00 -04:00 |
| `Bourgain.lean` | `thm:intro-bourgain` | `Codex.Spherical.Bourgain.bourgainCircularMaximal` | ToDo | 2026-08-13 13:24:00 -04:00 |
| `FractalDilations/DiagonalTheorem.lean` | Final requested integration | `Codex.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_sphericalMaximal_le` | ToDo | 2026-08-13 13:24:00 -04:00 |

## `LeanSpherical/Codex/Spherical/MikhlinHormander.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.MikhlinCondition` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.mikhlin` | Proof completed | 2026-08-14 02:36:45 -04:00 |
| `thm:littlewood-paley` downstream consequence | `Codex.Spherical.MikhlinHormander.littlewoodPaley_of_mikhlin` | Proof completed | 2026-08-14 02:38:28 -04:00 |
| Coordinate Mikhlin bridge | `Codex.Spherical.MikhlinHormander.norm_continuousMultilinearMap_le_of_basis_coordinates` | Proof completed | 2026-08-14 02:36:45 -04:00 |
| Coordinate Mikhlin bridge | `Codex.Spherical.MikhlinHormander.CoordinateMikhlinCondition` | Proof completed | 2026-08-14 02:36:45 -04:00 |
| Coordinate Mikhlin bridge | `Codex.Spherical.MikhlinHormander.coordinateMikhlinCondition_to_mikhlinCondition` | Proof completed | 2026-08-14 02:36:45 -04:00 |
| `thm:mikhlin` planar coordinate form | `Codex.Spherical.MikhlinHormander.PlanarCoordinateMikhlinCondition` | Proof completed | 2026-08-14 02:36:45 -04:00 |
| `thm:mikhlin` planar coordinate form | `Codex.Spherical.MikhlinHormander.planarCoordinateMikhlinCondition_to_mikhlinCondition` | Proof completed | 2026-08-14 02:36:45 -04:00 |
| `thm:mikhlin` planar coordinate form | `Codex.Spherical.MikhlinHormander.planarCoordinateMikhlinCondition_family_to_mikhlinCondition` | Proof completed | 2026-08-14 02:36:45 -04:00 |
| `thm:mikhlin` planar coordinate form | `Codex.Spherical.MikhlinHormander.mikhlin_two_of_coordinateMikhlinCondition` | Proof completed | 2026-08-14 02:36:45 -04:00 |
| Compact-annular multiplier theorem | `Codex.Spherical.MikhlinHormander.compactAnnularSchwartzMultiplier_strong_type` | Proof completed | 2026-08-13 22:28:25 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.compactFourierIBPConstant` | Proof completed | 2026-08-13 22:41:01 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.pow_norm_fourierInv_le_compactFourierIBPConstant` | Proof completed | 2026-08-13 22:41:01 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierKernelSize_le_compactFourierIBP` | Proof completed | 2026-08-14 05:35:16 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.integral_norm_le_of_support_subset_of_norm_le` | Proof completed | 2026-08-14 05:50:11 -04:00 |
| Dimension-generic radial compactness | `Codex.Spherical.MikhlinHormander.exists_norm_iteratedFDeriv_norm_bound_on_annulus` | Proof completed | 2026-08-14 06:16:36 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.compactFourierIBPConstant_le_of_support_subset_of_uniform_deriv_bound` | Proof completed | 2026-08-14 06:25:11 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.compact_cN_fourierInv_decay` | Proof completed | 2026-08-13 22:41:01 -04:00 |
| Literal dimension-generic multiplier | `Codex.Spherical.MikhlinHormander.mikhlinMultiplier` | Proof completed | 2026-08-13 22:49:15 -04:00 |
| Dimension-generic raw Mikhlin localization | `Codex.Spherical.MikhlinHormander.norm_iteratedFDeriv_cutoff_mul_mikhlin_le` | Proof completed | 2026-08-13 23:31:00 -04:00 |
| Dimension-generic raw Mikhlin localization | `Codex.Spherical.MikhlinHormander.norm_iteratedFDeriv_cutoff_mul_mikhlin_le_of_uniform_weighted_cutoff_bound` | Proof completed | 2026-08-13 23:31:00 -04:00 |
| Dimension-generic raw Mikhlin localization | `Codex.Spherical.MikhlinHormander.uniform_weighted_cutoff_deriv_comp_const_smul` | Proof completed | 2026-08-13 23:31:00 -04:00 |
| Dimension-generic raw Mikhlin localization | `Codex.Spherical.MikhlinHormander.norm_iteratedFDeriv_dilated_cutoff_mul_mikhlin_le` | Proof completed | 2026-08-13 23:31:00 -04:00 |
| Dimension-generic raw Mikhlin localization | `Codex.Spherical.MikhlinHormander.schwartzWeightedCutoffDerivativeConstant` | Proof completed | 2026-08-13 23:36:00 -04:00 |
| Dimension-generic raw Mikhlin localization | `Codex.Spherical.MikhlinHormander.weighted_deriv_le_schwartzWeightedCutoffDerivativeConstant` | Proof completed | 2026-08-13 23:36:00 -04:00 |
| Dimension-generic raw Mikhlin localization | `Codex.Spherical.MikhlinHormander.norm_iteratedFDeriv_dilated_schwartz_cutoff_mul_mikhlin_le` | Proof completed | 2026-08-13 23:36:00 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.integrable_of_uniform_and_power_decay` | Proof completed | 2026-08-13 22:49:15 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.compact_cN_fourierInv_integrable` | Proof completed | 2026-08-13 22:49:15 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.fderiv_fourierInv_eq_fourierInv_fourierSMulRight` | Proof completed | 2026-08-13 22:54:28 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.contDiff_fourierSMulRight_one` | Proof completed | 2026-08-13 22:59:16 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.hasCompactSupport_fourierSMulRight_one` | Proof completed | 2026-08-13 22:59:16 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.integrable_fderiv_fourierInv_of_compact_fourierSMulRight` | Proof completed | 2026-08-13 22:59:16 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.integrable_fderiv_compact_cN_fourierInv` | Proof completed | 2026-08-13 22:59:16 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.integral_norm_sub_translate_compact_cN_fourierInv_le` | Proof completed | 2026-08-13 22:59:16 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.integral_norm_sub_translate_le_two_integral_norm` | Proof completed | 2026-08-13 23:18:05 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.integral_norm_sub_translate_compact_cN_fourierInv_le_hormander` | Proof completed | 2026-08-13 23:18:05 -04:00 |
| Dimension-generic raw Mikhlin localization | `Codex.Spherical.MikhlinHormander.contDiff_hasCompactSupport_cutoff_mul_punctured` | Proof completed | 2026-08-13 23:18:05 -04:00 |
| `lem:calderon-zygmund-tail` | `Codex.Spherical.MikhlinHormander.integral_norm_kernel_sub_shift_le_of_hormander` | Proof completed | 2026-08-13 23:18:05 -04:00 |
| `lem:calderon-zygmund-tail` | `Codex.Spherical.MikhlinHormander.integral_norm_mean_zero_kernel_convolution_le_of_hormander` | Proof completed | 2026-08-13 23:18:05 -04:00 |
| `lem:calderon-zygmund-tail` | `Codex.Spherical.MikhlinHormander.restricted_mean_zero_kernel_convolution` | Proof completed | 2026-08-14 00:07:00 -04:00 |
| `lem:calderon-zygmund-tail` | `Codex.Spherical.MikhlinHormander.restricted_mean_zero_kernel_convolution_le_of_local_hormander` | Proof completed | 2026-08-14 00:07:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.signedDyadicLowOffsets` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.signedDyadicHighOffsets` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.exactDyadicRadius` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.exactDyadicRadius_selector` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.integerDyadicPhysicalFrequency_eq_zpow` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.sum_signedDyadicLowOffsets_eq` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.sum_signedDyadicHighOffsets_eq` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.sum_low_physicalFrequency_le` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.sum_high_physicalFrequency_inv_sq_le` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.setIntegral_norm_kernel_convolution_le_of_pointwise_tail` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.norm_sub_ge_third` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.integerDyadicBandpassPrototype_tail_seminorm_nonneg` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.one_scale_exterior_tail` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.physical_tail_algebra` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.finiteSignedIntegerDyadicBandpassKernel_split_at` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.low_signedDyadic_translation_bound` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.integral_norm_kernel_sub_shift_eq` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.low_signedDyadic_atom_tail_le` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.high_signedDyadic_kernel_exterior_tail` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.finiteSignedIntegerDyadicHighTailConstant` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.high_signedDyadic_atom_tail_le` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.setIntegral_norm_kernel_convolution_le_add_of_kernel_eq` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic C-Z tail | `Codex.Spherical.MikhlinHormander.finiteSignedIntegerDyadicBandpassCZTailConstant` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| `lem:calderon-zygmund-tail` | `Codex.Spherical.MikhlinHormander.finiteSignedIntegerDyadicBandpassKernel_atom_tail_le` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| `lem:calderon-zygmund-tail` | `Codex.Spherical.MikhlinHormander.finiteSignedIntegerDyadicBandpassKernel_hasFiniteConvolutionKernelCZTail` | Proof completed | 2026-08-14 00:25:00 -04:00 |
| Dimension-generic signed dyadic weak endpoint | `Codex.Spherical.MikhlinHormander.weak_one_finiteSignedIntegerDyadicMultiplier_of_CZTail` | Proof completed | 2026-08-14 00:30:00 -04:00 |
| Dimension-generic signed dyadic weak endpoint | `Codex.Spherical.MikhlinHormander.finiteSignedIntegerDyadicBandpassCZTailConstant_nonneg` | Proof completed | 2026-08-14 00:32:00 -04:00 |
| Dimension-generic signed dyadic weak endpoint | `Codex.Spherical.MikhlinHormander.weak_one_finiteSignedIntegerDyadicMultiplier` | Proof completed | 2026-08-14 00:32:00 -04:00 |
| Dimension-generic signed dyadic strong endpoint | `Codex.Spherical.MikhlinHormander.lintegral_norm_sq_finiteSignedIntegerDyadicMultiplierSchwartz_le` | Proof completed | 2026-08-14 00:43:00 -04:00 |
| Dimension-generic signed dyadic all-p | `Codex.Spherical.MikhlinHormander.lowerLp_finiteSignedIntegerDyadicMultiplier_of_CZTail` | Proof completed | 2026-08-14 00:43:00 -04:00 |
| Dimension-generic signed dyadic all-p | `Codex.Spherical.MikhlinHormander.lowerLp_finiteSignedIntegerDyadicMultiplier` | Proof completed | 2026-08-14 00:43:00 -04:00 |
| Dimension-generic signed dyadic all-p | `Codex.Spherical.MikhlinHormander.eLpNorm_two_finiteSignedIntegerDyadicMultiplier` | Proof completed | 2026-08-14 00:43:00 -04:00 |
| Dimension-generic signed dyadic all-p | `Codex.Spherical.MikhlinHormander.upperLp_finiteSignedIntegerDyadicMultiplier` | Proof completed | 2026-08-14 00:43:00 -04:00 |
| Dimension-generic signed dyadic all-p | `Codex.Spherical.MikhlinHormander.exists_strongLp_finiteSignedIntegerDyadicMultiplier` | Proof completed | 2026-08-14 00:43:00 -04:00 |
| Dimension-generic uniform signed dyadic all-p | `Codex.Spherical.MikhlinHormander.exists_uniform_strongLp_finiteSignedIntegerDyadicMultiplier` | Proof completed | 2026-08-14 01:23:15 -04:00 |
| Dimension-generic signed-dyadic/LP bridge | `Codex.Spherical.MikhlinHormander.finiteRademacherIntegerDyadicSum_eq_signedMultiplier` | Proof completed | 2026-08-14 01:27:00 -04:00 |
| Dimension-generic signed-dyadic/LP bridge | `Codex.Spherical.MikhlinHormander.rademacherSign_norm_le_one` | Proof completed | 2026-08-14 01:27:00 -04:00 |
| Dimension-generic signed dyadic moment bound | `Codex.Spherical.MikhlinHormander.exists_uniform_signed_dyadic_moment_bound` | Proof completed | 2026-08-14 01:27:00 -04:00 |
| `lem:calderon-zygmund-tail` | `Codex.Spherical.MikhlinHormander.HasFiniteConvolutionKernelCZTail_of_translation_bound` | Proof completed | 2026-08-13 23:18:05 -04:00 |
| Dimension-generic compact kernel layer | `Codex.Spherical.MikhlinHormander.compact_cN_fourierInv_hasFiniteConvolutionKernelCZTail` | Proof completed | 2026-08-13 23:18:05 -04:00 |
| Dimension-generic raw Mikhlin localization | `Codex.Spherical.MikhlinHormander.cutoff_mul_punctured_mikhlin_hasFiniteConvolutionKernelCZTail` | Proof completed | 2026-08-13 23:18:05 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.hasCompactSupport_integerDyadicBandpassPrototype` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.integerDyadicBandpassPrototype_zero_on_ball` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.hasCompactSupport_intDyadicBandpassMultiplier` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.intDyadicBandpassMultiplier_zero_on_ball` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.contDiff_hasCompactSupport_intDyadicMikhlinPiece` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.weighted_deriv_intDyadicMikhlinPiece` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.normalizedIntDyadicMikhlinPiece` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.normalizedIntDyadicMikhlinPiece_apply` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.contDiff_hasCompactSupport_normalizedIntDyadicMikhlinPiece` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.tsupport_normalizedIntDyadicMikhlinPiece_subset_unit_annulus` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.weighted_deriv_normalizedIntDyadicMikhlinPiece` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.deriv_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.integral_norm_iteratedFDeriv_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.compactFourierIBPConstant_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.integrable_iteratedFDeriv_normalizedIntDyadicMikhlinPiece` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.pow_norm_fourierInv_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.intDyadicMikhlinPiece_eq_normalized_scale` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.fourierInv_intDyadicMikhlinPiece_eq_normalized_scale` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.weighted_deriv_normalizedIntDyadicMikhlinPiece_le_uniform` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.deriv_fourierPowSMulRight_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.deriv_fourierSMulRight_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.tsupport_fourierSMulRight_normalizedIntDyadicMikhlinPiece_subset_unit_annulus` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.integral_norm_iteratedFDeriv_fourierSMulRight_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.compactFourierIBPConstant_fourierSMulRight_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.integrable_iteratedFDeriv_fourierSMulRight_normalizedIntDyadicMikhlinPiece` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.pow_norm_fourierInv_fourierSMulRight_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.integral_norm_le_uniform_and_power_decay` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.normalizedMikhlinKernelFrequencyL1Bound` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.normalizedMikhlinKernelIBPBound` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.normalizedMikhlinKernelL1Bound` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.integral_norm_fourierInv_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.normalizedMikhlinKernelDerivativeFrequencyL1Bound` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.normalizedMikhlinKernelDerivativeIBPBound` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.normalizedMikhlinKernelDerivativeL1Bound` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.integral_norm_fderiv_fourierInv_normalizedIntDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.contDiff_one_fourierInv_normalizedIntDyadicMikhlinPiece` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.contDiff_one_fourierInv_normalizedIntDyadicMikhlinPiece_at` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.integral_norm_fderiv_fourierInv_intDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.integral_norm_sub_translate_fourierInv_intDyadicMikhlinPiece_le` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin kernels | `Codex.Spherical.MikhlinHormander.norm_fourierInv_intDyadicMikhlinPiece_le_tail` | Proof completed | 2026-08-14 01:05:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.symmetricIntegerDyadicCutoff` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.finiteSymmetricMikhlinTruncation` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.finiteSymmetricMikhlinTruncation_apply` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.symmetricIntegerDyadicCutoff_eq_lowpass_difference` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.norm_symmetricIntegerDyadicCutoff_le_two` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.norm_symmetricIntegerDyadicCutoff_sub_one_le_three` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.symmetricIntegerDyadicCutoff_eq_one_of_bounds` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.eventually_norm_le_upper_symmetric_dyadic_scale` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.symmetric_lower_dyadic_scale_eq` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.eventually_lower_symmetric_dyadic_scale_le_norm` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.eventually_symmetricIntegerDyadicCutoff_eq_one` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.tendsto_symmetricIntegerDyadicCutoff` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.tendsto_fourierInv_of_dominated_convergence` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.continuous_symmetricIntegerDyadicCutoff` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.integrable_intDyadicBandpass_mul_punctured_fourier` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.integrable_symmetricIntegerDyadicCutoff_mul_punctured_fourier` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.continuous_finiteSymmetricMikhlinTruncation` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.fourierInv_finset_sum_of_integrable` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.finiteSymmetricMikhlinTruncation_eq_sum_dyadic_pieces` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.intDyadicBandpassMultiplier_mul_aux_puncturedSymbol_eq` | Proof completed | 2026-08-14 01:15:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.finiteSymmetricMikhlinTruncation_eq_sum_raw_dyadic_pieces` | Proof completed | 2026-08-14 01:15:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.measurable_aux_puncturedSymbol_of_mikhlin` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.norm_aux_puncturedSymbol_le_of_mikhlin` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.tendsto_finiteSymmetricMikhlinTruncation` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.eLpNorm_mikhlinMultiplier_le_of_uniform_finiteSymmetricMikhlinTruncation` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.exists_eLpNorm_mikhlinMultiplier_of_uniform_finiteSymmetricMikhlinTruncation` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.eLpNorm_mikhlinMultiplier_le_of_uniform_dyadic_pieces` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.eLpNorm_mikhlinMultiplier_le_of_uniform_finiteSymmetricMikhlinTruncation_of_mikhlin` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.eLpNorm_mikhlinMultiplier_le_of_uniform_dyadic_pieces_of_mikhlin` | Proof completed | 2026-08-14 01:12:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.eLpNorm_mikhlinMultiplier_le_of_uniform_raw_dyadic_pieces` | Proof completed | 2026-08-14 01:16:00 -04:00 |
| Dimension-generic raw Mikhlin reassembly | `Codex.Spherical.MikhlinHormander.eLpNorm_mikhlinMultiplier_le_of_uniform_raw_dyadic_pieces_of_mikhlin` | Proof completed | 2026-08-14 01:16:00 -04:00 |
| Dimension-generic raw-core duality | `Codex.Spherical.MikhlinHormander.eLpNorm_rawCoreOutput_le_of_formalAdjoint_lower` | Proof completed | 2026-08-14 01:34:00 -04:00 |
| Dimension-generic raw-core interpolation | `Codex.Spherical.MikhlinHormander.lowerLp_rawCore_of_weak_one_square` | Proof completed | 2026-08-14 01:34:00 -04:00 |
| Dimension-generic raw-core all-p interpolation | `Codex.Spherical.MikhlinHormander.exists_strongLp_rawCore_of_weak_one_square_adjoint` | Proof completed | 2026-08-14 01:34:00 -04:00 |
| Dimension-generic uniform raw-core all-p interpolation | `Codex.Spherical.MikhlinHormander.exists_uniform_strongLp_rawCore_of_weak_one_square_adjoint` | Proof completed | 2026-08-14 02:32:29 -04:00 |
| Dimension-generic finite raw Mikhlin all-p endpoint | `Codex.Spherical.MikhlinHormander.exists_uniform_strongLp_rawFiniteIntDyadicMikhlinKernelOperator` | Proof completed | 2026-08-14 02:32:29 -04:00 |
| Dimension-generic raw Mikhlin Fatou reassembly | `Codex.Spherical.MikhlinHormander.exists_uniform_strongLp_mikhlinMultiplier_withCutoffs` | Proof completed | 2026-08-14 02:32:29 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.mikhlin` | Proof completed | 2026-08-14 02:32:29 -04:00 |
| `thm:mikhlin` planar third-order corollary | `Codex.Spherical.MikhlinHormander.mikhlin_two` | Proof completed | 2026-08-14 02:32:29 -04:00 |
| Dimension-generic convolution duality | `Codex.Spherical.MikhlinHormander.integral_finiteConvolutionKernel_mul_star_eq_physicalAdjoint` | Proof completed | 2026-08-14 01:34:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinKernel` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.integrable_fourierInv_intDyadicMikhlinPiece` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.integrable_rawFiniteIntDyadicMikhlinKernel` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.norm_rawFiniteIntDyadicMikhlinKernel_sub_translate_le_sum` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.integrable_rawFiniteIntDyadicMikhlinKernel_sub_translate` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.integrable_rawFiniteIntDyadicMikhlinKernel_translation_majorant` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.integral_norm_rawFiniteIntDyadicMikhlinKernel_sub_translate_le_sum` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.low_rawFiniteIntDyadicMikhlinKernel_translation_bound` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinKernel_split_at` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.normalizedMikhlinKernelDerivativeL1Bound_nonneg` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.low_rawFiniteIntDyadicMikhlinKernel_atom_tail_le` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.raw_physical_tail_algebra` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.high_dyadic_inverse_power_term` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.sum_high_physicalFrequency_inv_pow_le` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.normalizedMikhlinKernelIBPBound_nonneg` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.high_rawFiniteIntDyadicMikhlinKernel_exterior_tail` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawExteriorPowerTail` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawExteriorPowerTail_nonneg` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.measurable_rawExteriorPowerTail` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.integrable_rawExteriorPowerTail` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawExteriorPowerTailAt` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawExteriorPowerTailAt_eq_scaled` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.integrable_rawExteriorPowerTailAt` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.integral_rawExteriorPowerTailAt` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.raw_high_scale_cancellation` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinHighTailConstant` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.high_rawFiniteIntDyadicMikhlinKernel_atom_tail_le` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinKernelCZTailConstant` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinHighTailConstant_nonneg` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinKernelCZTailConstant_nonneg` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin kernel C-Z tail | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinKernel_atom_tail_le` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| `lem:calderon-zygmund-tail` | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinKernel_hasFiniteConvolutionKernelCZTail` | Proof completed | 2026-08-14 02:15:00 -04:00 |
| Dimension-generic finite raw Mikhlin physical realization | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinSymbol` | Proof completed | 2026-08-14 02:01:14 -04:00 |
| Dimension-generic finite raw Mikhlin physical realization | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinMultiplier` | Proof completed | 2026-08-14 02:01:14 -04:00 |
| Dimension-generic finite raw Mikhlin physical realization | `Codex.Spherical.MikhlinHormander.fourier_rawFiniteIntDyadicMikhlinKernel_eq_symbol` | Proof completed | 2026-08-14 02:01:14 -04:00 |
| Dimension-generic finite raw Mikhlin physical realization | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinMultiplier_eq_convolution` | Proof completed | 2026-08-14 02:01:14 -04:00 |
| Dimension-generic finite raw Mikhlin physical realization | `Codex.Spherical.MikhlinHormander.symmetricRawFiniteIntDyadicMikhlinEmbedding` | Proof completed | 2026-08-14 02:01:14 -04:00 |
| Dimension-generic finite raw Mikhlin physical realization | `Codex.Spherical.MikhlinHormander.symmetricRawFiniteIntDyadicMikhlinIndex` | Proof completed | 2026-08-14 02:01:14 -04:00 |
| Dimension-generic finite raw Mikhlin physical realization | `Codex.Spherical.MikhlinHormander.finiteSymmetricMikhlinTruncation_eq_rawFiniteIntDyadicMikhlinConvolution` | Proof completed | 2026-08-14 02:01:14 -04:00 |
| Dimension-generic finite raw Mikhlin physical adjoint | `Codex.Spherical.MikhlinHormander.star_neg_rawFiniteIntDyadicMikhlinKernel_eq` | Proof completed | 2026-08-14 02:01:14 -04:00 |
| Dimension-generic finite raw Mikhlin physical adjoint | `Codex.Spherical.MikhlinHormander.convolutionPhysicalAdjoint_rawFiniteIntDyadicMikhlinKernel_eq` | Proof completed | 2026-08-14 02:01:14 -04:00 |
| Dimension-generic finite raw Mikhlin L2 realization | `Codex.Spherical.MikhlinHormander.continuous_rawFiniteIntDyadicMikhlinSymbol` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin L2 realization | `Codex.Spherical.MikhlinHormander.aestronglyMeasurable_rawFiniteIntDyadicMikhlinSymbol` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin L2 realization | `Codex.Spherical.MikhlinHormander.norm_rawFiniteIntDyadicMikhlinSymbol_le_four_mul` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin L2 realization | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinL2` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin L2 realization | `Codex.Spherical.MikhlinHormander.norm_rawFiniteIntDyadicMikhlinL2_le_four_mul` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin L2 realization | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinKernel_ae_eq_l2` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin L2 realization | `Codex.Spherical.MikhlinHormander.finiteConvolutionKernelOperator_rawFiniteIntDyadicMikhlinKernel_ae_eq_l2` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin L2 endpoint | `Codex.Spherical.MikhlinHormander.hasFiniteConvolutionKernelGoodL2Bound_rawFiniteIntDyadicMikhlinKernel` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin operator regularity | `Codex.Spherical.MikhlinHormander.integrable_finiteConvolutionKernelOperator_rawFiniteIntDyadicMikhlinKernel` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin operator regularity | `Codex.Spherical.MikhlinHormander.aestronglyMeasurable_finiteConvolutionKernelOperator_rawFiniteIntDyadicMikhlinKernel` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin operator algebra | `Codex.Spherical.MikhlinHormander.finiteConvolutionKernelOperator_rawFiniteIntDyadicMikhlinKernel_add` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin L2 endpoint | `Codex.Spherical.MikhlinHormander.lintegral_norm_sq_rawFiniteIntDyadicMikhlinKernelOperator_le` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin L2 endpoint | `Codex.Spherical.MikhlinHormander.eLpNorm_two_rawFiniteIntDyadicMikhlinKernelOperator_le` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin upper-Lp endpoint | `Codex.Spherical.MikhlinHormander.memLp_rawFiniteIntDyadicMikhlinKernelOperator` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin weak endpoint | `Codex.Spherical.MikhlinHormander.continuous_rawFiniteIntDyadicMikhlinKernel` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin weak endpoint | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinKernelBound` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin weak endpoint | `Codex.Spherical.MikhlinHormander.norm_rawFiniteIntDyadicMikhlinKernel_le_kernelBound` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic finite raw Mikhlin weak endpoint | `Codex.Spherical.MikhlinHormander.weak_one_rawFiniteIntDyadicMikhlinKernel` | Proof completed | 2026-08-14 02:30:00 -04:00 |
| Dimension-generic raw Mikhlin adjoint | `Codex.Spherical.MikhlinHormander.mikhlinCondition_conj` | Proof completed | 2026-08-14 02:26:16 -04:00 |
| Dimension-generic raw Mikhlin operator algebra | `Codex.Spherical.MikhlinHormander.rawFiniteIntDyadicMikhlinMultiplier_add` | Proof completed | 2026-08-14 02:26:16 -04:00 |
| Dimension-generic raw Mikhlin adjoint | `Codex.Spherical.MikhlinHormander.integral_rawFiniteIntDyadicMikhlinConvolution_mul_star_eq` | Proof completed | 2026-08-14 02:26:16 -04:00 |
| Dimension-generic raw Mikhlin adjoint | `Codex.Spherical.MikhlinHormander.integral_rawFiniteIntDyadicMikhlinMultiplier_mul_star_eq` | Proof completed | 2026-08-14 02:26:16 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierRaw` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplier` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.exists_relativeSchwartzMultiplier_majorant` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplier_aestronglyMeasurable` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.weak_one_of_dyadicBall_majorant_fixed` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.weak_one_of_dyadicBall_majorant` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplier_weak_one` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplier_strong_type` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierKernelSize` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierGeometricFactor` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierKernel` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierKernelHormanderSize` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.integrable_fderiv_fourierInv_schwartzMultiplierKernel` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierKernelHormanderSize_nonneg` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.fourierInv_relativeSchwartzMultiplier_eq_convolution` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.integral_norm_relativeSchwartzMultiplierKernel_sub_translate_le` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.uniform_integral_norm_relativeSchwartzMultiplierKernel_sub_translate_le` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplier_majorant_of_kernel_bound` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.uniform_relativeSchwartzMultiplier_majorant_of_kernel_bound` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.uniform_relativeSchwartzMultiplier_weak_one_of_majorant` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.uniform_relativeSchwartzMultiplier_weak_one_of_kernel_bound` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.uniform_relativeSchwartzMultiplier_strong_type_of_majorant` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.uniform_relativeSchwartzMultiplier_strong_type_of_kernel_bound` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.strong_type_of_dyadicBall_majorant` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierAt` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteRelativeSchwartzMultiplier` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.continuous_relativeSchwartzMultiplierAt` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.continuous_finiteRelativeSchwartzMultiplier` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.uniform_relativeSchwartzMultiplierAt_majorant_of_kernel_bound` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteRelativeSchwartzMultiplier_majorant_of_term_majorant` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteRelativeSchwartzMultiplier_strong_type_of_term_majorant` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteRelativeSchwartzMultiplier_strong_type_of_kernel_bound` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteRelativeSchwartzMultiplier_weak_one_of_term_majorant` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteRelativeSchwartzMultiplier_weak_one_of_kernel_bound` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.countableRelativeSchwartzMultiplier` | Proof completed | 2026-08-13 14:23:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.summable_countableRelativeSchwartzMultiplier_terms` | Proof completed | 2026-08-13 14:23:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.tendsto_sum_range_countableRelativeSchwartzMultiplier` | Proof completed | 2026-08-13 14:23:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.measurable_countableRelativeSchwartzMultiplier` | Proof completed | 2026-08-13 14:23:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.norm_countableRelativeSchwartzMultiplier_le` | Proof completed | 2026-08-13 14:23:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.countableRelativeSchwartzMultiplier_strong_type_of_term_majorant` | Proof completed | 2026-08-13 14:23:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.countableRelativeSchwartzMultiplier_strong_type_of_kernel_bound` | Proof completed | 2026-08-13 14:23:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.annularSchwartzMultiplierRaw` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.annularSchwartzMultiplier` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.annularSchwartzMultiplier_nonneg` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.annularSchwartzMultiplier_aestronglyMeasurable` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.annularSchwartzMultiplier_majorant_of_term_majorant` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.annularSchwartzMultiplier_majorant_of_kernel_bound` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.annularSchwartzMultiplier_strong_type_of_term_majorant` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.annularSchwartzMultiplier_strong_type_of_kernel_bound` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.annularSchwartzMultiplier_weak_one_of_kernel_bound` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.dyadicFrequencyScale` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.fatDyadicBandpassPrototype` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| Dimension-generic fat-annular cutoff support | `Codex.Spherical.MikhlinHormander.fatDyadicBandpassPrototype_eq_zero_of_norm_le` | Proof completed | 2026-08-14 05:54:53 -04:00 |
| Dimension-generic fat-annular cutoff support | `Codex.Spherical.MikhlinHormander.fatDyadicBandpassPrototype_eq_zero_of_le_norm` | Proof completed | 2026-08-14 05:54:53 -04:00 |
| Dimension-generic fat-annular cutoff support | `Codex.Spherical.MikhlinHormander.hasCompactSupport_fatDyadicBandpassPrototype` | Proof completed | 2026-08-14 05:54:53 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.intDyadicLowpassMultiplier_add_apply` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.fatDyadicBandpassMultiplier_eq_prototype_scale` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.fourierInv_fatDyadicBandpassMultiplier_eq_relativeSchwartzMultiplierAt` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.fatDyadicBandpassMultiplierMaximal` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.fatDyadicBandpassMultiplierMaximal_eq_annularSchwartzMultiplier` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.fatDyadicBandpassMultiplierMaximal_strong_type` | Proof completed | 2026-08-13 15:10:36 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierSymbol` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierSymbol_apply` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.relativeSchwartzMultiplierAt_eq_fourierInv_symbol` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteRelativeSchwartzMultiplierSquareEnergy` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteRelativeSchwartzMultiplierSquareFunction` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteRelativeSchwartzMultiplierSquareEnergy_nonneg` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.sq_finiteRelativeSchwartzMultiplierSquareFunction` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.integral_finiteRelativeSchwartzMultiplierSquareEnergy_eq_frequency` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.integral_finiteRelativeSchwartzMultiplierSquareEnergy_eq_frequency_overlap` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.integral_finiteRelativeSchwartzMultiplierSquareEnergy_le_of_square_overlap` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.integral_finiteRelativeSchwartzMultiplierSquareEnergy_le_of_scaled_square_overlap` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.integral_sq_finiteRelativeSchwartzMultiplierSquareFunction_le_of_scaled_square_overlap` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finite_sum_norm_intDyadicBandpassMultiplier_le_four` | Proof completed | 2026-08-13 16:14:56 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteSignedIntegerDyadicMultiplierSymbol` | Proof completed | 2026-08-13 16:14:56 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteSignedIntegerDyadicMultiplierSymbol_apply` | Proof completed | 2026-08-13 16:14:56 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.norm_finiteSignedIntegerDyadicMultiplierSymbol_le_four` | Proof completed | 2026-08-13 16:14:56 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteSignedIntegerDyadicMultiplier` | Proof completed | 2026-08-13 16:14:56 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.finiteSignedIntegerDyadicMultiplier_eq_sum_integerDyadicProjection` | Proof completed | 2026-08-13 16:14:56 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.integral_norm_sq_finiteSignedIntegerDyadicMultiplier_le` | Proof completed | 2026-08-13 16:14:56 -04:00 |
| `thm:mikhlin` | `Codex.Spherical.MikhlinHormander.integral_norm_sq_sum_integerDyadicProjection_le` | Proof completed | 2026-08-13 16:14:56 -04:00 |
| Dimension-generic signed-multiplier adjoint | `Codex.Spherical.MikhlinHormander.conjugateLpCutoffs` | Proof completed | 2026-08-13 23:21:37 -04:00 |
| Dimension-generic signed-multiplier adjoint | `Codex.Spherical.MikhlinHormander.intDyadicBandpassMultiplier_conjugateLpCutoffs_apply` | Proof completed | 2026-08-13 23:21:37 -04:00 |
| Dimension-generic signed-multiplier adjoint | `Codex.Spherical.MikhlinHormander.adjoint_finiteSignedIntegerDyadicMultiplierSymbol_eq` | Proof completed | 2026-08-13 23:21:37 -04:00 |
| Dimension-generic signed-multiplier adjoint | `Codex.Spherical.MikhlinHormander.integral_finiteSignedIntegerDyadicMultiplier_mul_star_eq` | Proof completed | 2026-08-13 23:21:37 -04:00 |
| Dimension-generic interpolation core | `Codex.Spherical.MikhlinHormander.lowerLp_of_schwartz_additive_weak_one_square` | Proof completed | 2026-08-14 00:11:00 -04:00 |
| Dimension-generic interpolation core | `Codex.Spherical.MikhlinHormander.eLpNorm_schwartzCore_le_of_formalAdjoint_lower` | Proof completed | 2026-08-14 00:15:00 -04:00 |
| `def:calderon-zygmund` | `Codex.Spherical.MikhlinHormander.finiteConvolutionKernelOperator` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `def:calderon-zygmund` | `Codex.Spherical.MikhlinHormander.finiteConvolutionKernelBadTail` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `lem:calderon-zygmund-decomposition` | `Codex.Spherical.MikhlinHormander.finiteConvolutionKernelOperator_decomposition` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `lem:calderon-zygmund-decomposition` | `Codex.Spherical.MikhlinHormander.finiteConvolutionKernel_level_subset_good_union_badTail` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `def:calderon-zygmund` | `Codex.Spherical.MikhlinHormander.HasFiniteConvolutionKernelL2Bound` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `def:calderon-zygmund` | `Codex.Spherical.MikhlinHormander.HasFiniteConvolutionKernelGoodL2Bound` | Proof completed | 2026-08-13 23:30:00 -04:00 |
| `lem:calderon-zygmund-good` | `Codex.Spherical.MikhlinHormander.HasFiniteConvolutionKernelL2Bound.to_good` | Proof completed | 2026-08-13 23:30:00 -04:00 |
| `lem:calderon-zygmund-good` | `Codex.Spherical.MikhlinHormander.hasFiniteConvolutionKernelGoodL2Bound_of_schwartz_core` | Proof completed | 2026-08-13 23:42:00 -04:00 |
| `lem:calderon-zygmund-good` | `Codex.Spherical.MikhlinHormander.hasFiniteConvolutionKernelGoodL2Bound_finiteSignedIntegerDyadicBandpassKernel` | Proof completed | 2026-08-13 23:58:00 -04:00 |
| `def:calderon-zygmund` | `Codex.Spherical.MikhlinHormander.HasFiniteConvolutionKernelCZTail` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `lem:calderon-zygmund-tail` | `Codex.Spherical.MikhlinHormander.finiteConvolutionKernelBadTail_nonneg` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `lem:calderon-zygmund-tail` | `Codex.Spherical.MikhlinHormander.finiteConvolutionKernelBadTail_weak_one_of_integral_bound` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `lem:calderon-zygmund-good` | `Codex.Spherical.MikhlinHormander.finiteConvolutionKernel_good_level_ennreal` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `def:calderon-zygmund` | `Codex.Spherical.MikhlinHormander.finiteConvolutionKernelWeakOneConstant` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `thm:calderon-zygmund-weak-one` | `Codex.Spherical.MikhlinHormander.weak_one_finiteConvolutionKernel_of_L2_and_CZTail` | Proof completed | 2026-08-13 17:01:27 -04:00 |
| `thm:calderon-zygmund-weak-one` | `Codex.Spherical.MikhlinHormander.weak_one_finiteConvolutionKernel_of_goodL2_and_CZTail` | Proof completed | 2026-08-13 23:30:00 -04:00 |

## `LeanSpherical/Codex/Spherical/LittlewoodPaley.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| `def:intro-lp-cutoffs` | `Codex.Spherical.LittlewoodPaley.LPCutoffs` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-lp-cutoffs` | `Codex.Spherical.LittlewoodPaley.lpCutoffs` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-lp-cutoffs` | `Codex.Spherical.LittlewoodPaley.exists_lpCutoffs` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-lp-cutoffs` | `Codex.Spherical.LittlewoodPaley.dyadicLowpassMultiplier` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-lp-cutoffs` | `Codex.Spherical.LittlewoodPaley.dyadicLowpassMultiplier_apply` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-lp-cutoffs` | `Codex.Spherical.LittlewoodPaley.dyadicBandpassMultiplier` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-lp-cutoffs` | `Codex.Spherical.LittlewoodPaley.dyadicBandpassMultiplier_apply` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-lp-cutoffs` | `Codex.Spherical.LittlewoodPaley.dyadicProjection` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-lp-cutoffs` | `Codex.Spherical.LittlewoodPaley.dyadicBandpass_eq_zero_of_norm_le` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-lp-cutoffs` | `Codex.Spherical.LittlewoodPaley.dyadicBandpass_eq_zero_of_le_norm` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.finiteDyadicResolution` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.homogeneousDyadicResolutionFinite` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.finiteIntegerDyadicResolution` | Proof completed | 2026-08-13 13:59:33 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.finiteIntegerDyadicMultiplierResolution` | Proof completed | 2026-08-13 13:59:33 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.finiteSymmetricIntegerDyadicResolution` | Proof completed | 2026-08-13 13:59:33 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.intDyadicLowpass_eq_one_of_norm_le` | Proof completed | 2026-08-13 13:59:33 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.intDyadicLowpass_eq_zero_of_le_norm` | Proof completed | 2026-08-13 13:59:33 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.finiteSymmetricIntegerDyadicAnnularReconstruction` | Proof completed | 2026-08-13 13:59:33 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.intDyadicBandpass_support_subset_of_norm_mem_Ico` | Proof completed | 2026-08-13 13:59:33 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.intDyadicBandpass_hasFiniteSupport_of_ne_zero` | Proof completed | 2026-08-13 13:59:33 -04:00 |
| `lem:homogeneous-dyadic-resolution` | `Codex.Spherical.LittlewoodPaley.homogeneousDyadicResolution` | Proof completed | 2026-08-13 13:59:33 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.norm_dyadicBandpassMultiplier_le_two` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.finiteLittlewoodPaleyL2` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.intDyadicLowpassMultiplier` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.intDyadicLowpassMultiplier_apply` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.intDyadicBandpassMultiplier` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.intDyadicBandpassMultiplier_apply` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.intDyadicBandpass_norm_bounds_of_ne_zero` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.norm_intDyadicBandpassMultiplier_le_two` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.intDyadicBandpass_square_overlap` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.integerLittlewoodPaleyL2` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.shiftedFatMultiplier` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.shiftedFatMultiplier_apply` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.fatDyadicBandpassMultiplier` | Proof completed | 2026-08-13 14:55:50 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.fatDyadicBandpassMultiplier_eq_shiftedFatMultiplier` | Proof completed | 2026-08-13 14:55:50 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.dyadicBandpassMultiplier_mul_fatDyadicBandpassMultiplier` | Proof completed | 2026-08-13 14:55:50 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.shiftedFatMultiplier_square_overlap` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.shiftedLittlewoodPaleyL2` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.finiteSquareEnergy` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.finiteSquareEnergy_sq_le_card_mul_sum_norm_four` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.integral_finiteSquareEnergy_sq_le_card_mul_sum_norm_four` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.finiteDyadicSquareEnergy` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.finiteDyadicSquareEnergy_sq_le_card_mul_sum_norm_four` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.finiteLittlewoodPaleyL4_of_term_bounds` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.dyadicProjectionKernelConstant` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.dyadicProjectionKernelConstant_nonneg` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.exists_dyadicProjection_majorant` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.finiteSquareEnergy_sq_le_card_sq_mul_of_majorant` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.finiteLittlewoodPaleyL4` | Proof completed | 2026-08-13 15:45:00 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.integerDyadicProjection` | Proof completed | 2026-08-13 15:47:13 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.finiteIntegerDyadicSquareEnergy` | Proof completed | 2026-08-13 15:47:13 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.uniformFiniteIntegerLittlewoodPaleyL4` | Statement completed | 2026-08-13 15:47:13 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.littlewoodPaley` | Proof completed | 2026-08-14 02:38:28 -04:00 |
| Completed file | `LeanSpherical/Codex/Spherical/LittlewoodPaley.lean` | Proof completed | 2026-08-14 02:38:28 -04:00 |
| `lem:rademacher-second-moment` | `Codex.Spherical.LittlewoodPaley.rademacherSign` | Proof completed | 2026-08-13 16:56:00 -04:00 |
| `lem:rademacher-second-moment` | `Codex.Spherical.LittlewoodPaley.rademacherSignedSum` | Proof completed | 2026-08-13 16:56:00 -04:00 |
| `lem:rademacher-second-moment` | `Codex.Spherical.LittlewoodPaley.rademacherSecondMoment` | Proof completed | 2026-08-13 16:56:00 -04:00 |
| `lem:rademacher-fourth-moment` | `Codex.Spherical.LittlewoodPaley.rademacherFourthMomentLower` | Proof completed | 2026-08-13 16:56:00 -04:00 |
| `lem:rademacher-fourth-moment` | `Codex.Spherical.LittlewoodPaley.integral_rademacherFourthMomentLower` | Proof completed | 2026-08-13 16:58:34 -04:00 |
| `def:rademacher-dyadic-sum` | `Codex.Spherical.LittlewoodPaley.finiteRademacherIntegerDyadicSum` | Proof completed | 2026-08-13 16:58:34 -04:00 |
| `def:rademacher-dyadic-sum` | `Codex.Spherical.LittlewoodPaley.HasUniformFiniteRademacherIntegerDyadicL4` | Proof completed | 2026-08-13 16:58:34 -04:00 |
| `lem:rademacher-lp-reduction` | `Codex.Spherical.LittlewoodPaley.uniformFiniteIntegerLittlewoodPaleyL4_of_signed` | Proof completed | 2026-08-13 16:58:34 -04:00 |
| `def:rademacher-lp` | `Codex.Spherical.LittlewoodPaley.HasUniformFiniteRademacherIntegerDyadicLp` | Proof completed | 2026-08-14 02:38:28 -04:00 |
| `def:rademacher-lp` | `Codex.Spherical.LittlewoodPaley.HasUniformFiniteRademacherIntegerDyadicLpAll` | Proof completed | 2026-08-14 02:38:28 -04:00 |
| `thm:littlewood-paley` | `Codex.Spherical.LittlewoodPaley.littlewoodPaley_of_uniform_signed` | Proof completed | 2026-08-14 02:38:28 -04:00 |

## `LeanSpherical/Codex/Spherical/OneDimStationaryPhase.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.quadraticOscillatoryIntegral` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.quadraticStationaryPhase_of_bounds` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.quadraticStationaryPhase` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.quadraticOscillatoryIntegral_neg_eq_conj` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.norm_quadraticOscillatoryIntegral_neg` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.quadraticOscillatoryIntegral_neg_eq_conj_conj` | Proof completed | 2026-08-14 02:46:40 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.quadraticStationaryPhase_abs` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.quadraticStationaryPhase_abs_complex` | Proof completed | 2026-08-14 02:46:40 -04:00 |
| `def:quadratic-normal-form` | `Codex.Spherical.OneDimStationaryPhase.quadraticNormalFormOscillatoryIntegral` | Proof completed | 2026-08-14 02:46:40 -04:00 |
| `lem:quadratic-normal-form` | `Codex.Spherical.OneDimStationaryPhase.quadraticNormalFormOscillatoryIntegral_eq` | Proof completed | 2026-08-14 02:46:40 -04:00 |
| `lem:quadratic-normal-form` | `Codex.Spherical.OneDimStationaryPhase.quadraticNormalFormStationaryPhase` | Proof completed | 2026-08-14 02:46:40 -04:00 |
| `lem:quadratic-normal-form` | `Codex.Spherical.OneDimStationaryPhase.quadraticOscillatoryIntegral_iteratedDeriv_abs` | Proof completed | 2026-08-14 02:54:07 -04:00 |
| `lem:quadratic-normal-form` | `Codex.Spherical.OneDimStationaryPhase.quadraticNormalFormStationaryPhase_iteratedDeriv` | Proof completed | 2026-08-14 02:54:07 -04:00 |
| `def:stationary-phase-transport` | `Codex.Spherical.OneDimStationaryPhase.stationaryOscillatoryIntegral` | Proof completed | 2026-08-14 03:05:00 -04:00 |
| `def:stationary-phase-transport` | `Codex.Spherical.OneDimStationaryPhase.normalizedStationaryOscillatoryIntegral` | Proof completed | 2026-08-14 03:05:00 -04:00 |
| `def:quadratic-normal-form` | `Codex.Spherical.OneDimStationaryPhase.HasQuadraticNormalForm` | Proof completed | 2026-08-14 03:05:00 -04:00 |
| `def:stationary-symbol` | `Codex.Spherical.OneDimStationaryPhase.HasHalfOrderStationarySymbol` | Proof completed | 2026-08-14 03:05:00 -04:00 |
| `lem:quadratic-normal-form` | `Codex.Spherical.OneDimStationaryPhase.HasQuadraticNormalForm.hasHalfOrderStationarySymbol` | Proof completed | 2026-08-14 03:05:00 -04:00 |
| `lem:local-morse-ift` | `Codex.Spherical.OneDimStationaryPhase.localInverse_of_contDiffAt_of_hasDerivAt_ne` | Proof completed | 2026-08-14 05:00:35 -04:00 |
| `def:local-morse-coordinate` | `Codex.Spherical.OneDimStationaryPhase.HasLocalQuadraticMorseCoordinate` | Proof completed | 2026-08-14 05:00:35 -04:00 |
| `def:local-morse-inverse` | `Codex.Spherical.OneDimStationaryPhase.HasLocalQuadraticMorseInverse` | Proof completed | 2026-08-14 05:00:35 -04:00 |
| `def:local-morse-ift` | `Codex.Spherical.OneDimStationaryPhase.HasLocalQuadraticMorseCoordinate.toHasLocalQuadraticMorseInverse` | Proof completed | 2026-08-14 05:00:35 -04:00 |
| `def:quadratic-hadamard-factor` | `Codex.Spherical.OneDimStationaryPhase.quadraticHadamardFactor` | Proof completed | 2026-08-14 05:04:59 -04:00 |
| `lem:quadratic-hadamard-factor` | `Codex.Spherical.OneDimStationaryPhase.phase_sub_eq_sq_mul_quadraticHadamardFactor` | Proof completed | 2026-08-14 05:04:59 -04:00 |
| `def:affine-moment-average` | `Codex.Spherical.OneDimStationaryPhase.affineMomentAverage` | Proof completed | 2026-08-14 05:52:59 -04:00 |
| `lem:affine-moment-average` | `Codex.Spherical.OneDimStationaryPhase.continuous_affineMomentAverage` | Proof completed | 2026-08-14 05:52:59 -04:00 |
| `lem:affine-moment-average` | `Codex.Spherical.OneDimStationaryPhase.hasDerivAt_affineMomentAverage` | Proof completed | 2026-08-14 05:52:59 -04:00 |
| `lem:affine-moment-average` | `Codex.Spherical.OneDimStationaryPhase.contDiff_infty_affineMomentAverage` | Proof completed | 2026-08-14 05:52:59 -04:00 |
| `def:quadratic-taylor-factor` | `Codex.Spherical.OneDimStationaryPhase.quadraticTaylorFactor` | Proof completed | 2026-08-14 05:52:59 -04:00 |
| `lem:quadratic-taylor-factor` | `Codex.Spherical.OneDimStationaryPhase.phase_sub_eq_sq_mul_quadraticTaylorFactor` | Proof completed | 2026-08-14 05:52:59 -04:00 |
| `lem:quadratic-taylor-factor` | `Codex.Spherical.OneDimStationaryPhase.contDiff_infty_quadraticTaylorFactor` | Proof completed | 2026-08-14 05:52:59 -04:00 |
| `lem:quadratic-taylor-factor` | `Codex.Spherical.OneDimStationaryPhase.quadraticTaylorFactor_at_criticalPoint` | Proof completed | 2026-08-14 05:52:59 -04:00 |
| `def:local-morse-coordinate` | `Codex.Spherical.OneDimStationaryPhase.HasLocalQuadraticMorseCoordinate.ofSmoothFactor` | Proof completed | 2026-08-14 05:52:59 -04:00 |
| `def:local-morse-coordinate` | `Codex.Spherical.OneDimStationaryPhase.HasLocalQuadraticMorseCoordinate.ofNondegenerate` | Proof completed | 2026-08-14 05:52:59 -04:00 |
| `def:local-morse-radius` | `Codex.Spherical.OneDimStationaryPhase.quadraticMorsePhaseRescale` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `lem:local-morse-radius` | `Codex.Spherical.OneDimStationaryPhase.contDiff_quadraticMorsePhaseRescale` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `lem:local-morse-radius` | `Codex.Spherical.OneDimStationaryPhase.HasLocalQuadraticMorseInverse.exists_pos_radius_phase_eq` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `lem:local-morse-radius` | `Codex.Spherical.OneDimStationaryPhase.exists_pos_radius_phase_eq_ofNondegenerate` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `def:quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.HasTwoBranchQuadraticMorseChart` | Proof completed | 2026-08-14 04:51:05 -04:00 |
| `def:radius-scaled-quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.HasRadiusScaledQuadraticNormalForm` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `def:radius-scaled-quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.HasRadiusScaledQuadraticMorseChart` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `def:radius-scaled-quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.HasRadiusScaledQuadraticMorseChart.toUnitChart` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `def:quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.twoBranchQuadraticTransportedAmplitude` | Proof completed | 2026-08-14 04:51:05 -04:00 |
| `lem:quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.contDiff_twoBranchQuadraticTransportedAmplitude` | Proof completed | 2026-08-14 04:51:05 -04:00 |
| `lem:quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.twoBranchQuadraticTransportedAmplitude_vanishesNearOne` | Proof completed | 2026-08-14 04:51:05 -04:00 |
| `def:quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.HasTwoBranchQuadraticMorseChart.toHasQuadraticNormalForm` | Proof completed | 2026-08-14 04:51:05 -04:00 |
| `lem:radius-scaled-quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.normalizedStationaryOscillatoryIntegral_quadraticMorsePhaseRescale` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `def:radius-scaled-quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.HasQuadraticNormalForm.toHasRadiusScaledQuadraticNormalForm` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `def:radius-scaled-quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.HasTwoBranchQuadraticMorseChart.toHasRadiusScaledQuadraticNormalForm` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `def:radius-scaled-quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.HasRadiusScaledQuadraticMorseChart.toHasRadiusScaledQuadraticNormalForm` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `lem:quadratic-normal-form` | `Codex.Spherical.OneDimStationaryPhase.contDiff_quadraticNormalFormOscillatoryIntegral` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `lem:radius-scaled-quadratic-morse-chart` | `Codex.Spherical.OneDimStationaryPhase.HasRadiusScaledQuadraticNormalForm.hasScaledHalfOrderStationarySymbol` | Proof completed | 2026-08-14 06:13:48 -04:00 |
| `def:stationary-phase-remainder` | `Codex.Spherical.OneDimStationaryPhase.HasRapidDecayRemainder` | Proof completed | 2026-08-14 04:11:34 -04:00 |
| `def:stationary-phase-expansion` | `Codex.Spherical.OneDimStationaryPhase.HasStationaryPhaseExpansion` | Proof completed | 2026-08-14 04:11:34 -04:00 |
| `lem:stationary-phase-transport` | `Codex.Spherical.OneDimStationaryPhase.stationaryOscillatoryIntegral_eq_phase_mul_normalized` | Proof completed | 2026-08-14 04:11:34 -04:00 |
| `thm:stationary-phase (conditional composition)` | `Codex.Spherical.OneDimStationaryPhase.stationaryPhase_of_normalForm_and_rapidRemainder` | Proof completed | 2026-08-14 04:11:34 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.nonstationaryPhase` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.nonstationaryPhaseExp` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.norm_nonstationaryPhaseExp` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.HasNonstationaryPhaseIBPChain` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.intervalIntegral_mul_nonstationaryPhaseExp_eq_neg_inv_mul` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.nonstationaryPhase_of_chain` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.exists_nonstationaryPhaseBound_of_chain` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `def:stationary-phase-moment` | `Codex.Spherical.OneDimStationaryPhase.stationaryPhaseMomentIntegral` | Proof completed | 2026-08-14 04:27:27 -04:00 |
| `lem:stationary-phase-parameter-derivative` | `Codex.Spherical.OneDimStationaryPhase.hasDerivAt_stationaryPhaseMomentIntegral` | Proof completed | 2026-08-14 04:27:27 -04:00 |
| `lem:stationary-phase-parameter-derivative` | `Codex.Spherical.OneDimStationaryPhase.iteratedDeriv_stationaryOscillatoryIntegral_eq_stationaryPhaseMomentIntegral` | Proof completed | 2026-08-14 04:27:27 -04:00 |
| `def:nonstationary-remainder-data` | `Codex.Spherical.OneDimStationaryPhase.HasNonstationaryRapidDecayData` | Proof completed | 2026-08-14 04:27:27 -04:00 |
| `lem:nonstationary-remainder` | `Codex.Spherical.OneDimStationaryPhase.HasNonstationaryRapidDecayData.hasRapidDecayRemainder` | Proof completed | 2026-08-14 04:27:27 -04:00 |
| `def:nonstationary-ibp` | `Codex.Spherical.OneDimStationaryPhase.nonstationaryIBPAmplitude` | Proof completed | 2026-08-14 04:36:39 -04:00 |
| `lem:nonstationary-ibp` | `Codex.Spherical.OneDimStationaryPhase.contDiff_nonstationaryIBPAmplitude` | Proof completed | 2026-08-14 04:36:39 -04:00 |
| `lem:nonstationary-ibp` | `Codex.Spherical.OneDimStationaryPhase.nonstationaryIBPAmplitude_eventuallyEq_zero` | Proof completed | 2026-08-14 04:36:39 -04:00 |
| `lem:nonstationary-ibp` | `Codex.Spherical.OneDimStationaryPhase.hasNonstationaryPhaseIBPChain_nonstationaryIBPAmplitude_of_contDiff` | Proof completed | 2026-08-14 04:36:39 -04:00 |
| `def:nonstationary-remainder-data (smooth)` | `Codex.Spherical.OneDimStationaryPhase.nonstationaryRapidDecayData_of_contDiff` | Proof completed | 2026-08-14 04:36:39 -04:00 |
| `lem:nonstationary-remainder (smooth)` | `Codex.Spherical.OneDimStationaryPhase.hasRapidDecayRemainder_of_contDiff` | Proof completed | 2026-08-14 04:36:39 -04:00 |
| `def:nonstationary-remainder-data (derivative)` | `Codex.Spherical.OneDimStationaryPhase.nonstationaryRapidDecayData_of_contDiff_deriv` | Proof completed | 2026-08-14 04:36:39 -04:00 |
| `lem:nonstationary-remainder (derivative)` | `Codex.Spherical.OneDimStationaryPhase.hasRapidDecayRemainder_of_contDiff_deriv` | Proof completed | 2026-08-14 04:36:39 -04:00 |
| `thm:stationary-phase` | `Codex.Spherical.OneDimStationaryPhase.stationaryPhase` | ToDo | 2026-08-13 13:24:00 -04:00 |

## `LeanSpherical/Codex/Spherical/RieszThorin.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| File completion | `LeanSpherical/Codex/Spherical/RieszThorin.lean` | Proof completed | 2026-08-13 22:06:39 -04:00 |
| `thm:riesz-thorin` main theorem (finite interior; supports `p1 = infinity`) | `Codex.Spherical.RieszThorin.rieszThorin` | Proof completed | 2026-08-13 22:01:06 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.ScalarAnalyticFamily` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.OperatorAnalyticFamily` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.hadamardThreeLines` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.scalarThreeLines` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.scalarThreeLines_unit` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.operatorPairingThreeLines` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.operatorThreeLines_apply_of_dualBounds` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.operatorThreeLines_apply` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.operatorNormThreeLines` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.operatorNormThreeLines_unit` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.eLpNorm_four_rpow_two_le_of_two_top_operator_bounds` | Proof completed | 2026-08-13 15:37:48 -04:00 |
| `thm:riesz-thorin` | `Codex.Spherical.RieszThorin.eLpNorm_four_rpow_two_le_of_two_top_operator_count` | Proof completed | 2026-08-13 15:37:48 -04:00 |
| `foundation:analytic-pairing` | `Codex.Spherical.RieszThorin.RieszThorinAnalyticDatum` | Proof completed | 2026-08-13 17:18:50 -04:00 |
| `foundation:analytic-pairing` | `Codex.Spherical.RieszThorin.rieszThorin_of_analyticDatum` | Proof completed | 2026-08-13 17:25:13 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorin_q_top_lintegral` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorin_ofReal_rpow_weight_q` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorin_q_top_lintegral_source_output` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorin_q_top_memLp_source_output` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinQTopConstant` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorin_q_top` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinQTopScaledConstant` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorin_q_top_scaled` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorin_two_top_four` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorin_q_top_scaled_of_additive` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:real-interpolation` | `Codex.Spherical.RieszThorin.rieszThorin_two_top_four_of_additive` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicCpow` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_finiteAtomicCpow` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicPowerFamily` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_finiteAtomicPowerFamily` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_finiteAtomicPowerFamily_le_rpow` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_finiteAtomicPowerFamily_eq_rpow_of_re_pos` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicPowerFamily_apply_of_exponent_one` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopInputExponent` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopTestExponent` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_finiteAtomicTwoTopInputExponent` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_finiteAtomicTwoTopTestExponent` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopInputExponent_half` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopTestExponent_half` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopInputExponent_re` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopTestExponent_re` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomic_coordinate_norm_le_one_of_sum_four_le_one` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicPowerFamily_norm_le_one_of_norm_le_one` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicPowerFamily_norm_le_square_max` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopInput_left_square_norm` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopTest_left_square_norm` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopTest_right_one_norm` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicPairing` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_finiteAtomicPairing` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicPairing_analytic` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopPairing_bddAbove` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomic_sum_norm_mul_le_sqrt` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopPairing_left_bound` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopPairing_right_bound` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopPairing_midpoint_bound` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicPhase` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicDualTest` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomic_mul_phase` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicDualTest_pair` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicPhase_norm_le_one` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicDualTest_norm_le` | Proof completed | 2026-08-13 18:40:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicDualTest_moment_le_one` | Proof completed | 2026-08-13 18:42:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicDualTest_pairing_eq` | Proof completed | 2026-08-13 18:42:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomic_exists_l4_dualTest` | Proof completed | 2026-08-13 18:42:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicL4Norm` | Proof completed | 2026-08-13 18:42:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopFour_normalized` | Proof completed | 2026-08-13 18:42:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicL4Norm_smul` | Proof completed | 2026-08-13 18:46:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicL4Norm_pow_four` | Proof completed | 2026-08-13 18:46:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomic_sum_norm_four_eq_coe` | Proof completed | 2026-08-13 18:48:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicL4Norm_eq_zero_iff` | Proof completed | 2026-08-13 18:48:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopFour` | Proof completed | 2026-08-13 18:56:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVectorPowerFamily` | Proof completed | 2026-08-13 19:00:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_finiteAtomicVectorPowerFamily` | Proof completed | 2026-08-13 19:00:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_finiteAtomicVectorPowerFamily_le_rpow` | Proof completed | 2026-08-13 19:00:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_finiteAtomicVectorPowerFamily_eq_rpow_of_re_pos` | Proof completed | 2026-08-13 19:06:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVectorPowerFamily_apply_of_exponent_one` | Proof completed | 2026-08-13 19:06:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVectorPowerFamily_norm_le_one_of_norm_le_one` | Proof completed | 2026-08-13 19:06:00 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVectorPowerFamily_norm_le_square_max` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVectorPairing` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_finiteAtomicVectorPairing` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVectorPairing_analytic` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopVectorPairing_bddAbove` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopVectorInput_left_square_norm` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopVectorPairing_left_bound` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopVectorPairing_right_bound` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopVectorPairing_midpoint_bound` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopFour_vector_normalized` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVectorL4Norm` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVectorL4Norm_smul` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVectorL4Norm_pow_four` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVector_sum_norm_four_eq_coe` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicVectorL4Norm_eq_zero_iff` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:finite-atomic-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicTwoTopFour_vector` | Proof completed | 2026-08-13 19:12:05 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPowerFamily` | Proof completed | 2026-08-13 19:17:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPowerFamily_apply` | Proof completed | 2026-08-13 19:17:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPowerFamily_apply_of_exponent_one` | Proof completed | 2026-08-13 19:17:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_finiteSimpleVectorPowerFamily_le_rpow` | Proof completed | 2026-08-13 19:17:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_finiteSimpleVectorPowerFamily_eq_rpow_of_re_pos` | Proof completed | 2026-08-13 19:17:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPowerFamily_finMeasSupp` | Proof completed | 2026-08-13 19:17:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleNonzeroRange` | Proof completed | 2026-08-13 19:24:53 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorAtom` | Proof completed | 2026-08-13 19:24:53 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorAtom_apply` | Proof completed | 2026-08-13 19:24:53 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_sum_smul_atom_apply` | Proof completed | 2026-08-13 19:24:53 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPowerFamily_eq_sum_atoms` | Proof completed | 2026-08-13 19:24:53 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorAtom_memLp_of_memLp` | Proof completed | 2026-08-13 19:30:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_differentiable_finset_sum` | Proof completed | 2026-08-13 19:35:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing` | Proof completed | 2026-08-13 19:35:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_finiteSimpleVectorPairing` | Proof completed | 2026-08-13 19:35:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_analytic` | Proof completed | 2026-08-13 19:35:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_integral_mul_scalar_atom` | Proof completed | 2026-08-13 19:35:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_pairing_expand` | Proof completed | 2026-08-13 19:35:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_pairing_expand_atoms` | Proof completed | 2026-08-13 19:39:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPowerFamily_map_eq_sum_atoms` | Proof completed | 2026-08-13 19:39:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_source_pairing_expand` | Proof completed | 2026-08-13 19:39:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_eq_integral` | Proof completed | 2026-08-13 19:42:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPowerFamily_memLp_of_memLp` | Proof completed | 2026-08-13 19:42:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_finiteSimpleVectorPowerFamily_eq_rpow` | Proof completed | 2026-08-13 19:44:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_two_mul_ofReal_two_div_three` | Proof completed | 2026-08-13 19:50:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_finiteSimpleTwoTopInput_left` | Proof completed | 2026-08-13 19:50:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_finiteSimpleTwoTopTest_left` | Proof completed | 2026-08-13 19:50:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_finiteSimpleTwoTopTest_right` | Proof completed | 2026-08-13 19:50:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_finiteSimpleTwoTopInput_right_le_one` | Proof completed | 2026-08-13 19:50:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleTwoTopInput_left_memLp` | Proof completed | 2026-08-13 20:01:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleTwoTopTest_left_memLp` | Proof completed | 2026-08-13 20:01:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleTwoTopTest_right_memLp` | Proof completed | 2026-08-13 20:01:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleTwoTopInput_right_memLp` | Proof completed | 2026-08-13 20:04:38 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorAtom_memLp_of_memLp_any_exponent` | Proof completed | 2026-08-13 20:04:38 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.enorm_integral_mul_le_eLpNorm_two_mul` | Proof completed | 2026-08-13 20:01:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.enorm_integral_mul_le_eLpNorm_top_one_mul` | Proof completed | 2026-08-13 20:01:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.memLp_of_aestronglyMeasurable_of_eLpNorm_le` | Proof completed | 2026-08-13 20:01:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleTwoTopPairing_left_enorm_bound` | Proof completed | 2026-08-13 20:01:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleTwoTopPairing_right_enorm_bound` | Proof completed | 2026-08-13 20:04:38 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_finiteAtomicCpow_ofReal_le_square_max` | Proof completed | 2026-08-13 20:12:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_bddAbove` | Proof completed | 2026-08-13 20:12:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleTwoTopPairing_midpoint_enorm_bound` | Proof completed | 2026-08-13 20:16:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.enorm_integral_mul_le_eLpNorm_four_fourThird_mul` | Proof completed | 2026-08-13 20:21:00 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.fourDualTest` | Proof completed | 2026-08-13 20:32:15 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.fourDualTest_memLp` | Proof completed | 2026-08-13 20:32:15 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_fourDualTest` | Proof completed | 2026-08-13 20:32:15 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.mul_fourDualTest` | Proof completed | 2026-08-13 20:32:15 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.integral_mul_fourDualTest` | Proof completed | 2026-08-13 20:32:15 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleTwoTopPairing_midpoint_integral_enorm_bound` | Proof completed | 2026-08-13 20:33:27 -04:00 |
| `foundation:simple-function-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_eLpNorm_reciprocal_smul_le_one` | Proof completed | 2026-08-13 20:39:56 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.affineExponent` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.recipBlend` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinInputExponent` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinTestExponent` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_affineExponent` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.affineExponent_re` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.affineExponent_re_zero` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.affineExponent_re_one` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_rieszThorinInputExponent` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.differentiable_rieszThorinTestExponent` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinInputExponent_re` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinTestExponent_re` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinInputExponent_re_zero` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinInputExponent_re_one` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinTestExponent_re_zero` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinTestExponent_re_one` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.affineExponent_at_real` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.affineExponent_at_real_eq_one` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.affineExponent_left_re` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.affineExponent_right_re` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinInputExponent_theta` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinTestExponent_theta` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finite_input_endpoint_identity` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finite_test_endpoint_identity` | Proof completed | 2026-08-13 20:43:53 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_finiteSimpleVectorPowerFamily_top_le_one_of_re_zero` | Proof completed | 2026-08-13 20:47:18 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPowerFamily_memLp_top_of_re_zero` | Proof completed | 2026-08-13 20:47:18 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_finiteSimpleVectorPowerFamily_affineExponent_left` | Proof completed | 2026-08-13 20:47:18 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_finiteSimpleVectorPowerFamily_affineExponent_right` | Proof completed | 2026-08-13 20:47:18 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.enorm_integral_mul_le_eLpNorm_mul_of_holderTriple` | Proof completed | 2026-08-13 20:47:18 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_endpoint_enorm_bound` | Proof completed | 2026-08-13 20:47:18 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_finiteAtomicCpow_ofReal_le_rpow_max` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_bddAbove_of_re_bounds` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.affineExponent_re_nonneg_on_verticalClosedStrip` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.affineExponent_re_le_max_on_verticalClosedStrip` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinInputExponent_left_re` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinInputExponent_right_re` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinTestExponent_left_re` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinTestExponent_right_re` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinInputExponent_re_nonneg_on_verticalClosedStrip` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinTestExponent_re_nonneg_on_verticalClosedStrip` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinInputExponent_re_le_max_on_verticalClosedStrip` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.rieszThorinTestExponent_re_le_max_on_verticalClosedStrip` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_rieszThorin_bddAbove` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_rieszThorin_threeLines` | Proof completed | 2026-08-13 20:53:26 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_finiteSimpleVectorPowerFamily_eq_rpow_of_moment_identity` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_finiteSimpleVectorPowerFamily_le_one_of_moment_identity` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.ennreal_finite_input_endpoint_identity` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.ennreal_finite_test_endpoint_identity` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.ennreal_mul_ofReal_mul_reciprocal_toReal` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.holderConjugate_reciprocal_toReal` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.ennreal_holderConjugate_test_moment` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_inputPower_le_one_of_finite_endpoint` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_inputPower_top_le_one_of_infinite_endpoint` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_inputPower_memLp_top_of_infinite_endpoint` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_testPower_memLp_of_nonone_endpoint` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_testPower_le_one_of_nonone_endpoint` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_testPower_top_of_one_endpoint` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_atomPair_integrable_of_endpoint_bound` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_endpoint_of_finiteSource_nononeTarget` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_endpoint_of_infiniteSource_nononeTarget` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_endpoint_of_finiteSource_oneTarget` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimpleVectorPairing_endpoint_of_infiniteSource_oneTarget` | Proof completed | 2026-08-13 21:12:17 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.ennrealHolderDual` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.ennreal_holderConjugate_ennrealHolderDual` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.pRawDualTest` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteAtomicPhase_norm_eq_one` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.aestronglyMeasurable_pRawDualTest` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.pRawDualTest_pair_pointwise` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_pRawDualTest` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.p_conjExponent_mul_sub_one` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.ofReal_p_div_sub_one` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.ofReal_pconj_mul_sub_one` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.memLp_pRawDualTest` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_pRawDualTest` | Proof completed | 2026-08-13 21:24:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.integral_pRawDualTest_pairing` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.lpNorm_p_pow_eq_integral_norm_rpow` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.integral_pRawDualTest_pairing_eq_lpNorm_pow` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.ofReal_holderConjugate` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.enorm_integral_mul_le_eLpNorm_p_pconj_mul` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_bound_of_dense_simple_tests` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.one_le_ofReal_conjExponent` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.norm_toLp_pRawDualTest` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.lpPairing_apply_toLp_eq_integral` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.lpNorm_le_of_simple_test_pairing_bound` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.lpNorm_le_of_raw_simpleFunc_test_pairing_bound` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.raw_simpleFunc_pairing_bound_of_unit_bound` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.lpNorm_le_of_raw_simpleFunc_unit_test_pairing_bound` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.eLpNorm_le_of_raw_simpleFunc_unit_test_pairing_enorm_bound` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `thm:riesz-thorin` supporting simple-function core | `Codex.Spherical.RieszThorin.finiteSimpleRieszThorin_diagonal_unit_pairing` | Proof completed | 2026-08-13 21:32:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.memLp_of_power_interpolation` | Proof completed | 2026-08-13 21:43:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.finiteSimple_memLp_of_memLp_any_exponent` | Proof completed | 2026-08-13 21:43:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.reciprocal_power_interpolation_identity` | Proof completed | 2026-08-13 21:43:00 -04:00 |
| `foundation:general-exponent-complex-interpolation` | `Codex.Spherical.RieszThorin.ennreal_weighted_geometricMean_eq_ofReal` | Proof completed | 2026-08-13 21:43:00 -04:00 |
| `thm:riesz-thorin` supporting simple-function core | `Codex.Spherical.RieszThorin.finiteSimpleRieszThorin_diagonal_eLpNorm` | Proof completed | 2026-08-13 21:49:31 -04:00 |
| `thm:riesz-thorin` supporting simple-function core | `Codex.Spherical.RieszThorin.finiteSimpleRieszThorin_diagonal_eLpNorm_homogeneous` | Proof completed | 2026-08-13 21:49:31 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.rawCore_memLp` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.rawCore_ae_compatible` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.rawSimpleCore` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.rawSimpleCore_apply_toLp` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.norm_rawSimpleCore_apply_le` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.rawCoreEmbedding` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.rawLpExtension` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.rawLpExtension_apply_toLp` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.norm_rawLpExtension_apply_le` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.opNorm_rawLpExtension_le` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion core | `Codex.Spherical.RieszThorin.exists_rawLpExtension_of_midpoint` | Proof completed | 2026-08-13 21:56:00 -04:00 |
| `thm:riesz-thorin` completion algebra | `Codex.Spherical.RieszThorin.real_midpoint_of_ennreal_reciprocal` | Proof completed | 2026-08-13 22:06:39 -04:00 |
| `thm:riesz-thorin` endpoint algebra | `Codex.Spherical.RieszThorin.min_le_weighted_geometricMean` | Proof completed | 2026-08-13 22:06:39 -04:00 |
| `thm:riesz-thorin` endpoint algebra | `Codex.Spherical.RieszThorin.norm_le_toReal_mul_of_eLpNorm_le` | Proof completed | 2026-08-13 22:06:39 -04:00 |
| `thm:riesz-thorin` degenerate endpoint | `Codex.Spherical.RieszThorin.rieszThorin_top_top` | Proof completed | 2026-08-13 22:06:39 -04:00 |
| `thm:riesz-thorin` degenerate endpoint | `Codex.Spherical.RieszThorin.rieszThorin_top_top_of_eLpNorm` | Proof completed | 2026-08-13 22:06:39 -04:00 |
| `thm:riesz-thorin` degenerate endpoint | `Codex.Spherical.RieszThorin.rieszThorin_one_one` | Proof completed | 2026-08-13 22:06:39 -04:00 |
| `thm:riesz-thorin` supporting membership | `Codex.Spherical.RieszThorin.memLp_of_norm_power_interpolation` | Proof completed | 2026-08-13 22:17:11 -04:00 |
| `thm:riesz-thorin` exponent algebra | `Codex.Spherical.RieszThorin.conjugate_test_moment_of_input_moment` | Proof completed | 2026-08-13 22:17:11 -04:00 |
| `thm:riesz-thorin` supporting simple-function core | `Codex.Spherical.RieszThorin.finiteSimpleRieszThorin_diagonal_unit_pairing_conjugate` | Proof completed | 2026-08-13 22:17:11 -04:00 |
| `thm:riesz-thorin` finite-simple normalization | `Codex.Spherical.RieszThorin.finiteSimpleVector_eLpNorm_reciprocal_smul_le_one` | Proof completed | 2026-08-13 22:17:11 -04:00 |

## `LeanSpherical/Codex/Spherical/LpSpaceFacts.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| File completion | `LeanSpherical/Codex/Spherical/LpSpaceFacts.lean` | Proof completed | 2026-08-13 22:17:11 -04:00 |
| Main reusable Lp fact | `Codex.Spherical.LpSpaceFacts.eLpNorm_power_interpolation_of_holder` | Proof completed | 2026-08-13 22:15:21 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.eLpNorm_four_rpow_two_le_two_mul_top` | Proof completed | 2026-08-13 22:15:21 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.eLpNorm_four_le_geometricMean_two_top` | Proof completed | 2026-08-13 22:15:21 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.memLp_four_of_two_and_top` | Proof completed | 2026-08-13 22:15:21 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.memLp_power_interpolation_of_holder` | Proof completed | 2026-08-13 22:15:21 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.eLpNorm_three_rpow_two_le_two_mul_six` | Proof completed | 2026-08-13 22:15:21 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.eLpNorm_three_le_geometricMean_two_six` | Proof completed | 2026-08-13 22:15:21 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.memLp_three_of_two_and_six` | Proof completed | 2026-08-13 22:15:21 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.eLpNorm_top_le_eLpNorm_two_count` | Proof completed | 2026-08-13 22:15:21 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.eLpNorm_real_nonneg_le_of_lintegral_ofReal_rpow_le` | Proof completed | 2026-08-13 22:17:11 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.lintegral_ofReal_norm_rpow_eq_eLpNorm_rpow` | Proof completed | 2026-08-13 22:17:11 -04:00 |
| Reusable Lp-space fact | `Codex.Spherical.LpSpaceFacts.lintegral_ofReal_rpow_eq_eLpNorm_rpow_of_nonneg` | Proof completed | 2026-08-13 22:17:11 -04:00 |

## `LeanSpherical/Codex/Spherical/MSSPhaseCalculus.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Reusable radial phase derivative | `Codex.Spherical.MSSPhaseCalculus.fderiv_radial_phase_apply` | Proof completed | 2026-08-14 04:37:17 -04:00 |
| Planar radial phase Laplacian | `Codex.Spherical.MSSPhaseCalculus.laplacian_radial_phase_eq` | Proof completed | 2026-08-14 04:37:17 -04:00 |
| Local planar Laplacian product rule | `Codex.Spherical.MSSPhaseCalculus.laplacian_mul_at` | Proof completed | 2026-08-14 04:37:17 -04:00 |

## `LeanSpherical/Codex/Spherical/SmoothDyadicPhysicalCore.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.fourierCubeKernel` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.fourierCubeSourceKernel` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.fourierCubeProjection_eq_sourceKernel` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.fourierCubeProjectedSchwartz` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.fourierCubeProjectedSchwartz_apply` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.fourier_fourierCubeProjectedSchwartz_apply` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.integrable_fourierCubeSourceKernel` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.integral_norm_fourierCubeSourceKernel_eq` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.norm_pow_mul_norm_fourierCubeKernel_le_seminorm` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.finiteFourierCubeKernelMass` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.finiteFourierCubeKernelMass_nonneg` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| Dimension-generic Fourier-cube physical kernel | `Codex.Spherical.SmoothDyadicPhysicalCore.integral_norm_fourierCubeSourceKernel_le_finiteMass` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| Dimension-generic compact modulation | `Codex.Spherical.SmoothDyadicPhysicalCore.planeWaveModulatedCompactSchwartz` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Dimension-generic compact modulation | `Codex.Spherical.SmoothDyadicPhysicalCore.planeWaveModulatedCompactSchwartz_apply` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Dimension-generic compact modulation | `Codex.Spherical.SmoothDyadicPhysicalCore.fourierInv_planeWaveModulatedCompactSchwartz_eq_translate` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Dimension-generic Fourier-kernel decay | `Codex.Spherical.SmoothDyadicPhysicalCore.norm_fourierCubeKernel_le_scaled_seminorm_decay` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Dimension-generic translated/dilated cutoff | `Codex.Spherical.SmoothDyadicPhysicalCore.translatedDilatedSchwartzCutoff` | Proof completed | 2026-08-14 06:19:01 -04:00 |
| Dimension-generic translated/dilated cutoff | `Codex.Spherical.SmoothDyadicPhysicalCore.iteratedFDeriv_translatedDilatedSchwartzCutoff` | Proof completed | 2026-08-14 06:19:01 -04:00 |
| Dimension-generic translated/dilated cutoff | `Codex.Spherical.SmoothDyadicPhysicalCore.integral_norm_iteratedFDeriv_translatedDilatedSchwartzCutoff` | Proof completed | 2026-08-14 06:19:01 -04:00 |

## `LeanSpherical/Codex/Spherical/MSS.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| `def:intro-half-wave` | `Codex.Spherical.MSS.WaveSign.toReal` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.halfWaveMultiplier` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| Half-wave temporal derivative | `Codex.Spherical.MSS.halfWaveMultiplierTimeDerivative` | Proof completed | 2026-08-14 08:38:45 -04:00 |
| Half-wave temporal derivative | `Codex.Spherical.MSS.hasDerivAt_halfWaveMultiplier_time` | Proof completed | 2026-08-14 08:38:45 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.halfWave` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.norm_halfWaveMultiplier` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.halfWaveMultiplier_zero` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.halfWaveMultiplier_add` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.halfWaveMultiplier_contDiffAt_of_ne_zero` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.halfWave_apply` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.dyadicHalfWave` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.dyadicHalfWave_zero` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.dyadicHalfWaveSymbol` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.dyadicHalfWaveSchwartzSymbol_apply` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-half-wave` | `Codex.Spherical.MSS.norm_dyadicHalfWaveSchwartzSymbol_le_two` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.integral_norm_sq_dyadicProjection_le_four` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.integral_norm_sq_dyadicHalfWave_zero_le_four` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.fixedTimeL2Endpoint` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.l2Endpoint` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.localSmoothingMeasure` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.dyadicHalfWaveSpaceTime` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.continuous_dyadicHalfWaveSpaceTime` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.aestronglyMeasurable_dyadicHalfWaveSpaceTime` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.integrable_norm_sq_dyadicHalfWaveSpaceTime` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.integral_norm_sq_dyadicHalfWaveSpaceTime_le_four` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.localL2Endpoint` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-l2-endpoint` | `Codex.Spherical.MSS.localL2Endpoint_proof` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.dyadicBandpassMultiplier_eq_levelZero_scaled` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.halfWaveMultiplier_eq_levelZero_scaled` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.dyadicHalfWaveSymbol_eq_levelZero_scaled` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.dyadicHalfWaveKernel` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.dyadicHalfWaveKernel_eq_levelZero_scaled` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.integral_norm_dyadicHalfWaveKernel_eq_levelZero_scaled` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.dyadicHalfWaveKernelL1` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.dyadicHalfWaveKernelL1_eq_levelZero_scaled` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.dyadicHalfWave_eq_convolution` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.waveKernelL1` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| Fourier cone-weight bridge | `Codex.Spherical.MSS.fourierInv_cancelled_laplacian_eq_cone_quadratic` | Proof completed | 2026-08-14 03:38:20 -04:00 |
| Fourier cone-weight bridge | `Codex.Spherical.MSS.cancelledWaveLaplacian` | Proof completed | 2026-08-14 03:48:08 -04:00 |
| Fourier cone-weight bridge | `Codex.Spherical.MSS.integrable_coneWeightedEnergy_fourierInv` | Proof completed | 2026-08-14 03:48:08 -04:00 |
| Fourier cone-weight bridge | `Codex.Spherical.MSS.integral_coneWeightedEnergy_fourierInv_le` | Proof completed | 2026-08-14 03:48:08 -04:00 |
| Fourier cone-weight bridge | `Codex.Spherical.MSS.integral_norm_sq_le_of_support_subset` | Proof completed | 2026-08-14 03:58:25 -04:00 |
| Fourier cone-weight bridge | `Codex.Spherical.MSS.integral_norm_sq_le_scaled_of_norm_le_of_support_subset` | Proof completed | 2026-08-14 03:58:25 -04:00 |
| Fourier cone-weight bridge | `Codex.Spherical.MSS.integral_norm_sq_levelZero_dyadicHalfWaveSchwartzSymbol_le` | Proof completed | 2026-08-14 03:58:25 -04:00 |
| Fourier cone-weight bridge | `Codex.Spherical.MSS.hasUniformConeWeightedKernelEnergy_of_frequencyBounds` | Proof completed | 2026-08-14 03:50:59 -04:00 |
| Fourier cone-weight bridge | `Codex.Spherical.MSS.hasUniformConeWeightedKernelEnergy_of_cancelledEnergyBound` | Proof completed | 2026-08-14 03:59:50 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.coneWeight` | Proof completed | 2026-08-14 03:27:16 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.coneReciprocal` | Proof completed | 2026-08-14 03:27:16 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.coneWeight_pos` | Proof completed | 2026-08-14 03:27:16 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.integral_radius_coneReciprocal` | Proof completed | 2026-08-14 03:27:16 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.integrable_coneReciprocal` | Proof completed | 2026-08-14 03:27:16 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.integral_coneReciprocal_le` | Proof completed | 2026-08-14 03:27:16 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.integral_norm_le_coneWeightedEnergy` | Proof completed | 2026-08-14 03:27:16 -04:00 |
| Fourier cone-weight bridge | `Codex.Spherical.MSS.fourierInv_cancelled_laplacian_eq_cone_quadratic` | Proof completed | 2026-08-14 03:38:20 -04:00 |
| Planar cancelled phase energy | `Codex.Spherical.MSS.exists_cancelled_levelZero_dyadicHalfWave_energy_bound` | Proof completed | 2026-08-14 04:37:17 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.HasUniformConeWeightedKernelEnergy` | Proof completed | 2026-08-14 04:37:17 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.hasUniformConeWeightedKernelEnergy` | Proof completed | 2026-08-14 04:37:17 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.levelZeroKernelL1_le_of_coneWeightedEnergy` | Proof completed | 2026-08-14 03:34:19 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.waveKernelL1_sharp_of_uniformConeWeightedEnergy` | Proof completed | 2026-08-14 03:34:19 -04:00 |
| `lem:wave-kernel-l1` | `Codex.Spherical.MSS.waveKernelL1_sharp` | Proof completed | 2026-08-14 04:37:17 -04:00 |
| `prop:mss-linfty-endpoint` | `Codex.Spherical.MSS.norm_dyadicHalfWave_le_kernelL1` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-linfty-endpoint` | `Codex.Spherical.MSS.fixedTimePhysicalLInfinityEndpoint` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-linfty-endpoint` | `Codex.Spherical.MSS.fixedTimePhysicalLInfinityEndpoint_scaled` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-linfty-endpoint` | `Codex.Spherical.MSS.fixedTimePhysicalLInfinityEndpoint_of_kernelL1_le` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-linfty-endpoint` | `Codex.Spherical.MSS.fixedTimeFourierL1Endpoint` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-linfty-endpoint` | `Codex.Spherical.MSS.lInfinityEndpoint` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `prop:mss-linfty-endpoint` | `Codex.Spherical.MSS.mssLInfinityEndpoint_of_waveKernelL1_sharp` | Proof completed | 2026-08-14 03:34:19 -04:00 |
| `prop:mss-linfty-endpoint` | `Codex.Spherical.MSS.mssLInfinityEndpoint_of_uniformConeWeightedEnergy` | Proof completed | 2026-08-14 03:34:19 -04:00 |
| `prop:mss-linfty-endpoint` | `Codex.Spherical.MSS.mssLInfinityEndpoint` | Proof completed | 2026-08-14 04:37:17 -04:00 |
| `def:intro-mss-gain` | `Codex.Spherical.MSS.mssGain` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-mss-gain` | `Codex.Spherical.MSS.mssGain_of_le_four` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-mss-gain` | `Codex.Spherical.MSS.mssGain_of_four_lt` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-mss-gain` | `Codex.Spherical.MSS.mssGain_four` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-mss-gain` | `Codex.Spherical.MSS.mssGain_pos` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:intro-mss-local-smoothing`; `thm:mss-local-smoothing` | `Codex.Spherical.MSS.localSmoothing` | Statement completed | 2026-08-13 13:24:00 -04:00 |
| `thm:intro-mss-local-smoothing` | `Codex.Spherical.MSS.localSmoothing_to_hasPositiveLocalSmoothingGain` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `p = 4` MSS-to-Bourgain gain bridge | `Codex.Spherical.MSS.p4LocalSmoothing_to_hasPositiveLocalSmoothingGain` | Proof completed | 2026-08-14 05:07:14 -04:00 |
| `thm:mss-p4` | `Codex.Spherical.MSS.p4LocalSmoothing` | Statement completed | 2026-08-13 16:18:27 -04:00 |
| Literal source/output `L²`--`L⁴` interpolation | `Codex.Spherical.MSS.mss_two_four_coefficient` | Proof completed | 2026-08-14 08:16:44 -04:00 |
| Literal source/output `L⁴`--slab-local-`L∞` interpolation | `Codex.Spherical.MSS.mss_four_top_coefficient` | Proof completed | 2026-08-14 08:16:44 -04:00 |
| `p = 4` MSS interpolation below four | `Codex.Spherical.MSS.p4LocalSmoothing_to_localSmoothing_two_four` | Proof completed | 2026-08-14 08:16:44 -04:00 |
| `p = 4` MSS interpolation above four | `Codex.Spherical.MSS.p4LocalSmoothing_to_localSmoothing_four_top` | Proof completed | 2026-08-14 08:16:44 -04:00 |
| `thm:mss-local-smoothing` all-exponent interpolation | `Codex.Spherical.MSS.p4LocalSmoothing_to_localSmoothing_all_p` | Proof completed | 2026-08-14 08:16:44 -04:00 |
| `def:intro-time-discretization` | `Codex.Spherical.MSS.dyadicTimeScale` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:intro-time-discretization` | `Codex.Spherical.MSS.MaximalSeparated` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:intro-discrete-local-smoothing`; `cor:mss-discrete` | `Codex.Spherical.MSS.discreteLocalSmoothing` | Statement completed | 2026-08-13 13:24:00 -04:00 |
| `def:spacetime-fourier` | `Codex.Spherical.MSS.WaveSpaceTime` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `def:spacetime-fourier` | `Codex.Spherical.MSS.spaceTimeFourier` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `def:spacetime-fourier` | `Codex.Spherical.MSS.spaceTimeFourierInv` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `def:mss-radial-vertical` | `Codex.Spherical.MSS.verticalMultiplier` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `def:mss-radial-vertical` | `Codex.Spherical.MSS.verticalProjection` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| Literal temporal factor of a vertical projection | `Codex.Spherical.MSS.verticalTemporalProjection` | Statement completed | 2026-08-14 08:32:26 -04:00 |
| Literal separable vertical packet | `Codex.Spherical.MSS.verticalSeparablePacket` | Statement completed | 2026-08-14 08:32:26 -04:00 |
| Iterated Fourier factorization of a separable vertical packet | `Codex.Spherical.MSS.spaceTimeFourier_verticalSeparablePacket` | Proof completed | 2026-08-14 08:32:26 -04:00 |
| Fourier-support product bound for a literal separable vertical packet | `Codex.Spherical.MSS.support_spaceTimeFourier_verticalSeparablePacket_subset_prod` | Proof completed | 2026-08-19 22:15:10 -04:00 |
| Fourier-support containment transfer for a literal separable vertical packet | `Codex.Spherical.MSS.support_spaceTimeFourier_verticalSeparablePacket_subset` | Proof completed | 2026-08-19 22:15:10 -04:00 |
| Literal vertical projection on a separable packet | `Codex.Spherical.MSS.verticalProjection_verticalSeparablePacket` | Proof completed | 2026-08-14 08:32:26 -04:00 |
| Exact space--time Fourier multiplier identity for a separable Schwartz vertical packet | `Codex.Spherical.MSS.spaceTimeFourier_verticalProjection_verticalSeparablePacket_of_schwartzProfile` | Proof completed | 2026-08-19 22:23:04 -04:00 |
| `def:mss-radial-vertical` | `Codex.Spherical.MSS.radialPiece` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| Finite Schwartz multiplier partition synthesis | `Codex.Spherical.MSS.sum_fourierCubeProjection_eq_fourierInv_multiplier_of_sum_eq` | Proof completed | 2026-08-14 07:18:56 -04:00 |
| Finite radial/conic cube synthesis under supplied Schwartz partition data | `Codex.Spherical.MSS.sum_fourierCubeProjection_eq_radialPiece_of_sum_eq`; `Codex.Spherical.MSS.conicOperator_sum_fourierCubeProjection_eq_radialPiece_of_sum_eq` | Proof completed | 2026-08-14 07:18:56 -04:00 |
| `def:conic-operator` | `Codex.Spherical.MSS.conicOperator` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| Conic/dyadic scale normal form (positive) | `Codex.Spherical.MSS.conicOperator_eq_dyadicHalfWaveSpaceTime_plus` | Proof completed | 2026-08-14 05:02:59 -04:00 |
| Conic/dyadic local `L⁴` transfer (positive) | `Codex.Spherical.MSS.eLpNorm_dyadicHalfWaveSpaceTime_plus_le_conicOperator` | Proof completed | 2026-08-14 05:02:59 -04:00 |
| Conic/dyadic scale normal form (reflected negative) | `Codex.Spherical.MSS.conicOperator_timeReflect_eq_dyadicHalfWaveSpaceTime_minus` | Proof completed | 2026-08-14 05:02:59 -04:00 |
| Conic/dyadic local `L⁴` transfer (negative) | `Codex.Spherical.MSS.eLpNorm_dyadicHalfWaveSpaceTime_minus_le_conicOperator` | Proof completed | 2026-08-14 05:02:59 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.relevantRadialIndices` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.mem_relevantRadialIndices_iff` | Proof completed | 2026-08-13 14:00:00 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.mem_relevantRadialIndices_of_mem_annulus_of_abs_sub_lt` | Proof completed | 2026-08-13 14:19:17 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.HasRelevantRadialEnumeration` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.relevantRadialIndexBounds` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.relevantRadialIndexEnumeration` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.mem_relevantRadialIndexBounds_of_mem_relevantRadialIndices` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.mem_relevantRadialIndexEnumeration_iff` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.hasRelevantRadialEnumeration_relevantRadialIndexEnumeration` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.relevantRadialIndexEnumeration_subset_bounds` | Proof completed | 2026-08-13 14:16:11 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.card_relevantRadialIndexBounds` | Proof completed | 2026-08-13 14:16:11 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.card_relevantRadialIndexEnumeration_le` | Proof completed | 2026-08-13 14:16:11 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.card_relevantRadialIndexEnumeration_le_two_mul_natCeil_sqrt_add_seven` | Proof completed | 2026-08-13 14:16:11 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.card_relevantRadialIndexEnumeration_le_eleven_mul_sqrt` | Proof completed | 2026-08-13 14:16:11 -04:00 |
| `lem:mss-relevant-indices` | `Codex.Spherical.MSS.relevantRadialIndexEnumeration_eq_of_hasRelevantRadialEnumeration` | Proof completed | 2026-08-13 14:16:11 -04:00 |
| `prop:mss-radial-time-localization` | `Codex.Spherical.MSS.radialTimeReconstruction` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `prop:mss-radial-time-localization` | `Codex.Spherical.MSS.radialTimeResidual` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `prop:mss-radial-time-localization` | `Codex.Spherical.MSS.radialTimeLocalization` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| Radial reconstruction/vertical recombination identity | `Codex.Spherical.MSS.radialTimeReconstruction_eq_verticalRecombined` | Proof completed | 2026-08-14 07:07:09 -04:00 |
| `prop:mss-radial-time-localization` | `Codex.Spherical.MSS.radialTimeReconstruction_eq_of_hasRelevantRadialEnumeration` | Proof completed | 2026-08-13 14:16:11 -04:00 |
| `prop:mss-radial-time-localization` | `Codex.Spherical.MSS.radialTimeResidual_eq_of_hasRelevantRadialEnumeration` | Proof completed | 2026-08-13 14:16:11 -04:00 |
| `prop:mss-radial-time-localization` | `Codex.Spherical.MSS.radialTimeLocalization_iff_estimate_relevantRadialIndexEnumeration` | Proof completed | 2026-08-13 14:16:11 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.verticalSquareFunction` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.verticalSquareFunction_nonneg` | Proof completed | 2026-08-13 14:19:17 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.norm_le_verticalSquareFunction` | Proof completed | 2026-08-13 14:19:17 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.norm_finset_sum_le_card_nsmul_verticalSquareFunction` | Proof completed | 2026-08-13 14:19:17 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.verticalRecombined` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| Literal finite recombination of separable vertical packets | `Codex.Spherical.MSS.verticalRecombined_verticalSeparablePackets` | Proof completed | 2026-08-14 08:32:26 -04:00 |
| Common-spatial-factor finite recombination Fourier multiplier identity | `Codex.Spherical.MSS.spaceTimeFourier_verticalRecombined_verticalSeparablePackets_of_schwartzProfiles_common_spatial` | Proof completed | 2026-08-19 22:30:20 -04:00 |
| Finite mixed-tensor recombination Fourier multiplier identity | `Codex.Spherical.MSS.spaceTimeFourier_verticalRecombined_verticalSeparablePackets_of_schwartzProfiles` | Proof completed | 2026-08-19 22:37:06 -04:00 |
| Finite Schwartz-profile temporal `L²` vertical recombination | `Codex.Spherical.MSS.integral_norm_sq_sum_verticalTemporalProjection_le_of_schwartz_profiles` | Proof completed | 2026-08-14 08:52:46 -04:00 |
| Finite mixed-tensor space--time `L²` vertical recombination | `Codex.Spherical.MSS.integral_norm_sq_verticalRecombined_verticalSeparablePackets_le_of_schwartz_profiles` | Proof completed | 2026-08-19 22:59:54 -04:00 |
| Finite mixed-tensor input-energy `L²` vertical recombination | `Codex.Spherical.MSS.integral_norm_sq_verticalRecombined_verticalSeparablePackets_le_sum_inputEnergy_of_schwartz_profiles` | Proof completed | 2026-08-19 22:59:54 -04:00 |
| Finite separable-packet temporal-square endpoint | `Codex.Spherical.MSS.norm_verticalRecombined_verticalSeparablePackets_le_of_temporal_square_bound` | Proof completed | 2026-08-19 23:11:12 -04:00 |
| Finite Schwartz-profile common-time-kernel endpoint | `Codex.Spherical.MSS.norm_verticalRecombined_verticalSeparablePackets_le_of_schwartz_profiles_of_common_time_kernel` | Proof completed | 2026-08-19 23:11:12 -04:00 |
| Finite Schwartz-profile pointwise `L∞` common-kernel endpoint | `Codex.Spherical.MSS.norm_verticalRecombined_verticalSeparablePackets_le_of_schwartz_profiles_of_common_time_kernel_and_spatial_envelope` | Proof completed | 2026-08-19 23:11:12 -04:00 |
| Finite mixed-tensor `L²`--`L⁴`--`L∞` vertical interpolation | `Codex.Spherical.MSS.eLpNorm_four_rpow_two_verticalRecombined_verticalSeparablePackets_le_of_schwartz_profiles_of_common_time_kernel_and_spatial_envelope` | Proof completed | 2026-08-19 23:26:14 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.verticalRecombinationGain` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.verticalRecombination` | Statement completed | 2026-08-13 14:00:00 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.finiteVerticalRecombinedOnCounting` | Proof completed | 2026-08-13 15:47:13 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.eLpNorm_four_rpow_two_finiteVerticalRecombinedOnCounting_le_of_two_top` | Proof completed | 2026-08-13 15:47:13 -04:00 |
| Finite-packet-to-continuum `L⁴` closedness | `Codex.Spherical.MSS.eLpNorm_verticalRecombined_le_of_tendsto_eLpNorm` | Proof completed | 2026-08-14 07:03:58 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.eLpNorm_verticalRecombined_le_sum` | Proof completed | 2026-08-13 14:19:17 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.eLpNorm_verticalRecombined_le_card_nsmul_of_bound` | Proof completed | 2026-08-13 14:19:17 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.eLpNorm_verticalRecombined_relevantRadialIndexEnumeration_le_of_bound` | Proof completed | 2026-08-13 14:20:39 -04:00 |
| `thm:mss-vertical-recombination` | `Codex.Spherical.MSS.norm_verticalRecombined_le_card_nsmul_of_pointwise_bound` | Proof completed | 2026-08-13 14:22:45 -04:00 |
| `def:mss-angular-pieces` | `Codex.Spherical.MSS.angularPiece` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-angular-pieces` | `Codex.Spherical.MSS.angularSector` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-wavefront-plates` | `Codex.Spherical.MSS.wavefrontMultiplier` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-wavefront-plates` | `Codex.Spherical.MSS.wavefrontProjection` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-wavefront-plates` | `Codex.Spherical.MSS.conicPlate` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| Spectral conic-packet bridge | `Codex.Spherical.MSS.spectralRadialNormalPacket` | Statement completed | 2026-08-20 00:45:10 -04:00 |
| Spectral conic-packet bridge | `Codex.Spherical.MSS.spaceTimeFourier_spectralRadialNormalPacket_of_schwartzProfile` | Proof completed | 2026-08-20 00:45:10 -04:00 |
| Spectral conic-packet bridge | `Codex.Spherical.MSS.support_spaceTimeFourier_spectralRadialNormalPacket_subset_conicPlate` | Proof completed | 2026-08-20 00:45:10 -04:00 |
| Spectral conic-packet bridge | `Codex.Spherical.MSS.spectralCubeRadialNormalPacket` | Statement completed | 2026-08-20 00:45:10 -04:00 |
| Spectral conic-packet bridge | `Codex.Spherical.MSS.spaceTimeFourier_spectralCubeRadialNormalPacket_of_schwartzProfile` | Proof completed | 2026-08-20 00:45:10 -04:00 |
| Spectral conic-packet bridge | `Codex.Spherical.MSS.support_spaceTimeFourier_spectralCubeRadialNormalPacket_subset_conicPlate` | Proof completed | 2026-08-20 00:45:10 -04:00 |
| Spectral conic-packet bridge | `Codex.Spherical.MSS.spectralCubeRadialNormalPackets_satisfy_conicPlateSupport` | Proof completed | 2026-08-20 00:45:10 -04:00 |
| Spectral conic-packet bridge | `Codex.Spherical.MSS.support_spaceTimeFourier_spectralCubeRadialNormalPacket_subset_conicPlate_of_cube` | Proof completed | 2026-08-20 00:45:10 -04:00 |
| Spectral packet overlap consumer | `Codex.Spherical.MSS.overlapSquareFunction_spectralCubeRadialNormalPackets` | Proof completed | 2026-08-20 00:56:09 -04:00 |
| Spectral packet finite overlap energy | `Codex.Spherical.MSS.exists_finitePlateOverlapSquareEnergy_spectralCubeRadialNormalPackets_le_scaled` | Proof completed | 2026-08-20 00:56:09 -04:00 |
| `def:mss-wavefront-plates` | `Codex.Spherical.MSS.angularRadialSquareFunction` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-wavefront-plates` | `Codex.Spherical.MSS.angularRadialWave` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-wavefront-plates` | `Codex.Spherical.MSS.wavefrontAngularRadialWave` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `lem:mss-wavefront-localization` | `Codex.Spherical.MSS.wavefrontLocalization` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `lem:mss-wavefront-localization` | `Codex.Spherical.MSS.wavefrontPlateSupport` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-angular-separation` | `Codex.Spherical.MSS.angularSeparationClass` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-angular-separation` | `Codex.Spherical.MSS.angularSeparationPairs` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-angular-separation` | `Codex.Spherical.MSS.mem_angularSeparationPairs_iff` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-angular-separation` | `Codex.Spherical.MSS.angularSeparationClass_zero_iff` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-angular-separation` | `Codex.Spherical.MSS.angularSeparationClass_succ_iff` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-angular-separation` | `Codex.Spherical.MSS.angularSeparationClass_comm` | Proof completed | 2026-08-13 14:27:35 -04:00 |
| `def:mss-angular-separation` | `Codex.Spherical.MSS.mem_swap_angularSeparationPairs_iff` | Proof completed | 2026-08-13 14:27:35 -04:00 |
| `def:mss-angular-separation` | `Codex.Spherical.MSS.angularSeparationPairs_subset_product` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `def:mss-angular-separation` | `Codex.Spherical.MSS.card_angularSeparationPairs_le` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.sq_sum_norm_angularSeparationPairs_le_card_mul_sum_sq` | Proof completed | 2026-08-13 14:25:17 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.sq_sum_norm_angularSeparationPairs_le_card_sq_mul_sum_sq` | Proof completed | 2026-08-13 14:25:17 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.minkowskiSum` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.mem_minkowskiSum_iff` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.minkowskiSum_comm` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessConicPoint` | Statement completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessConicPlate` | Statement completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlatePairSum` | Statement completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessConicPoint_mem_conicPlate` | Proof completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.mem_minkowskiSum_zeroThicknessConicPlates_iff` | Proof completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlateOverlapPairs` | Statement completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlateOverlapMultiplicity` | Statement completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.angularSectorGeometry_direction_injective` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.finset_card_le_two_of_forall_mem_eq_or_eq` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.norm_smul_unit_direction_of_nonneg` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.dist_zero_zeroThicknessPlatePairSum_first` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.dist_zeroThicknessPlatePairSum_first_spatial` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlatePairSum_spatial_ne_zero_of_angularSectorGeometry` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlatePairSum_eq_right_of_fst_eq` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlatePairSum_right_injective_of_angularSectorGeometry` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlateOverlapFirstSpatialPoints` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlateOverlapPairs_firstSpatial_injective_of_angularSectorGeometry` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.mem_zeroThicknessPlateOverlapFirstSpatialPoints_two_spheres` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlateOverlapMultiplicity_le_two_of_angularSectorGeometry_of_spatial_ne_zero` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlateOverlapMultiplicity_le_two_of_angularSectorGeometry` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlateOverlapMultiplicity_le_card_of_angularSectorGeometry` | Proof completed | 2026-08-13 15:25:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPairSumAtMostTwo` | Statement completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlateOverlapMultiplicity_le_two_of_pairSumAtMostTwo` | Proof completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.zeroThicknessPlatePairSum_swap` | Proof completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.two_le_zeroThicknessPlateOverlapMultiplicity_of_offDiagonalPair` | Proof completed | 2026-08-13 14:52:24 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlapPairs` | Statement completed | 2026-08-13 14:31:39 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.mem_plateOverlapPairs_iff` | Proof completed | 2026-08-13 14:35:56 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlapPairs_subset_angularSeparationPairs` | Proof completed | 2026-08-13 14:35:56 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlapMultiplicity` | Statement completed | 2026-08-13 14:08:12 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlapMultiplicity_eq_card_plateOverlapPairs` | Proof completed | 2026-08-13 14:31:39 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.unitNormalConicPlate` | Proof completed | 2026-08-14 05:26:27 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.normalCoordinatePlateCover_normalCoverShifts` | Proof completed | 2026-08-14 05:26:27 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.card_normalCoverShifts_at_scale_le_six_mul` | Proof completed | 2026-08-14 05:26:27 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlapMultiplicity_le_normalCover_mul_unitBound` | Proof completed | 2026-08-14 05:26:27 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.translatedUnitNormalPlateOverlap` | Proof completed | 2026-08-19 21:33:17 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.translatedUnitNormalPlateOverlap_of_angularSectorGeometry` | Proof completed | 2026-08-19 21:33:17 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlap_of_translatedUnitNormalPlateOverlap` | Proof completed | 2026-08-14 05:26:27 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlap_of_angularSectorGeometry` | Proof completed | 2026-08-19 21:33:17 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.sq_sum_norm_plateOverlapPairs_le_plateOverlapMultiplicity_mul_sum_sq` | Proof completed | 2026-08-13 14:31:39 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.sq_sum_norm_mul_plateOverlapPairs_le_plateOverlapMultiplicity_mul_sum_sq` | Proof completed | 2026-08-13 14:31:39 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.finitePlateOverlapSquareEnergy` | Proof completed | 2026-08-19 21:43:17 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.exists_sq_sum_norm_mul_plateOverlapPairs_le_scaled_of_plateOverlap` | Proof completed | 2026-08-19 21:43:17 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.exists_finitePlateOverlapSquareEnergy_le_scaled_of_plateOverlap` | Proof completed | 2026-08-19 21:43:17 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.exists_finitePlateOverlapSquareEnergy_le_scaled_of_angularSectorGeometry` | Proof completed | 2026-08-19 21:43:17 -04:00 |
| Finite cube-to-plate-pair realization | `Codex.Spherical.MSS.plateOverlapCubeOutputFiber` | Proof completed | 2026-08-19 21:49:36 -04:00 |
| Finite cube-to-plate-pair realization | `Codex.Spherical.MSS.mem_plateOverlapCubeOutputFiber_iff` | Proof completed | 2026-08-19 21:49:36 -04:00 |
| Finite cube-to-plate-pair realization | `Codex.Spherical.MSS.card_plateOverlapCubeOutputFiber_le_plateOverlapMultiplicity_of_pairRealization` | Proof completed | 2026-08-19 21:49:36 -04:00 |
| Finite cube-to-plate-pair realization | `Codex.Spherical.MSS.exists_card_plateOverlapCubeOutputFiber_le_scaled_of_plateOverlap` | Proof completed | 2026-08-19 21:49:36 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlapMultiplicity_le_card_angularSeparationPairs` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlapMultiplicity_le_card_sq` | Proof completed | 2026-08-13 14:08:12 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.sq_sum_norm_mul_plateOverlapPairs_le_card_sq_mul_sum_sq` | Proof completed | 2026-08-13 14:33:59 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.angularSectorGeometry` | Statement completed | 2026-08-13 14:42:30 -04:00 |
| `thm:mss-plate-overlap` | `Codex.Spherical.MSS.plateOverlap` | Statement completed | 2026-08-13 14:42:30 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.overlapSquareFunction` | Statement completed | 2026-08-13 16:18:27 -04:00 |
| `lem:mss-remove-vertical` | `Codex.Spherical.MSS.removeVerticalProjections` | Statement completed | 2026-08-13 16:18:27 -04:00 |
| `def:fourier-cubes` | `Codex.Spherical.MSS.frequencyCube` | Proof completed | 2026-08-13 15:01:28 -04:00 |
| `def:fourier-cubes` | `Codex.Spherical.MSS.mem_frequencyCube_iff` | Proof completed | 2026-08-13 15:01:28 -04:00 |
| `def:fourier-cubes` | `Codex.Spherical.MSS.isFourierCubeCutoff` | Proof completed | 2026-08-13 15:01:28 -04:00 |
| `def:fourier-cubes` | `Codex.Spherical.MSS.fourierCubeProjection` | Proof completed | 2026-08-13 15:01:28 -04:00 |
| `def:fourier-cubes` | `Codex.Spherical.MSS.fourierCubeProjection_apply` | Proof completed | 2026-08-13 15:01:28 -04:00 |
| `def:fourier-cube-physical` | `Codex.Spherical.MSS.fourierCubePhysicalKernel` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| `thm:fourier-cube-physical` | `Codex.Spherical.MSS.fourierCubeProjection_eq_physicalKernel` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| `thm:fourier-cube-physical` | `Codex.Spherical.MSS.integrable_fourierCubePhysicalKernel` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| `thm:fourier-cube-physical` | `Codex.Spherical.MSS.integral_norm_fourierCubePhysicalKernel_eq` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| `thm:fourier-cube-physical` | `Codex.Spherical.MSS.exists_uniform_fourierCubePhysicalKernelMass` | Proof completed | 2026-08-14 04:52:16 -04:00 |
| Literal angular half-wave/cube model | `Codex.Spherical.MSS.angularDyadicCubeSchwartzSymbol` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Literal angular half-wave/cube model | `Codex.Spherical.MSS.angularDyadicCubeSchwartzSymbol_apply` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Literal angular half-wave/cube model | `Codex.Spherical.MSS.angularDyadicCubeKernel` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Literal angular half-wave/cube model | `Codex.Spherical.MSS.angularDyadicCubeSpaceTimeKernel` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Literal angular half-wave/cube model | `Codex.Spherical.MSS.angularDyadicCubePiece` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Literal angular half-wave/cube model | `Codex.Spherical.MSS.angularDyadicCubePiece_eq_sourceKernel` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Literal angular half-wave/cube model | `Codex.Spherical.MSS.angularDyadicCubeSpaceTimeKernel_integrable` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Literal angular half-wave/cube model | `Codex.Spherical.MSS.integral_norm_angularDyadicCubeSpaceTimeKernel_eq` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Literal angular half-wave/cube model | `Codex.Spherical.MSS.angularPiece_dyadicCube_eq_spaceTimeKernel` | Proof completed | 2026-08-14 05:08:23 -04:00 |
| Literal finite angular packet/cube model | `Codex.Spherical.MSS.angularDyadicCubeKernelSum` | Proof completed | 2026-08-14 05:36:45 -04:00 |
| Literal finite angular packet/cube model | `Codex.Spherical.MSS.angularDyadicCubeKernelSum_eq_sum` | Proof completed | 2026-08-14 05:36:45 -04:00 |
| Literal finite angular packet/cube model | `Codex.Spherical.MSS.angularDyadicCubeSpaceTimeKernelSum` | Proof completed | 2026-08-14 05:36:45 -04:00 |
| Literal finite angular packet/cube model | `Codex.Spherical.MSS.angularDyadicCubeSpaceTimeKernelSum_eq_sum` | Proof completed | 2026-08-14 05:36:45 -04:00 |
| Literal finite angular packet/cube model | `Codex.Spherical.MSS.integrable_angularDyadicCubeSpaceTimeKernel_mul` | Proof completed | 2026-08-14 05:36:45 -04:00 |
| Literal finite angular packet/cube model | `Codex.Spherical.MSS.angularDyadicCubePacket` | Proof completed | 2026-08-14 05:36:45 -04:00 |
| Literal finite angular packet/cube model | `Codex.Spherical.MSS.angularDyadicCubePacket_eq_sum` | Proof completed | 2026-08-14 05:36:45 -04:00 |
| Literal angular half-wave/cube support | `Codex.Spherical.MSS.hasCompactSupport_dyadicHalfWaveSchwartzSymbol` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Literal angular half-wave/cube support | `Codex.Spherical.MSS.hasCompactSupport_angularDyadicCubeSchwartzSymbol` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Literal angular half-wave/cube support | `Codex.Spherical.MSS.contDiff_angularDyadicCubeSchwartzSymbol` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Literal angular half-wave/cube support | `Codex.Spherical.MSS.isScaledRayCubeCutoff` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Concrete scaled ray-cube cutoff | `Codex.Spherical.MSS.scaledRayCubeCutoff` | Proof completed | 2026-08-14 06:19:01 -04:00 |
| Concrete scaled ray-cube cutoff | `Codex.Spherical.MSS.isFourierCubeCutoff_translatedDilatedSchwartzCutoff` | Proof completed | 2026-08-14 06:19:01 -04:00 |
| Concrete scaled ray-cube cutoff | `Codex.Spherical.MSS.isScaledRayCubeCutoff_scaledRayCubeCutoff` | Proof completed | 2026-08-14 06:19:01 -04:00 |
| Concrete scaled ray-cube cutoff | `Codex.Spherical.MSS.integral_norm_iteratedFDeriv_scaledRayCubeCutoff` | Proof completed | 2026-08-14 06:19:01 -04:00 |
| Concrete scaled ray-cube phase calculus | `Codex.Spherical.MSS.support_scaledRayCubeCutoff_subset_closedBall` | Proof completed | 2026-08-14 07:09:45 -04:00 |
| Concrete scaled ray-cube phase calculus | `Codex.Spherical.MSS.support_iteratedFDeriv_scaledRayCubeCutoff_subset_closedBall` | Proof completed | 2026-08-14 07:09:45 -04:00 |
| Dimension-generic radial phase calculus | `Codex.Spherical.MSS.iteratedFDeriv_norm_smul_pos` | Proof completed | 2026-08-14 07:53:15 -04:00 |
| Dimension-generic radial phase calculus | `Codex.Spherical.MSS.exists_scaled_norm_iteratedFDeriv_bound` | Proof completed | 2026-08-14 07:53:15 -04:00 |
| Literal phase-mismatch residual calculus | `Codex.Spherical.MSS.fderiv_angularDyadicRayPhaseMismatch` | Proof completed | 2026-08-14 07:09:45 -04:00 |
| Matched plus-sheet phase mismatch | `Codex.Spherical.MSS.norm_iteratedFDeriv_angularDyadicRayPhaseMismatch_plus_zero_one_on_scaledRayCubeCutoff` | Proof completed | 2026-08-14 07:09:45 -04:00 |
| Matched plus-sheet higher phase mismatch | `Codex.Spherical.MSS.iteratedFDeriv_angularDyadicRayPhaseMismatch_plus_eq_norm_of_two_le` | Proof completed | 2026-08-14 07:53:15 -04:00 |
| Matched plus-sheet higher phase mismatch | `Codex.Spherical.MSS.exists_scaledRayCubeCutoff_plusMismatch_higherDerivativeBound` | Proof completed | 2026-08-14 07:53:15 -04:00 |
| Compact-time matched plus-sheet phase mismatch | `Codex.Spherical.MSS.norm_iteratedFDeriv_time_angularDyadicRayPhaseMismatch_plus_zero_one_on_scaledRayCubeCutoff` | Proof completed | 2026-08-14 07:09:45 -04:00 |
| Literal phase-mismatch residual model | `Codex.Spherical.MSS.angularDyadicResidualBaseSymbol` | Proof completed | 2026-08-14 06:41:11 -04:00 |
| Literal phase-mismatch residual model | `Codex.Spherical.MSS.angularDyadicRayPhaseMismatch` | Proof completed | 2026-08-14 06:41:11 -04:00 |
| Literal phase-mismatch residual model | `Codex.Spherical.MSS.angularDyadicResidualBaseSymbol_eq_phaseMismatch` | Proof completed | 2026-08-14 06:41:11 -04:00 |
| Literal phase-mismatch residual amplitude | `Codex.Spherical.MSS.angularDyadicResidualAmplitude` | Proof completed | 2026-08-14 07:31:56 -04:00 |
| Literal phase-mismatch residual amplitude | `Codex.Spherical.MSS.angularDyadicResidualAmplitude_apply` | Proof completed | 2026-08-14 07:31:56 -04:00 |
| Matched plus-sheet residual calculus | `Codex.Spherical.MSS.norm_iteratedFDeriv_angularDyadicResidualBaseSymbol_plus_zero_one_on_scaledRayCubeCutoff` | Proof completed | 2026-08-14 07:31:56 -04:00 |
| Concrete scaled ray-cube residual bound | `Codex.Spherical.MSS.scaledRayCubeResidualDerivativeBound` | Proof completed | 2026-08-14 06:41:11 -04:00 |
| Concrete scaled ray-cube residual bound | `Codex.Spherical.MSS.integral_norm_iteratedFDeriv_angularDyadicCubeResidualSymbol_le_scaledRayCubeCutoff` | Proof completed | 2026-08-14 06:41:11 -04:00 |
| Cutoff-supported residual Leibniz bridge | `Codex.Spherical.MSS.integral_norm_iteratedFDeriv_angularDyadicCubeResidualSymbol_le_scaledRayCubeCutoff_of_supportBounds` | Proof completed | 2026-08-14 07:31:56 -04:00 |
| Concrete plus-sheet residual budget | `Codex.Spherical.MSS.scaledRayCubePlusResidualFirstDerivativeBound` | Proof completed | 2026-08-14 07:31:56 -04:00 |
| Concrete plus-sheet residual derivative integral | `Codex.Spherical.MSS.integral_norm_iteratedFDeriv_angularDyadicCubeResidualSymbol_plus_le_scaledRayCubeCutoff_firstOrder` | Proof completed | 2026-08-14 07:31:56 -04:00 |
| All-order concrete plus-sheet residual budget | `Codex.Spherical.MSS.scaledRayCubePlusResidualBaseDerivativeBound` | Proof completed | 2026-08-14 08:48:58 -04:00 |
| All-order matched plus-sheet residual base bounds | `Codex.Spherical.MSS.exists_scaledRayCubeCutoff_plusResidualBaseDerivativeBounds` | Proof completed | 2026-08-14 08:48:58 -04:00 |
| All-order concrete plus-sheet residual derivative integral | `Codex.Spherical.MSS.exists_scaledRayCubeCutoff_plusResidualDerivativeIntegralBounds` | Proof completed | 2026-08-14 08:48:58 -04:00 |
| Explicit scaled ray-packet budget | `Codex.Spherical.MSS.scaledRayCubePacketBudget`; `Codex.Spherical.MSS.scaledRayCubePlusResidualLocalizationBudget` | Proof completed | 2026-08-14 08:48:58 -04:00 |
| Compact-time all-order plus-sheet ray localization (scale-dependent coefficient) | `Codex.Spherical.MSS.exists_scaledRayCubeCutoff_plus_ray_localized_of_explicitHighOrderBounds` | Proof completed | 2026-08-14 08:48:58 -04:00 |
| Compact-time literal ray localization | `Codex.Spherical.MSS.scaledRayCubeCutoff_ray_localized_of_residualBaseBounds_on_compactTimeSupport` | Proof completed | 2026-08-14 07:31:56 -04:00 |
| Compact-time concrete plus-sheet ray localization | `Codex.Spherical.MSS.scaledRayCubeCutoff_ray_localized_of_concretePlusFirstDerivativeBounds_on_compactTimeSupport` | Proof completed | 2026-08-14 07:31:56 -04:00 |

> High-order ray localization is now literal, but the coefficient is intentionally **not** recorded as scale-uniform.  The current hypotheses leave the amplitude seminorms and the cutoff width independent of `scale`; the exact residual derivative budget consequently retains powers of `width * sqrt scale`.  A scale-uniform coefficient for the existing `scaledRayCube...` interface needs additional normalized amplitude/cutoff hypotheses and is not used by `fineSquareFunctionEstimate`.

| Literal angular half-wave/cube support | `Codex.Spherical.MSS.support_angularDyadicCubeSchwartzSymbol_subset_frequencyCube` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Fixed-time cube-piece Fourier identity | `Codex.Spherical.MSS.fourier_angularDyadicCubePiece_apply` | Proof completed | 2026-08-19 22:01:21 -04:00 |
| Fixed-time cube-piece spatial support | `Codex.Spherical.MSS.support_fourier_angularDyadicCubePiece_subset_frequencyCube` | Proof completed | 2026-08-19 22:01:21 -04:00 |
| Fixed-time scaled-ray cube spatial support | `Codex.Spherical.MSS.support_fourier_scaledRayAngularDyadicCubePiece_subset_frequencyCube` | Proof completed | 2026-08-19 22:01:21 -04:00 |
| Singleton literal packet reconstruction | `Codex.Spherical.MSS.angularDyadicCubePacket_singleton_eq_timeCutoff_mul_piece` | Proof completed | 2026-08-19 22:01:21 -04:00 |
| Literal angular half-wave/cube residual | `Codex.Spherical.MSS.angularDyadicCubeResidualSymbol` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Literal angular half-wave/cube residual | `Codex.Spherical.MSS.angularDyadicCubeResidualSymbol_apply` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Literal angular half-wave/cube residual | `Codex.Spherical.MSS.angularDyadicCubeKernel_eq_residual_shifted` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Literal angular half-wave/cube ray localization | `Codex.Spherical.MSS.support_angularDyadicCubeResidualSymbol_subset_frequencyCube` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Literal angular half-wave/cube ray localization | `Codex.Spherical.MSS.norm_angularDyadicCubeSpaceTimeKernel_le_lightRayKernel_of_residual_seminorm` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Literal angular half-wave/cube ray localization | `Codex.Spherical.MSS.angularDyadicCubePacket_ray_localized_of_residual_seminorm` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Literal angular half-wave/cube ray localization | `Codex.Spherical.MSS.scaledRayCube_angularDyadicCubePacket_ray_localized_of_residual_seminorm` | Proof completed | 2026-08-14 05:48:44 -04:00 |
| Literal angular half-wave/cube ray localization | `Codex.Spherical.MSS.angularDyadicCubeResidualSymbol_fourierInv_seminorm_le_derivativeIntegrals` | Proof completed | 2026-08-14 06:01:37 -04:00 |
| Literal angular half-wave/cube ray localization | `Codex.Spherical.MSS.angularDyadicCubePacket_ray_localized_of_residual_derivativeIntegrals` | Proof completed | 2026-08-14 06:01:37 -04:00 |
| `thm:fourier-cube-square-function` | `Codex.Spherical.MSS.fourierCubeSquareFunction` | Proof completed | 2026-08-13 15:01:28 -04:00 |
| `thm:fourier-cube-square-function` | `Codex.Spherical.MSS.fourierCubeSquareFunction_nonneg` | Proof completed | 2026-08-13 15:01:28 -04:00 |
| `thm:fourier-cube-square-function` | `Codex.Spherical.MSS.integral_sq_fourierCubeSquareFunction_eq` | Proof completed | 2026-08-13 15:01:28 -04:00 |
| `thm:fourier-cube-square-function` | `Codex.Spherical.MSS.integral_sq_fourierCubeSquareFunction_eq_frequency` | Proof completed | 2026-08-13 15:01:28 -04:00 |
| `thm:fourier-cube-square-function` | `Codex.Spherical.MSS.integral_sq_fourierCubeSquareFunction_le_of_square_overlap` | Proof completed | 2026-08-13 15:01:28 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.unitLightRayDirections` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.mem_unitLightRayDirections_iff` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.lightRayTimeInterval` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.mem_lightRayTimeInterval_iff` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.lightRayTube` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.mem_lightRayTube_iff` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.lightRayTube_mono` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.norm_lightRayTerminalSeparation_sub_timeDirectionDifference_le_of_mem_inter` | Proof completed | 2026-08-14 07:35:11 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.abs_norm_lightRayTerminalSeparation_sub_time_mul_normDirectionDifference_le_of_mem_inter` | Proof completed | 2026-08-14 07:35:11 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.lightRayKernel` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.lightRayKernel_nonneg` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.lightRayKernel_decay_le_one` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.lightRayKernel_le_normalization` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.integral_lightRayKernel_spatial_eq_decayProfile` | Proof completed | 2026-08-14 07:35:11 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.aestronglyMeasurable_lightRayKernel_terminal_of_aestronglyMeasurable_direction` | Proof completed | 2026-08-14 07:35:11 -04:00 |
| `thm:mss-kakeya` measurable TT* layer | `Codex.Spherical.MSS.aestronglyMeasurable_lightRayKernel_of_aestronglyMeasurable_direction_comp` | Proof completed | 2026-08-14 07:56:07 -04:00 |
| `thm:mss-kakeya` measurable TT* layer | `Codex.Spherical.MSS.aestronglyMeasurable_lightRayKernel_joint_of_aestronglyMeasurable_direction` | Proof completed | 2026-08-14 07:56:07 -04:00 |
| `thm:mss-kakeya` measurable TT* layer | `Codex.Spherical.MSS.integral_lightRayKernel_mul_transpose_of_aestronglyMeasurable_direction` | Proof completed | 2026-08-14 07:56:07 -04:00 |
| `thm:mss-kakeya` measurable TT* layer | `Codex.Spherical.MSS.aestronglyMeasurable_lightRayTTStarIntegrand_of_aestronglyMeasurable_direction` | Proof completed | 2026-08-14 07:56:07 -04:00 |
| `thm:mss-kakeya` measurable TT* layer | `Codex.Spherical.MSS.aestronglyMeasurable_lightRayTTStarIntersectionProduct_of_aestronglyMeasurable_direction` | Proof completed | 2026-08-14 07:56:07 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.lightRayAverage` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.lightRayMaximal` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.HasLightRayMaximalEstimate` | Statement completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.continuumLightRayMeasure` | Proof completed | 2026-08-14 04:41:29 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.sq_norm_continuumFineKernelTerm_le_lightRayEnergy` | Proof completed | 2026-08-14 04:41:29 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.continuumFineKernelWeightedPairing_le_lightRayMaximal` | Proof completed | 2026-08-14 04:41:29 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.continuumFineKernelWeightedPairing_le_of_lightRayL2Energy` | Proof completed | 2026-08-14 04:41:29 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.finiteLightRayAverage` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.finiteLightRayMaximal` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.finiteLightRayAverage_nonneg` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.finiteLightRayMaximal_nonneg` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.finiteLightRayAverage_le_normalization_mul_sum_norm` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:light-ray-maximal` | `Codex.Spherical.MSS.finiteLightRayMaximal_le_normalization_mul_sum_norm` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.sq_sum_norm_sample_le_card_mul_sum_sq` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.sq_finiteLightRayAverage_le_crude_sampleEnergy` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.sq_finiteLightRayMaximal_le_crude_sampleEnergy` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.finiteLightRaySquareEnergy` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.finiteLightRaySquareEnergy_le_crude` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.lightRayTubeIncidences` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.mem_lightRayTubeIncidences_iff` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.lightRayTubeMultiplicity` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.lightRayTubeMultiplicity_eq_card_lightRayTubeIncidences` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `thm:mss-kakeya` | `Codex.Spherical.MSS.lightRayTubeMultiplicity_le_card_mul_card` | Proof completed | 2026-08-13 15:09:32 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineCubeTerm` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFinePiece` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineSquareFunction` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineCubeSquareFunction` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.fineCubeIncidences` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineDualPairing` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineCubeEnergy` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineAssignedCubeEnergy` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.HasFiniteFineKernelLocalization` | Statement completed | 2026-08-13 15:57:46 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.HasFiniteFineKernelMassBound` | Statement completed | 2026-08-13 15:57:46 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.sq_norm_sum_le_kernelMass_mul_weightedEnergy` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.finiteLightRayAverage_le_finiteLightRayMaximal` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.sq_norm_finiteFineCubeTerm_le_of_lightRayLocalization` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.sum_sq_norm_finiteFineCubeTerm_mul_norm_le_lightRayMaximal` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.sum_sq_norm_finiteFineCubeTerms_mul_norm_le_finiteLightRayMaximal` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.sq_finiteFineSquareFunction` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.sq_finiteFineCubeSquareFunction` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.sq_norm_finiteFinePiece_le_card_mul_sum_sq` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.sq_finiteFineSquareFunction_le_cubeMultiplicity_mul_sq` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineDualPairing_le_cubeMultiplicity_mul_finiteLightRayEnergy` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.fineCubeAssignments` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.fineCubeAssignmentFiber` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.HasFiniteFineCubeReverseOverlap` | Statement completed | 2026-08-13 15:57:46 -04:00 |
| Concrete owner-fiber cube model | `Codex.Spherical.MSS.ownerCubeSets` | Proof completed | 2026-08-14 05:48:32 -04:00 |
| Concrete owner-fiber cube model | `Codex.Spherical.MSS.hasFiniteFineCubeReverseOverlap_ownerCubeSets` | Proof completed | 2026-08-14 05:48:32 -04:00 |
| Concrete owner-fiber cube model | `Codex.Spherical.MSS.sum_sq_fourierCubeProjection_ownerCubeSets_eq` | Proof completed | 2026-08-14 05:48:32 -04:00 |
| Concrete owner-fiber cube model | `Codex.Spherical.MSS.integral_ownerCubeSquareEnergy_eq_frequency` | Proof completed | 2026-08-14 05:48:32 -04:00 |
| Concrete owner-fiber cube model | `Codex.Spherical.MSS.sum_angularDyadicCubePacket_ownerCubeSets_eq` | Proof completed | 2026-08-14 05:48:32 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineAssignedCubeEnergy_eq_sum_fibers` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineAssignedCubeEnergy_le_reverseOverlap_mul_finiteFineCubeEnergy` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineAssignedCubeEnergy_le_card_mul_finiteFineCubeEnergy` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineAssignedCubeEnergy_le_card_mul_finiteFineCubeEnergy_lightRay` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineAssignedCubeEnergy_le_reverseOverlap_mul_finiteFineCubeEnergy_lightRay` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineDualPairing_le_cubeMultiplicities_mul_finiteLightRayEnergy` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.finiteFineDualPairing_le_cubeMultiplicity_card_mul_finiteLightRayEnergy` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.sq_sum_norm_mul_zeroThicknessPlateOverlapPairs_le_multiplicity_mul_sum_sq` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.sq_sum_norm_mul_zeroThicknessPlateOverlapPairs_le_two_mul_sum_sq` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.finiteZeroThicknessOverlapSquareEnergy` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `prop:mss-overlap-square-function` | `Codex.Spherical.MSS.finiteZeroThicknessOverlapSquareEnergy_le_two_mul_sum` | Proof completed | 2026-08-13 15:57:46 -04:00 |
| `def:mss-fine-square-function` | `Codex.Spherical.MSS.fineSquareFunction` | Proof completed | 2026-08-13 15:47:13 -04:00 |
| `lem:mss-fine-kernel` | `Codex.Spherical.MSS.fineKernelLocalization` | Statement completed | 2026-08-13 16:18:27 -04:00 |
| `prop:mss-fine-square-function` | `Codex.Spherical.MSS.fineSquareFunctionEstimate` | Statement completed | 2026-08-13 15:47:13 -04:00 |
| `prop:mss-recombination` | `Codex.Spherical.MSS.recombination` | Statement completed | 2026-08-13 16:18:27 -04:00 |
| `thm:mss-p4` | `Codex.Spherical.MSS.conicL4Estimate_of_recombination_of_fineSquareFunctionEstimate` | Proof completed | 2026-08-14 04:08:58 -04:00 |
| Positive dyadic consequence of conic data | `Codex.Spherical.MSS.exists_plus_dyadicHalfWaveSpaceTime_L4_bound_of_conicData` | Proof completed | 2026-08-14 05:02:59 -04:00 |
| Two-sided dyadic consequence of one two-slab conic datum | `Codex.Spherical.MSS.exists_bothSign_dyadicHalfWaveSpaceTime_L4_bound_of_twoSidedConicData` | Proof completed | 2026-08-14 05:02:59 -04:00 |
| Conditional `p = 4` local smoothing from two-sided conic data | `Codex.Spherical.MSS.p4LocalSmoothing_of_twoSidedConicData` | Proof completed | 2026-08-14 05:07:14 -04:00 |

## `LeanSpherical/Codex/Spherical/Bourgain.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| `def:fourier-convention` | Mathlib Fourier convention | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:circular-average` | `Codex.Spherical.Bourgain.circularAverage` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:circular-average` | `Codex.Spherical.Bourgain.circularMaximal` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:circular-average` | `Codex.Spherical.Bourgain.fullCircularMaximal` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:circular-average` | `Codex.Spherical.Bourgain.circularAverage_eq_sphericalAverage` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `def:circular-average` | `Codex.Spherical.Bourgain.circularMaximal_eq_sphericalMaximal` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:intro-bourgain` | `Codex.Spherical.Bourgain.HasCircularMaximalSchwartzBound` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:intro-bourgain`; `cor:bourgain-final` | `Codex.Spherical.Bourgain.bourgainCircularMaximal` | ToDo | 2026-08-13 13:24:00 -04:00 |
| `thm:basic-analysis` | Mathlib analysis and measure-theory APIs | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:plancherel` | `Codex.Spherical.FourierRadius` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:hardy-littlewood` | `Codex.Spherical.HardyLittlewoodMaximal` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:radial-majorant` | `Codex.Spherical.Bourgain.radialSchwartzKernelMajorantConstant` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:radial-majorant` | `Codex.Spherical.Bourgain.scaledSchwartzConvolution_radialMajorant` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:time-sobolev` | `Codex.Spherical.Bourgain.norm_le_norm_add_timeDerivativeIntegral` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:time-sobolev` | `Codex.Spherical.Bourgain.timeSobolevL2` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| Unit-slab `L4` time Sobolev | `Codex.Spherical.Bourgain.timeSobolevFour_unit` | Proof completed | 2026-08-14 07:04:21 -04:00 |
| Unit-slab `L4` time supremum | `Codex.Spherical.Bourgain.timeSupremumFour_unit` | Proof completed | 2026-08-14 07:04:21 -04:00 |
| `lem:time-sobolev` | `Codex.Spherical.Bourgain.timeSamplingL2_of_uniformPartition` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:time-sobolev` | `Codex.Spherical.Bourgain.timeSamplingL2_of_pairwiseDisjointIntervals` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:time-sobolev` | `Codex.Spherical.Bourgain.timeSamplingL2_of_pairwiseDisjointComparableIntervals` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:time-sobolev` | `Codex.Spherical.Bourgain.timeSamplingL2_of_MSS_MaximalSeparated` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:time-sobolev` | `Codex.Spherical.Bourgain.timeSupremumL2` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| Dyadic time-scale arithmetic | `Codex.Spherical.Bourgain.dyadicTimeScale_eq_inv_natPow` | Proof completed | 2026-08-14 08:35:42 -04:00 |
| Finite dyadic maximal-separated grid | `Codex.Spherical.Bourgain.exists_MSS_MaximalSeparated` | Proof completed | 2026-08-14 08:35:42 -04:00 |
| Scale-local time increment energy | `Codex.Spherical.Bourgain.norm_sub_sq_le_abs_sub_mul_timeDerivativeEnergy` | Proof completed | 2026-08-14 08:35:42 -04:00 |
| Continuous scale-sensitive `L²` time maximum | `Codex.Spherical.Bourgain.timeSupremumL2_of_MSS_MaximalSeparated` | Proof completed | 2026-08-14 08:35:42 -04:00 |
| Measurable space-time scale-sensitive `L²` maximum | `Codex.Spherical.Bourgain.measurable_and_lintegral_iSup_ennreal_norm_sq_le_timeSamplingL2` | Proof completed | 2026-08-14 08:35:42 -04:00 |
| Scale-sensitive fourth-power time Sobolev | `Codex.Spherical.Bourgain.timeSobolevFour` | Proof completed | 2026-08-14 09:25:22 -04:00 |
| Fourth-power clipped-cell time sampling | `Codex.Spherical.Bourgain.timeSamplingFour_of_pairwiseDisjointComparableIntervals` | Proof completed | 2026-08-14 09:25:22 -04:00 |
| Fourth-power MSS separated-time sampling | `Codex.Spherical.Bourgain.timeSamplingFour_of_MSS_MaximalSeparated` | Proof completed | 2026-08-14 09:25:22 -04:00 |
| Fourth-power interval Holder estimate | `Codex.Spherical.Bourgain.intervalIntegral_norm_pow_four_le` | Proof completed | 2026-08-14 09:25:22 -04:00 |
| Fourth-power time increment energy | `Codex.Spherical.Bourgain.norm_sub_pow_four_le_abs_sub_pow_three_mul_timeDerivativeEnergy` | Proof completed | 2026-08-14 09:25:22 -04:00 |
| Continuous scale-sensitive fourth-power time maximum | `Codex.Spherical.Bourgain.timeSupremumFour_of_MSS_MaximalSeparated` | Proof completed | 2026-08-14 09:25:22 -04:00 |
| Measurable space-time scale-sensitive fourth-power maximum | `Codex.Spherical.Bourgain.measurable_and_lintegral_iSup_ennreal_norm_pow_four_le_timeSamplingL4` | Proof completed | 2026-08-14 09:25:22 -04:00 |
| `lem:time-sobolev` | `Codex.Spherical.Bourgain.timeSobolev` | ToDo | 2026-08-13 13:24:00 -04:00 |
| `cor:time-sobolev-spacetime` | `Codex.Spherical.Bourgain.timeSobolevL2_spacetime` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| Unit-slab spatial `L4` time Sobolev | `Codex.Spherical.Bourgain.timeSobolevFour_spacetime` | Proof completed | 2026-08-14 07:15:26 -04:00 |
| Unit-slab spatial `L4` time supremum | `Codex.Spherical.Bourgain.measurable_and_lintegral_iSup_ennreal_norm_pow_four_le_timeSobolev` | Proof completed | 2026-08-14 07:20:54 -04:00 |
| `cor:time-sobolev-spacetime` | `Codex.Spherical.Bourgain.timeSamplingL2_spacetime_of_MSS_MaximalSeparated` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `cor:time-sobolev-spacetime` | `Codex.Spherical.Bourgain.timeSobolevSpacetime` | ToDo | 2026-08-13 13:24:00 -04:00 |
| `lem:circle-stationary-phase` | `Codex.Spherical.Bourgain.circleStationaryPhase` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:circle-stationary-phase` | `Codex.Spherical.Bourgain.exists_circleMiddleMeridianLocalizedIntegral_decay_one` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` | `Codex.Spherical.Bourgain.circleSurfaceFourierMeridianNormalForm` | Proof completed | 2026-08-13 13:47:16 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleSurfaceFourierCoordinateWaveDecomposition` | Proof completed | 2026-08-13 14:34:41 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleWaveDecomposition` | ToDo | 2026-08-13 13:24:00 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleBandpassFourierMeridianNormalForm` | Proof completed | 2026-08-13 13:47:16 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleBandpassFourierCoordinateWaveNormalForm` | Proof completed | 2026-08-13 14:40:26 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleEndpointAmplitude` | Proof completed | 2026-08-13 14:44:11 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleEndpointDyadicNormalization` | Proof completed | 2026-08-13 14:44:11 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleEndpointDyadicNormalization_ne_zero` | Proof completed | 2026-08-13 14:44:11 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleEndpointMultiplier` | Proof completed | 2026-08-13 14:44:11 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleAnnularEndpointMultiplier` | Proof completed | 2026-08-13 15:11:47 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.hasCompactSupport_circleEndpointMultiplier` | Proof completed | 2026-08-13 14:44:11 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleEndpointMultiplier_factorization` | Proof completed | 2026-08-13 14:44:11 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleAnnularEndpointMultiplier_factorization` | Proof completed | 2026-08-13 15:11:47 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleEndpointScaledRadialAmplitude` | Proof completed | 2026-08-13 15:22:51 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.iteratedDeriv_circleEndpointScaledRadialAmplitude` | Proof completed | 2026-08-13 15:22:51 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.exists_norm_iteratedDeriv_circleEndpointScaledRadialAmplitude_decay` | Proof completed | 2026-08-13 15:22:51 -04:00 |
| Uniform endpoint radial derivatives | `Codex.Spherical.Bourgain.exists_uniform_norm_iteratedDeriv_circleEndpointScaledRadialAmplitude_le` | Proof completed | 2026-08-14 06:10:15 -04:00 |
| Uniform endpoint radial derivatives | `Codex.Spherical.Bourgain.exists_uniform_norm_iteratedFDeriv_circleEndpointScaledRadialComp_le` | Proof completed | 2026-08-14 06:33:17 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleAnnularEndpointScaledSymbol` | Proof completed | 2026-08-13 15:22:51 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleAnnularEndpointScaledSymbol_apply` | Proof completed | 2026-08-13 15:22:51 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleAnnularEndpointSchwartzSymbol` | Proof completed | 2026-08-13 15:29:32 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleAnnularEndpointSchwartzSymbol_apply` | Proof completed | 2026-08-13 15:29:32 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleAnnularEndpointSchwartzSymbol_factorization` | Proof completed | 2026-08-13 15:29:32 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleEndpointWaveContribution` | Proof completed | 2026-08-13 14:44:11 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleEndpointWaveContribution_factorization` | Proof completed | 2026-08-13 14:44:11 -04:00 |
| Endpoint multiplier temporal derivative | `Codex.Spherical.Bourgain.circleEndpointBandpassMultiplierTimeDerivative` | Proof completed | 2026-08-14 08:45:36 -04:00 |
| Endpoint multiplier temporal derivative | `Codex.Spherical.Bourgain.hasDerivAt_circleEndpointBandpassMultiplier` | Proof completed | 2026-08-14 08:45:36 -04:00 |
| Literal endpoint output derivative | `Codex.Spherical.Bourgain.circleEndpointWaveContributionTimeDerivative` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Literal endpoint output derivative | `Codex.Spherical.Bourgain.circleEndpointWaveContributionTimeDerivative_eq_fourierInv_multiplier` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint fixed-time `L²` scaling | `Codex.Spherical.Bourgain.exists_integral_norm_sq_circleEndpointWaveContribution_le_dyadicSqrtInverse` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative fixed-time `L²` scaling | `Codex.Spherical.Bourgain.exists_integral_norm_sq_circleEndpointWaveContributionTimeDerivative_le_dyadicSqrt` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Uniform derivative-annular multiplier | `Codex.Spherical.Bourgain.circleAnnularEndpointMultiplierTimeDerivative` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Uniform derivative-annular multiplier | `Codex.Spherical.Bourgain.circleAnnularEndpointMultiplierTimeDerivative_factorization` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Uniform derivative-annular multiplier | `Codex.Spherical.Bourgain.circleAnnularEndpointTimeDerivativeSchwartzSymbol` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Uniform derivative-annular multiplier family | `Codex.Spherical.Bourgain.aux_circleAnnularEndpointTimeDerivativeSchwartzFamily` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Uniform derivative-annular kernel bound | `Codex.Spherical.Bourgain.aux_HasCircleAnnularEndpointTimeDerivativeUniformKernelBound` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Uniform derivative-annular kernel bound | `Codex.Spherical.Bourgain.hasCircleAnnularEndpointTimeDerivativeUniformKernelBound` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative compact input | `Codex.Spherical.Bourgain.circleEndpointTimeDerivativeInputMultiplier` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative compact input | `Codex.Spherical.Bourgain.circleEndpointTimeDerivativeInputMultiplier_scaled_apply` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative compact input | `Codex.Spherical.Bourgain.circleEndpointTimeDerivativeInput` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative compact input | `Codex.Spherical.Bourgain.circleEndpointTimeDerivativeInput_fourier` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative half-wave identity | `Codex.Spherical.Bourgain.dyadicHalfWaveSymbol_mul_circleEndpointTimeDerivativeInputMultiplier` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative two-term factorization | `Codex.Spherical.Bourgain.circleAnnularEndpointTimeDerivativeSchwartzSymbol_factorization` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative two-term factorization | `Codex.Spherical.Bourgain.circleAnnularEndpointSchwartzSymbol_factorization_timeDerivativeInput` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative two-term factorization | `Codex.Spherical.Bourgain.circleEndpointWaveContributionTimeDerivativeFactored` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative two-term factorization | `Codex.Spherical.Bourgain.circleEndpointWaveContributionTimeDerivativeFactored_eq_literal` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint output time differentiability | `Codex.Spherical.Bourgain.continuous_and_hasDerivAt_circleEndpointWaveContribution` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Derivative-annular endpoint contribution | `Codex.Spherical.Bourgain.aux_circleAnnularEndpointTimeDerivativeWaveContribution` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Derivative-annular endpoint contribution | `Codex.Spherical.Bourgain.aux_circleAnnularEndpointTimeDerivativeWaveContribution_eq_relativeMultiplier_halfWave` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Derivative-annular endpoint `L⁴` stability | `Codex.Spherical.Bourgain.exists_circleAnnularEndpointTimeDerivativeWaveContribution_dyadicBall_stability` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Derivative-annular endpoint `L⁴` stability | `Codex.Spherical.Bourgain.exists_integral_norm_pow_four_circleAnnularEndpointTimeDerivativeWaveContribution_le` | Proof completed | 2026-08-14 10:05:15 -04:00 |
| Endpoint derivative compact input `L⁴` stability | `Codex.Spherical.Bourgain.exists_integral_norm_pow_four_circleEndpointTimeDerivativeInput_le` | Proof completed | 2026-08-14 11:51:57 -04:00 |
| Slab product integrability | `Codex.Spherical.Bourgain.integrable_norm_pow_four_prod_of_continuous_of_interval_integral_bound` | Proof completed | 2026-08-14 11:51:57 -04:00 |
| Endpoint slab product integrability | `Codex.Spherical.Bourgain.integrable_norm_pow_four_circleEndpointWaveContribution_prod_of_gain` | Proof completed | 2026-08-14 11:51:57 -04:00 |
| Endpoint derivative slab product integrability | `Codex.Spherical.Bourgain.integrable_norm_pow_four_circleEndpointWaveContributionTimeDerivative_prod_of_gain` | Proof completed | 2026-08-14 11:51:57 -04:00 |
| Endpoint fourth-power slab energy | `Codex.Spherical.Bourgain.exists_intervalIntegral_integral_norm_pow_four_circleEndpointWaveContribution_le_gain` | Proof completed | 2026-08-14 11:51:57 -04:00 |
| Endpoint derivative fourth-power slab energy | `Codex.Spherical.Bourgain.exists_intervalIntegral_integral_norm_pow_four_circleEndpointWaveContributionTimeDerivative_le_gain` | Proof completed | 2026-08-14 11:51:57 -04:00 |
| Endpoint continuous local maximal `L⁴` estimate | `Codex.Spherical.Bourgain.exists_memLp_four_and_eLpNorm_iSup_circleEndpointWaveContribution_of_positiveLocalSmoothingGain` | Proof completed | 2026-08-14 11:51:57 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleMiddleWaveContribution` | Proof completed | 2026-08-13 15:11:47 -04:00 |
| Middle-wave slab integrability | `Codex.Spherical.Bourgain.aux_integrable_norm_sq_circleMiddleWaveContribution_prod` | Proof completed | 2026-08-14 09:02:46 -04:00 |
| Middle-wave dyadic time energy | `Codex.Spherical.Bourgain.aux_exists_intervalIntegral_integral_norm_sq_circleMiddleWaveContribution_le_dyadicInverse` | Proof completed | 2026-08-14 09:02:46 -04:00 |
| Middle-wave dyadic time maximum | `Codex.Spherical.Bourgain.aux_exists_memLp_two_and_integral_norm_sq_iSup_circleMiddleWaveContribution_le_dyadicGain` | Proof completed | 2026-08-14 09:02:46 -04:00 |
| Middle-wave continuous maximal definition | `Codex.Spherical.Bourgain.circleMiddleWaveMaximal` | Proof completed | 2026-08-14 09:15:22 -04:00 |
| Middle-wave finite dyadic `L²` assembly | `Codex.Spherical.Bourgain.exists_memLp_two_and_eLpNorm_sum_circleMiddleWaveMaximal_le` | Proof completed | 2026-08-14 09:15:22 -04:00 |
| Rapid middle-wave local `L⁴` maximum | `Codex.Spherical.Bourgain.exists_memLp_four_and_eLpNorm_iSup_circleMiddleWaveContribution_le_rapid_dyadicDecay` | Proof completed | 2026-08-14 13:16:27 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.circleDyadicBandpassThreeWaveDecomposition` | Proof completed | 2026-08-13 15:11:47 -04:00 |
| `lem:circle-stationary-phase` | `Codex.Spherical.Bourgain.exists_circleEndpointAmplitude_decay` | Proof completed | 2026-08-13 14:49:34 -04:00 |
| `lem:circle-stationary-phase` | `Codex.Spherical.Bourgain.contDiff_circleEndpointAmplitude` | Proof completed | 2026-08-13 15:22:51 -04:00 |
| Endpoint temporal derivative | `Codex.Spherical.Bourgain.circleEndpointAmplitudeTimeDerivative` | Proof completed | 2026-08-14 08:40:15 -04:00 |
| Endpoint temporal derivative | `Codex.Spherical.Bourgain.hasDerivAt_circleEndpointAmplitude_time` | Proof completed | 2026-08-14 08:40:15 -04:00 |
| `lem:circle-stationary-phase` | `Codex.Spherical.Bourgain.exists_iteratedDeriv_circleEndpointAmplitude_abs_decay` | Proof completed | 2026-08-13 15:22:51 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.norm_circleEndpointDyadicNormalization` | Proof completed | 2026-08-13 14:49:34 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.norm_circleEndpointMultiplier_le_of_amplitude_bound` | Proof completed | 2026-08-13 14:49:34 -04:00 |
| `prop:circle-wave-decomposition` | `Codex.Spherical.Bourgain.exists_norm_circleEndpointMultiplier_le_on_dyadicBandpass` | Proof completed | 2026-08-13 14:49:34 -04:00 |
| Uniform endpoint Fourier-side mass | `Codex.Spherical.Bourgain.exists_norm_circleAnnularEndpointScaledSymbol_le` | Proof completed | 2026-08-14 06:03:21 -04:00 |
| Uniform endpoint Fourier-side mass | `Codex.Spherical.Bourgain.circleAnnularEndpointSchwartzFamily_support_subset` | Proof completed | 2026-08-14 06:03:21 -04:00 |
| Uniform endpoint Fourier-side derivatives | `Codex.Spherical.Bourgain.circleAnnularEndpointSchwartzFamily_support_subset_annulus` | Proof completed | 2026-08-14 06:43:36 -04:00 |
| Uniform endpoint Fourier-side mass | `Codex.Spherical.Bourgain.exists_integral_norm_circleAnnularEndpointSchwartzFamily_le` | Proof completed | 2026-08-14 06:03:21 -04:00 |
| Uniform endpoint Fourier-side derivatives | `Codex.Spherical.Bourgain.exists_uniform_norm_iteratedFDeriv_circleAnnularEndpointSchwartzFamily_le` | Proof completed | 2026-08-14 06:43:36 -04:00 |
| Uniform endpoint Fourier-side IBP | `Codex.Spherical.Bourgain.exists_compactFourierIBPConstant_circleAnnularEndpointSchwartzFamily_le` | Proof completed | 2026-08-14 06:45:47 -04:00 |
| Uniform endpoint kernel bound | `Codex.Spherical.Bourgain.hasCircleAnnularEndpointUniformKernelBound` | Proof completed | 2026-08-14 06:45:47 -04:00 |
| Endpoint/half-wave factorization | `Codex.Spherical.Bourgain.circleAnnularEndpointHalfWaveOutput` | Proof completed | 2026-08-14 07:40:19 -04:00 |
| Endpoint/half-wave factorization | `Codex.Spherical.Bourgain.circleAnnularEndpointHalfWaveOutput_fourier` | Proof completed | 2026-08-14 07:40:19 -04:00 |
| Endpoint/half-wave factorization | `Codex.Spherical.Bourgain.circleAnnularEndpointHalfWaveOutput_apply` | Proof completed | 2026-08-14 07:49:28 -04:00 |
| Endpoint/half-wave factorization | `Codex.Spherical.Bourgain.aux_circleAnnularEndpointWaveContribution_eq_relativeMultiplier_halfWave` | Proof completed | 2026-08-14 07:40:19 -04:00 |
| Uniform endpoint maximal family | `Codex.Spherical.Bourgain.aux_circleAnnularEndpointMultiplierMaximal_majorant` | Proof completed | 2026-08-14 06:47:32 -04:00 |
| Uniform endpoint maximal family | `Codex.Spherical.Bourgain.aux_circleAnnularEndpointMultiplierMaximal_strong_type` | Proof completed | 2026-08-14 06:47:32 -04:00 |
| Moving relative-band local time | `Codex.Spherical.Bourgain.CircleRelativeBandLocalTime` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band unit cutoff | `Codex.Spherical.Bourgain.circleRelativeBandUnitDifference` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band unit cutoff | `Codex.Spherical.Bourgain.circleRelativeBandUnitDifference_apply` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band compact family | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitFamily` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band compact family | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitFamily_apply` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band exact rescaling | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitFamily_at_dyadicScale` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band exact rescaling | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitFamily_at_dyadicScale_eq_movingBand` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band compact support | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitFamily_support_subset_annulus` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band time derivative | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitTimeDerivative` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band time derivative | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitTimeDerivative_apply_core` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band time derivative | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitTimeDerivative_apply` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band time derivative support | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitTimeDerivative_support_subset_annulus` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band uniform derivatives | `Codex.Spherical.Bourgain.exists_uniform_norm_iteratedFDeriv_circleRelativeBandFatUnitFamily_le` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band uniform derivatives | `Codex.Spherical.Bourgain.exists_uniform_norm_iteratedFDeriv_circleRelativeBandFatUnitTimeDerivative_le` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band uniform Fourier mass | `Codex.Spherical.Bourgain.exists_integral_norm_circleRelativeBandFatUnitFamily_le` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band uniform Fourier mass | `Codex.Spherical.Bourgain.exists_integral_norm_circleRelativeBandFatUnitTimeDerivative_le` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band uniform Fourier IBP | `Codex.Spherical.Bourgain.exists_compactFourierIBPConstant_circleRelativeBandFatUnitFamily_le` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band uniform Fourier IBP | `Codex.Spherical.Bourgain.exists_compactFourierIBPConstant_circleRelativeBandFatUnitTimeDerivative_le` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band uniform kernel | `Codex.Spherical.Bourgain.exists_circleRelativeBandFatUnit_uniformKernelBound` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band uniform derivative kernel | `Codex.Spherical.Bourgain.exists_circleRelativeBandFatUnitTimeDerivative_uniformKernelBound` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band simultaneous kernel certificate | `Codex.Spherical.Bourgain.exists_circleRelativeBandFatUnit_uniformKernelBounds` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band finite fat decomposition | `Codex.Spherical.Bourgain.circleRelativeBand_fatDyadicBandpassMultiplier_eq_sum_intDyadic` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band finite fat decomposition | `Codex.Spherical.Bourgain.circleRelativeBand_fatDyadicBandpassMultiplier_eq_sum_dyadic` | Proof completed | 2026-08-14 10:25:05 -04:00 |
| Moving relative-band fixed half-wave output | `Codex.Spherical.Bourgain.circleRelativeBandFatHalfWaveOutput` | Proof completed | 2026-08-14 12:33:00 -04:00 |
| Moving relative-band fixed half-wave derivative | `Codex.Spherical.Bourgain.circleRelativeBandFatHalfWaveOutputTimeDerivative` | Proof completed | 2026-08-14 12:33:00 -04:00 |
| Moving relative-band local maximal `L⁴` transfer | `Codex.Spherical.Bourgain.exists_memLp_four_and_eLpNorm_iSup_circleRelativeBandFatHalfWaveOutput_of_positiveLocalSmoothingGain` | Proof completed | 2026-08-14 12:33:00 -04:00 |
| Moving-fat middle local maximal `L⁴` decay | `Codex.Spherical.Bourgain.exists_memLp_four_and_eLpNorm_iSup_circleRelativeBandFatMiddleOutput_le_rapid_dyadicDecay` | Proof completed | 2026-08-19 21:42:21 -04:00 |
| Literal moving-fat unit-slab input | `Codex.Spherical.Bourgain.circleRelativeBandFatInputProjection` | Proof completed | 2026-08-19 21:42:21 -04:00 |
| Literal moving-fat unit-slab output | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitSlabOutput` | Proof completed | 2026-08-19 21:42:21 -04:00 |
| Literal moving-fat unit-slab maximal | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitSlabMaximal` | Proof completed | 2026-08-19 21:42:21 -04:00 |
| Moving-fat unit-slab compact factorization | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitSlabOutput_eq_compactMultiplier` | Proof completed | 2026-08-19 21:42:21 -04:00 |
| Moving-fat unit-slab five-band factorization | `Codex.Spherical.Bourgain.circleRelativeBandFatUnitSlabOutput_eq_sum_five_dyadic` | Proof completed | 2026-08-19 21:42:21 -04:00 |
| All-radius `p = 4` reassembly from literal moving-fat unit slab | `Codex.Spherical.Bourgain.hasRelativeCircularBandGeometricDecay_four_of_circleRelativeBandFatUnitSlab` | Proof completed | 2026-08-19 22:15:08 -04:00 |
| Literal moving-fat unit-slab geometric fourth moment | `Codex.Spherical.Bourgain.exists_circleRelativeBandFatUnitSlab_geometric_fourth_moment_of_positiveLocalSmoothingGain` | Proof completed | 2026-08-20 00:40:04 -04:00 |
| Positive local smoothing to relative circular-band decay | `Codex.Spherical.Bourgain.hasRelativeCircularBandGeometricDecay_four_of_positiveLocalSmoothingGain` | Proof completed | 2026-08-20 00:40:04 -04:00 |
| Conditional planar circular maximal bound from positive local smoothing | `Codex.Spherical.Bourgain.hasCircularMaximalSchwartzBound_four_of_positiveLocalSmoothingGain` | Proof completed | 2026-08-20 00:40:04 -04:00 |
| All-radius uniform planar `p = 2` reassembly from literal moving-fat unit slab | `Codex.Spherical.Bourgain.exists_memLp_two_and_eLpNorm_restrictedRelativeBandpassSphericalMaximal_of_circleRelativeBandFatUnitSlab` | Proof completed | 2026-08-20 01:01:08 -04:00 |
| Unconditional all-radius uniform planar `p = 2` moving relative-band maximal bound | `Codex.Spherical.Bourgain.exists_memLp_two_and_eLpNorm_restrictedRelativeBandpassSphericalMaximal` | Proof completed | 2026-08-20 01:53:17 -04:00 |
| Uniform `L²` plus decaying `L⁴` relative-band interpolation at every finite `p > 2` | `Codex.Spherical.Bourgain.hasRelativeCircularBandGeometricDecay_all_gt_two_of_uniform` | Proof completed | 2026-08-20 02:09:50 -04:00 |
| Positive local smoothing to all-finite-exponent relative circular-band decay | `Codex.Spherical.Bourgain.hasRelativeCircularBandGeometricDecay_of_positiveLocalSmoothingGain` | Proof completed | 2026-08-20 02:09:50 -04:00 |
| Conditional planar circular maximal bound from positive local smoothing at every finite `p > 2` | `Codex.Spherical.Bourgain.hasCircularMaximalSchwartzBound_of_positiveLocalSmoothingGain` | Proof completed | 2026-08-20 02:09:50 -04:00 |
| `def:positive-gain` | `Codex.Spherical.MSS.HasPositiveLocalSmoothingGain` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `lem:annular-stability` | `Codex.Spherical.Bourgain.exists_circleAnnularEndpointWaveContribution_dyadicBall_stability` | Proof completed | 2026-08-14 08:07:15 -04:00 |
| `lem:endpoint-L4-stability` | `Codex.Spherical.Bourgain.exists_integral_norm_pow_four_circleAnnularEndpointWaveContribution_le` | Proof completed | 2026-08-14 08:18:06 -04:00 |
| `prop:annular-maximal` | `Codex.Spherical.Bourgain.annularCircularMaximal` | ToDo | 2026-08-13 13:24:00 -04:00 |
| `def:relative-frequency` | `Codex.Spherical.Bourgain.relativeFrequencyDecomposition` | ToDo | 2026-08-13 13:24:00 -04:00 |
| `lem:low-relative-frequency` | `Codex.Spherical.Bourgain.lowRelativeFrequencies` | ToDo | 2026-08-13 13:24:00 -04:00 |
| `lem:high-frequency-scaling` | `Codex.Spherical.Bourgain.highFrequencyScaling` | ToDo | 2026-08-13 13:24:00 -04:00 |
| `thm:conditional-bourgain` | `Codex.Spherical.Bourgain.HasRelativeCircularBandGeometricDecay` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:conditional-bourgain` | `Codex.Spherical.Bourgain.hasCircularMaximalSchwartzBound_of_relativeBandGeometricDecay` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:conditional-bourgain` | `Codex.Spherical.Bourgain.conditionalCircularMaximal` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:conditional-bourgain` | `Codex.Spherical.Bourgain.circleBandpassShortIntervalL2` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:conditional-bourgain` | `Codex.Spherical.Bourgain.circleBandpassReciprocalIntervalL2` | Proof completed | 2026-08-13 13:50:03 -04:00 |
| `thm:conditional-bourgain` | `Codex.Spherical.Bourgain.circleBandpassUnitIntervalL2_of_finiteCover` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `thm:conditional-bourgain` | `Codex.Spherical.Bourgain.circleBandpassUnitIntervalL2` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| `cor:conditional-extension` | `Codex.Spherical.Bourgain.conditionalExtension` | ToDo | 2026-08-13 13:24:00 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/DiagonalTheorem.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Final requested integration | `Codex.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_sphericalMaximal_le_of_bourgain` | Proof completed | 2026-08-13 13:24:00 -04:00 |
| Final requested integration | `Codex.Spherical.FractalDilations.DiagonalTheorem.eLpNorm_sphericalMaximal_le` | ToDo | 2026-08-13 13:24:00 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/SmoothEndpointAmplitude.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.SmoothEndpointAmplitude.contDiff_smoothEndpointAmplitude` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.SmoothEndpointAmplitude.contDiff_smoothEndpointProfile` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.SmoothEndpointAmplitude.smoothEndpointAmplitude_eventuallyEq_zero_at_one` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.SmoothEndpointAmplitude.smoothEndpointProfile_eventuallyEq_zero_at_one` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.SmoothEndpointAmplitude.iteratedDeriv_smoothEndpointAmplitude_at_one` | Proof completed | 2026-08-13 14:20:00 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/QuadraticStationaryPhase.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.VanishesNearOne` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.VanishesNearOne.deriv` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.exists_pos_norm_le_on_unit_of_contDiff` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.exists_quadraticMoment_zero_decay` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.quadraticMomentIntegral_succ_two_recurrence` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.quadraticMomentIntegral_one_recurrence` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.exists_quadraticMoment_one_decay` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.exists_quadraticMoment_decay` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.smoothEndpointQuadraticIntegral_eq_quadraticMomentIntegral` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.smoothEndpointQuadraticIntegral_neg_eq_conj` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticStationaryPhase.exists_smoothEndpointQuadraticIntegral_abs_decay` | Proof completed | 2026-08-13 14:20:00 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/QuadraticMomentDerivatives.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.hasDerivAt_quadraticMomentIntegral` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.deriv_quadraticMomentIntegral` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.iteratedDeriv_quadraticMomentIntegral` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.contDiff_quadraticMomentIntegral` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.exists_norm_quadraticMomentIntegral_le` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.exists_iteratedDeriv_quadraticMomentIntegral_decay` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.exists_iteratedDeriv_smoothEndpointQuadraticIntegral_decay` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.iteratedDeriv_smoothEndpointQuadraticIntegral` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.contDiff_smoothEndpointQuadraticIntegral` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.iteratedDeriv_smoothEndpointQuadraticIntegral_comp_mul` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.exists_iteratedDeriv_smoothEndpointQuadraticIntegral_abs_decay` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.exists_norm_smoothEndpointQuadraticIntegral_le` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.exists_iteratedDeriv_smoothEndpointQuadraticIntegral_comp_mul_le` | Proof completed | 2026-08-13 14:20:00 -04:00 |
| Supporting planar stationary-phase foundation | `Codex.Spherical.FractalDilations.QuadraticMomentDerivatives.exists_iteratedDeriv_smoothEndpointQuadraticIntegral_comp_mul_abs_decay` | Proof completed | 2026-08-13 14:20:00 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/CoordinateMeridianWaves.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| `prop:circle-wave-decomposition` supporting coordinate form | `Codex.Spherical.FractalDilations.CoordinateMeridianWaves.coordinateUpperMeridianLocalizedIntegral_eq_smoothEndpointQuadratic` | Proof completed | 2026-08-13 14:17:00 -04:00 |
| `prop:circle-wave-decomposition` supporting coordinate form | `Codex.Spherical.FractalDilations.CoordinateMeridianWaves.coordinateLowerMeridianLocalizedIntegral_eq_smoothEndpointQuadratic` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting coordinate form | `Codex.Spherical.FractalDilations.CoordinateMeridianWaves.intervalIntegral_meridian_eq_coordinateLocalizedPartition` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting coordinate form | `Codex.Spherical.FractalDilations.CoordinateMeridianWaves.surfaceFourier_succ_eq_coordinateSmoothWaves` | Proof completed | 2026-08-13 14:17:00 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/PlanarEndpointAmplitude.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.planarEndpointProfileReal` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.planarEndpointProfile` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.planarEndpointQuadraticIntegral` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.planarEndpointProfileReal_eq_raw` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.planarEndpointGuardedSqrt_ne_zero` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.contDiff_planarEndpointProfileReal` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.contDiff_planarEndpointProfile` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.planarEndpointProfile_eventuallyEq_zero_at_one` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.exists_planarEndpointQuadraticIntegral_decay` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.exists_iteratedDeriv_planarEndpointQuadraticIntegral_decay` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.iteratedDeriv_planarEndpointQuadraticIntegral` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.contDiff_planarEndpointQuadraticIntegral` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.planarEndpointQuadraticIntegral_neg_eq_conj` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.norm_planarEndpointQuadraticIntegral_neg` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.exists_iteratedDeriv_planarEndpointQuadraticIntegral_abs_decay` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar endpoint | `Codex.Spherical.FractalDilations.PlanarEndpointAmplitude.exists_iteratedDeriv_planarEndpointQuadraticIntegral_le` | Proof completed | 2026-08-13 14:24:00 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/PlanarCoordinateMeridianWaves.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| `prop:circle-wave-decomposition` supporting planar coordinate form | `Codex.Spherical.FractalDilations.PlanarCoordinateMeridianWaves.coordinateUpperMeridianLocalizedIntegral_zero_eq_planarEndpointQuadratic` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar coordinate form | `Codex.Spherical.FractalDilations.PlanarCoordinateMeridianWaves.coordinateLowerMeridianLocalizedIntegral_zero_eq_planarEndpointQuadratic` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar coordinate form | `Codex.Spherical.FractalDilations.PlanarCoordinateMeridianWaves.circleMeridian_eq_coordinatePlanarSmoothWaves` | Proof completed | 2026-08-13 14:24:00 -04:00 |
| `prop:circle-wave-decomposition` supporting planar coordinate form | `Codex.Spherical.FractalDilations.PlanarCoordinateMeridianWaves.surfaceFourier_two_eq_coordinatePlanarSmoothWaves` | Proof completed | 2026-08-13 14:24:00 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/CoordinateMiddleNonstationary.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.sqrt_one_sub_sin_eq_coordinateUpperArgument` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.sqrt_one_add_sin_eq_coordinateLowerArgument` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateUpperMeridianCutoff_eq_coordinate` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateLowerMeridianCutoff_eq_coordinate` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.contDiff_coordinateUpperMeridianCutoff` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.contDiff_coordinateLowerMeridianCutoff` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.contDiff_coordinateMiddleMeridianCutoff` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateLowerMeridianCutoff_eq_upper_neg` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateUpperMeridianCutoff_eq_zero_of_le_pi_div_four` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateUpperMeridianCutoff_eq_one_of_fifteen_pi_div_thirty_two_le` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateLowerMeridianCutoff_eq_zero_of_neg_pi_div_four_le` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateLowerMeridianCutoff_eq_one_of_theta_le_neg_fifteen_pi_div_thirty_two` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateMiddleMeridianCutoff_eq_zero_of_large_abs` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateUpperMeridianLocalizedIntegral_eq_full_cutoff` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateLowerMeridianLocalizedIntegral_eq_full_cutoff` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateMiddleMeridianLocalizedIntegral_eq_middle_cutoff` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateMiddleGuardCutoff_eq_one_of_abs_le` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateMiddleCosineGuard_pos` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.contDiff_coordinateMiddleCosineGuard` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.contDiff_coordinateMiddleIBPAmplitudeReal` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.contDiff_coordinateMiddleIBPAmplitude` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateMiddleIBPAmplitude_mul_cos_eq_middle` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateMiddleIBPAmplitude_eq_zero_at_meridian_endpoints` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.coordinateMiddleMeridianLocalizedIntegral_eq_neg_inv_mul_deriv_integral` | Proof completed | 2026-08-13 16:06:10 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleNonstationary.exists_coordinateMiddleMeridianLocalizedIntegral_decay_one` | Proof completed | 2026-08-13 16:06:10 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/CoordinateMiddleRapidDecay.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleRapidDecay.coordinateMiddleIBPCompactAmplitude` | Proof completed | 2026-08-13 17:18:50 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleRapidDecay.coordinateMiddleIBPCompactIntegral` | Proof completed | 2026-08-13 17:18:50 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleRapidDecay.coordinateMiddleIBPCompactAmplitude_eq_zero_of_large_abs` | Proof completed | 2026-08-13 17:18:50 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleRapidDecay.contDiff_coordinateMiddleIBPCompactAmplitude` | Proof completed | 2026-08-13 17:18:50 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleRapidDecay.coordinateMiddleIBPCompactAmplitude_zero_mul_cos_eq_middle` | Proof completed | 2026-08-13 17:18:50 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleRapidDecay.coordinateMiddleIBPCompactAmplitude_succ_mul_cos_eq_deriv` | Proof completed | 2026-08-13 17:18:50 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleRapidDecay.coordinateMiddleMeridianLocalizedIntegral_eq_coordinateMiddleIBPCompactIntegral_zero` | Proof completed | 2026-08-13 17:18:50 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleRapidDecay.coordinateMiddleIBPCompactIntegral_eq_neg_inv_mul_succ` | Proof completed | 2026-08-13 17:18:50 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleRapidDecay.coordinateMiddleMeridianLocalizedIntegral_eq_iteratedIBPCompactIntegral` | Proof completed | 2026-08-13 17:18:50 -04:00 |
| `lem:circle-stationary-phase` supporting middle nonstationary term | `Codex.Spherical.FractalDilations.CoordinateMiddleRapidDecay.exists_coordinateMiddleMeridianLocalizedIntegral_abs_decay` | Proof completed | 2026-08-13 17:18:50 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/CentralMeridianIBP.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| All-order compact central-meridian IBP | `Codex.Spherical.FractalDilations.CentralMeridianIBP.contDiff_centralMeridianIBPAmplitude` | Proof completed | 2026-08-14 11:09:38 -04:00 |
| All-order compact central-meridian IBP | `Codex.Spherical.FractalDilations.CentralMeridianIBP.centralMeridianIBPIntegral_eq_iterated` | Proof completed | 2026-08-14 11:09:38 -04:00 |
| All-order compact central-meridian IBP | `Codex.Spherical.FractalDilations.CentralMeridianIBP.exists_centralMeridianIBPIntegral_abs_decay` | Proof completed | 2026-08-14 11:09:38 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/CoordinateMiddleParameterDerivatives.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| All-order middle frequency differentiation | `Codex.Spherical.FractalDilations.CoordinateMiddleParameterDerivatives.hasDerivAt_coordinateMiddleSineMomentIntegral` | Proof completed | 2026-08-14 11:09:38 -04:00 |
| All-order middle frequency differentiation | `Codex.Spherical.FractalDilations.CoordinateMiddleParameterDerivatives.contDiff_coordinateMiddleMeridianLocalizedIntegral` | Proof completed | 2026-08-14 11:09:38 -04:00 |
| All-order middle frequency decay | `Codex.Spherical.FractalDilations.CoordinateMiddleParameterDerivatives.exists_iteratedDeriv_coordinateMiddleMeridianLocalizedIntegral_abs_decay` | Proof completed | 2026-08-14 11:09:38 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/OscillatoryIBP.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.OscillatoryIBP.star_oscillatoryExp` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.OscillatoryIBP.norm_oscillatoryExp` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.OscillatoryIBP.oscillatoryExp_mul` | Proof completed | 2026-08-13 14:57:55 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/AllDimensionalRadialPairKernel.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.AllDimensionalRadialPairKernel.norm_absoluteDyadicBandpass_le_two_allDimensions` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.AllDimensionalRadialPairKernel.q4DyadicPairKernel_eq_annular_surfaceFourier_intervalIntegral` | Proof completed | 2026-08-13 14:57:55 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/AllDimensionalTripleWaveNormalForm.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.AllDimensionalTripleWaveNormalForm.coordinateSurfaceWaveSum_eq_three_radialTerms` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.AllDimensionalTripleWaveNormalForm.surfaceFourier_eq_coordinateSurfaceWaveSum` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.AllDimensionalTripleWaveNormalForm.q4DyadicPairKernel_eq_annular_coordinateTripleWaveIntegral` | Proof completed | 2026-08-13 14:57:55 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/PlanarTripleWaveNormalForm.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.PlanarTripleWaveNormalForm.planarCoordinateSurfaceWaveSum_eq_three_radialTerms` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.PlanarTripleWaveNormalForm.q4DyadicPairKernel_two_eq_annular_planarCoordinateTripleWaveIntegral` | Proof completed | 2026-08-13 14:57:55 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/TripleWaveConeGeometry.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.TripleWaveConeGeometry.abs_radiusDifference_add_ge_quarter_gap` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.TripleWaveConeGeometry.abs_signed_triple_phase_ge_quarter_gap` | Proof completed | 2026-08-13 14:57:55 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/CoordinateTripleWaveExpansion.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.CoordinateTripleWaveExpansion.mem_coordinateWaveParts` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.CoordinateTripleWaveExpansion.exists_coordinateWaveRadialPhase_sign` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.CoordinateTripleWaveExpansion.abs_coordinateTripleWavePhase_ge_quarter_gap_of_physical_middle` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.CoordinateTripleWaveExpansion.coordinateTripleWaveTerm_eq_coefficient_mul_oscillatoryExp` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.CoordinateTripleWaveExpansion.q4CoordinateTripleWaveRadialIntegrand_eq_finset_sum` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.CoordinateTripleWaveExpansion.planarCoordinateTripleWaveTerm_eq_coefficient_mul_oscillatoryExp` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.CoordinateTripleWaveExpansion.q4PlanarCoordinateTripleWaveRadialIntegrand_eq_finset_sum` | Proof completed | 2026-08-13 14:57:55 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/CompactOscillatoryIBP.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.CompactOscillatoryIBP.hasOscillatoryIBPChain_iteratedDeriv_of_contDiff` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.CompactOscillatoryIBP.exists_pos_norm_iteratedDeriv_le_on_Icc_of_contDiff` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.CompactOscillatoryIBP.exists_norm_intervalIntegral_mul_oscillatoryExp_le_iterated_of_contDiff` | Proof completed | 2026-08-13 14:57:55 -04:00 |

## `LeanSpherical/Codex/Spherical/FractalDilations/NormalizedDyadicRadialCutoff.lean`

| Blueprint label | Lean name | Status | Last update |
| --- | --- | --- | --- |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.NormalizedDyadicRadialCutoff.normalizedDyadicRadialBandpass_eventuallyEq_zero_left` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.NormalizedDyadicRadialCutoff.normalizedDyadicRadialBandpass_eventuallyEq_zero_right` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.NormalizedDyadicRadialCutoff.absoluteDyadicBandpass_smul_dyadicScale_eq_normalizedDyadicRadialBandpass` | Proof completed | 2026-08-13 14:57:55 -04:00 |
| Supporting planar triple-wave foundation | `Codex.Spherical.FractalDilations.NormalizedDyadicRadialCutoff.hasOscillatoryIBPChain_normalizedDyadicRadialBandpass_mul` | Proof completed | 2026-08-13 14:57:55 -04:00 |
