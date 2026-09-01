# BRRS formalization status ledger

Source: Beltran--Roos--Rutar--Seeger, [*A fractal local smoothing problem for
the wave equation*](https://arxiv.org/abs/2501.12805).

Scope: every numbered theorem, proposition, corollary, and displayed equation
used in the proofs of Theorems 1.2 and 1.1, plus each unnumbered prerequisite
needed to expose the actual proof dependency graph.

## Strict forward-dependency convention

This is a topological sort of the logical proof DAG, not a reading order for
the paper. The Immediate prerequisites column lists every recorded incoming
edge. Every prerequisite must occur in an earlier layer. A double dash means
that the row is an irreducible definition, imported theorem, or starting
input. Rows in one layer have no edge between them, except that Proposition
5.1 and (5.1) are two labels for the same assertion.

No source step may be begun because it appears next in the paper. A qualified
existing declaration is evidence only: it never erases an open source
prerequisite or authorizes skipping a row. The Section 3 lower-bound and
Section 5 upper-bound streams may run concurrently only after their shared
prerequisites are closed.

Complete means a mathematically source-faithful item has a closed Lean proof.
Benign representation choices and degenerate boundary conventions are stated
in the evidence column but do not downgrade a completed mathematical step.
`complete with qualification` is reserved for an unremedied material mismatch
and is not a source milestone. The audit at 2026-09-01T15:15:49-04:00 found
no such mismatch in a row marked complete: the only nonliteral source display
is the documented missing radial Jacobian in Section 5, for which the Lean
development proves the mathematically necessary corrected operator identity.
In progress means the currently available source-level target. Not started
means no faithful proof of that source item has begun. The initial audit timestamp was
2026-09-01T07:29:09-04:00. Timestamps change only when a row status changes.
Rows added by the first strict-DAG audit are timestamped
2026-09-01T09:57:45-04:00; rows added or split by the later direct-edge audit
are timestamped 2026-09-01T10:39:59-04:00.

## Layer 0 -- irreducible definitions and imported inputs

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| U1.Setup (unnumbered): annular cutoff $P_j$, $s_p$, and a $2^{-j}$-discretization $E_j$ | -- | complete | 2026-09-01T15:15:49-04:00 | `BRRSAnnularCutoff`, `dyadicTimeScale`, and the literal `IsMaximalSeparatedSubset` / `IsDyadicDiscretization` predicates implement the source setup. |
| (1.4): definition of the Legendre--Assouad function $\nu_E^\sharp$ | -- | complete | 2026-09-01T15:15:49-04:00 | `brrsLegendreAssouadFunction`, `brrsLegendreAssouadProfile`, `brrsEntropyNumber`, and `brrsInterval` encode the finite-scale expression. The formal empty-set totalization is an explicitly harmless degenerate convention; all nonempty bounded sets have the literal source expression. |
| U2.S (unnumbered): Assouad-spectrum and $\varphi(\delta,\theta)$ starting data | -- | complete | 2026-09-01T15:15:49-04:00 | `brrsAssouadScaleCoveringNumber`, `brrsAssouadWeightedEntropy`, and `brrsAssouadPhi` give the equality-scale objects. `brrsAssouadPhi_limsup_eq_brrsAssouadSpectrum` proves $\limsup_{\delta\to0^+}\varphi(\delta,\theta)=\gamma_E(\theta)$ on the source domain $0\le\theta<1$; the formal nonempty convention is degenerate only. |
| (1.7): Legendre-transform convention | -- | complete | 2026-09-01T15:15:49-04:00 | `brrsAssouadLegendreTransform` is exactly the source instance on $[0,1]$. |
| U1.$\infty$ (unnumbered): fixed-time annular $p=\infty$ endpoint used for interpolation | -- | complete | 2026-09-01T15:15:49-04:00 | `exists_brrs_dyadicHalfWave_fixedTimeLInfinity_bound_dim_ge_three` and `exists_brrs_planarDyadicHalfWave_fixedTimeLInfinity_top_bound` establish the auxiliary endpoint used after Proposition 5.1; it is not mislabeled as the finite-$p$ source equation (1.1). |
| U2.R (unnumbered external input): Rutar spectrum realization | -- | complete | 2026-09-01T15:15:49-04:00 | `brrsRutarCorollaryB` is now proved by `hasBRRSSpectrumRealization_of_rutar` via the exact-hit binary Moran construction. |
| U2.Comp (unnumbered imported input): sequential compactness of $[0,1]$ | -- | complete | 2026-09-01T15:15:49-04:00 | Mathlib supplies compactness/subsequence extraction; the source-specialized extraction is closed in U2.K. |
| U3.R (unnumbered): radial Fourier inversion before (3.3) and (3.4) | -- | complete | 2026-09-01T15:15:49-04:00 | `RadialFourierTransform.fourierInv_radial_eq_sphereFourier_integral` and `SurfaceMeasureDecay.fourierInv_radial_eq_surfaceFourier_integral` give the exact polar/surface-Fourier forms in the repository normalization. |
| (3.3): Bessel asymptotic with $O(|u|^{-3/2})$ remainder | -- | in progress | 2026-09-01T16:11:44-04:00 | `exists_brrs_surfaceFourier_threeWave_leading_remainder_all_dimensions` gives the all-parity surface-Fourier outgoing/incoming/middle decomposition, endpoint leading terms, and one-full-order relative remainder in the repository's $2\pi$ normalization. The source audit confirmed that this is a sound $d\ge2$ stationary replacement, but not the literal paper display: a proved bridge from ordinary $J_{(d-2)/2}$ in the paper convention to the repository's normalized `surfaceFourier`/radial factor, and the explicit two-wave phase packaging, remain necessary. |
| U5.$\kappa$-def (unnumbered): definition of the local-counting coefficient $\kappa_{j,m}$ | -- | complete | 2026-09-01T15:15:49-04:00 | The finite-dyadic local-counting expression is represented by `brrsDyadicKappa`; its entropy consequence is recorded separately below. |

## Layer 1 -- first consequences of the root data

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (1.8): Assouad-spectrum potential $\nu_E(\theta)$ | U2.S | complete | 2026-09-01T15:15:49-04:00 | `brrsAssouadSpectrum` and `brrsAssouadPotential` encode the potential. Its $θ=1$ value is a harmless totalization: the source expression uses $θ<1$ and the weighted term vanishes at the endpoint. |
| U2.C (unnumbered): continuity and compact maximum for the spectrum expression | U2.S | complete | 2026-09-01T15:15:49-04:00 | `exists_brrsAssouadSpectrum_affine_maximizer` proves the compact maximum required for (2.2), using continuity of the weighted spectrum and compactness. The singular equality-scale $\varphi$ is never asserted at $θ=1$. |
| U2.Q (unnumbered): quasi-Assouad limit and domination | U2.S | not started | 2026-09-01T09:57:45-04:00 | This is $\gamma=\lim_{\theta\to1-}\gamma_E(\theta)$ and $\gamma_E(\theta)\leq\gamma$. brrsAssouadSpectrum_le_quasiAssouadDimension supplies only one formal comparison. |
| U2.L (unnumbered): decreasing limsup-realizing sequence $\delta_n$ | U2.S | complete | 2026-09-01T15:15:49-04:00 | `exists_strictAnti_brrsSectionTwo_limsup_sequence` gives positive strictly decreasing $\delta_n\to0$ whose finite-scale envelope values converge to its `Filter.limsup`. `brrsSectionTwoFiniteScaleEnvelope` is the (2.1) supremum; the $θ=1$ totalization is outside the source's singular $φ domain. |
| U2.D (unnumbered): restricted-convex-duality setup $\nu=\tau^*$ for Theorem 1.2(ii) | (1.7) | complete | 2026-09-01T15:15:49-04:00 | `brrsProfileConjugate` is the source restricted conjugate $\tau^*$ over $[0,\infty)$. |
| U3.P (unnumbered): the $I'$, $t_I$, $g_I$, $J_t$, and $D_t$ packet/separated-time geometry | U1.Setup | complete | 2026-09-01T15:15:49-04:00 | `exists_brrsSectionThree_packet_geometry` supplies the half interval, opposite endpoint, comparable subpacket, and pairwise-disjoint regions. Its reflected-endpoint alternative is the source's harmless WLOG symmetry. |
| U5.$\kappa$-ent (unnumbered): entropy control of $\kappa_{j,m}$ | U1.Setup, (1.4), U5.$\kappa$-def | complete | 2026-09-01T15:15:49-04:00 | `brrsDyadicKappa_le_profile_of_isDyadicDiscretization` and `exists_tail_brrsDyadicKappa_le_inv_rpow_of_lt` give the finite-dyadic entropy estimate used only in (5.1). |
| U5.C (unnumbered): discretization cardinality and $\kappa$ comparisons | U1.Setup, U5.$\kappa$-def | complete | 2026-09-01T15:15:49-04:00 | `brrsEntropyNumber_le_card_at_twice_scale`, `dyadicDiscretization_card_le_brrsEntropyNumber_half_scale`, and the terminal $\kappa$ lemmas give the required finite-net bounds. The half/double mesh constants are the harmless closed-ball normalization behind the source's $\asymp$. |
| U5.E (unnumbered): cited exterior fixed-time radial estimate | U1.Setup | in progress | 2026-09-01T17:17:27-04:00 | `brrsExteriorWeightedFourPhaseBlock_rpow_le` now proves the exact one-dimensional Young core for all four literal exterior phases, retaining the factor $(s/r)^\sigma$ and reducing it to an absorbed weighted $L^1$ phase kernel. This is not an exterior half-wave theorem: the remaining source-faithful work is to prove the absorbed rapid-kernel $L^1$ hypotheses and connect the actual corrected radial half-wave kernel in every radial region to this block. |
| U5.R (unnumbered): radial kernel representation and power-weight conjugation for (5.3) to (5.4) | U1.Setup, U3.R | complete | 2026-09-01T15:15:49-04:00 | `brrsDyadicHalfWave_eq_radialBesselKernel_integral_of_norm`, the scalar-kernel identity, and power conjugation prove the mathematically necessary radial representation. The arXiv/published $K_j$ display omits the forced $\rho\,d\rho$ (equivalently $\lambda\,d\lambda$) Jacobian; Lean formalizes the corrected operator identity, which is the only formula compatible with radial Fourier composition. |

## Layer 2 -- first source choices and kernel inputs

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| U2.Neg (unnumbered): $\alpha\leq0$ branch of Theorem 1.2(i) | (1.4), (1.7), (1.8) | complete | 2026-09-01T15:15:49-04:00 | `brrsLegendreAssouadFunction_eq_zero_of_nonpos` and the all-real transform theorem give the nonpositive-parameter branch; only the harmless empty-set convention is excluded. |
| (2.2): maximizing $\theta_\alpha$ for the lower half of (2.1) | (1.8), U2.C | complete | 2026-09-01T15:15:49-04:00 | `exists_brrsSectionTwo_lower_half_maximizer` selects the affine maximizer and proves the required lower comparison. The $\theta=1$ branch is handled separately because the displayed $\varphi$ is singular there. |
| (2.3): $\varepsilon$-maximizing $\theta_n$ selection | U2.L | complete | 2026-09-01T15:15:49-04:00 | `exists_strictAnti_brrsSectionTwo_limsup_sequence_with_approximate_maximizers` gives the source $\varepsilon$-maximizers along a strictly decreasing limsup-realizing scale sequence. |
| (2.7): $\gamma(\theta)=-\nu(\theta)/(1-\theta)$ candidate construction | U2.D | complete | 2026-09-01T15:15:49-04:00 | `brrsProfileSpectrumCandidate` is the source formula on $(0,1)$; its range, monotonicity, and weighted-potential hypotheses are proved by `brrsProfileSpectrumCandidate_nonneg`, `_le_one`, `_mono`, and `brrsProfileConjugate_mono`. |
| U5.K (unnumbered): four-sign Bessel/two-radius kernel majorant and rapid $\omega_j$ decay | U5.R | complete | 2026-09-01T15:15:49-04:00 | `brrsRadialBesselKernel_eq_levelZero_scaled`, `brrsSectionFiveOmega_le_sourceRapidDecay`, and `exists_norm_brrsRadialBesselKernel_fourPhase_region_majorants` give the all-region four-sign majorant for the corrected radial operator. Its compiled `exists_norm_brrsRadialBesselKernel_fourPhase_highSource_halfDensity_majorant` consequence gives the exact global high-source form used later in the compact kernel-to-one-dimensional reduction. |

## Layer 3 -- first analytic consequences

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| U2.K (unnumbered): convergent subsequence $\theta_n\to\theta_*$ | (2.3), U2.Comp | complete | 2026-09-01T15:15:49-04:00 | `exists_strictAnti_brrsSectionTwo_limsup_sequence_with_convergent_approximate_maximizers` applies compactness and retains the exact source sequence data. |
| U2.A (unnumbered): verification that the (2.7) candidate meets Rutar's hypotheses | U2.D, (2.7) | complete | 2026-09-01T15:15:49-04:00 | `brrsProfileSpectrumCandidate_isRutarAssouadSpectrum` proves the exact range and monotonicity conditions checked after (2.7). |
| (3.2): $\lVert g_I\rVert_p$ packet-norm upper bound | U3.R, U3.P, (3.3) | not started | 2026-09-01T07:56:08-04:00 | Requires the literal radial/Bessel input for its $L^\infty$ bound and the specified packet. |
| (3.4): $T_t^-+T_t^++T_t^{\mathrm{rem}}$ decomposition | U3.R, U3.P, (3.3) | not started | 2026-09-01T07:29:09-04:00 | Independent of (3.2), but requires radial inversion and the Bessel asymptotic. |
| (5.5): far-source $\mathrm{II}_n$ tail summation | U5.C, U5.K | complete | 2026-09-01T18:03:06-04:00 | `tsum_brrsSectionFiveFarSourceII_le_geometric_fullRange` proves the literal one-sign source contribution `brrsSectionFiveFarSourceII` for every selected sign, throughout the printed range $1\leq p<2d/(d-1)$. It combines the strict-Hölder $1<p<2$, direct $p=1$, and $p\ge2$ branches, sums $n=10+k$, and gives a finite constant depending only on $d,p,L$ times the exact factor $2^{-Lj}\int |f_0|^p$. The four values of `BRRSSectionFiveFarSourcePhase` establish all source sign choices separately; no four-phase block is identified with $\mathrm{II}_n$. The formal profile is the standard zero extension of the paper's nonnegative radial profile from $(0,\infty)$; the half-open annuli/endpoints are Lebesgue-null conventions. The actual-kernel constant and $4^{p-1}$ convexity factor belong later to the separate reduction from (5.3) to (5.4). |
| (5.6): terminal $\mathrm{I}_j$ estimate | U5.C, U5.K | not started | 2026-09-01T07:29:09-04:00 | Requires the four-sign kernel, cardinality comparison, and Young's inequality in the weighted reduction. |
| (5.7): initial-cell $\mathrm{I}_0$ estimate | (1.4), U5.C, U5.K | not started | 2026-09-01T07:29:09-04:00 | Its printed conclusion is $2^{j\nu_E^\sharp(ps_p)}$. It uses local packing and $ps_p\leq\nu_E^\sharp(ps_p)$, not U5.$\kappa$-ent merely to prove that displayed inequality. |
| U5.M (unnumbered): $0<m<j$ intermediate-cell estimate | U5.$\kappa$-def, U5.K | complete | 2026-09-01T15:15:49-04:00 | `brrsSectionFiveIntermediateCell_fourPhase_le` proves the strict four-sign interval-cell bound via rapid majorization, fivefold overlap, and Young; `brrsSectionFiveIntermediateCell_sourceWeight_fourPhase_le` specializes the literal outer weight $r^{-ps_p}$. ENNReal is only the positive-$|f_0|$ implementation of the source norm estimate. |

## Layer 4 -- joins internal to the Section 2, 3, and 5 branches

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| U2.R-app (unnumbered): apply Rutar to the verified candidate | U2.R, U2.A | complete | 2026-09-01T15:15:49-04:00 | `brrsRutarCorollaryB` applied to `brrsProfileSpectrumCandidate_isRutarAssouadSpectrum` is the source realization step following (2.7). |
| (2.4): left-limit spectrum comparison | U2.C, U2.K | complete | 2026-09-01T15:15:49-04:00 | `exists_brrsSectionTwo_left_weighted_approximation` proves the displayed comparison. At $\theta_*=0$ it supplies the necessary degenerate branch $\theta_*^-=0$; the source's strict-left phrase has no inhabitant in that boundary case, so this repairs rather than weakens the theorem argument. |
| (3.5): main-term lower bound on $D_t$ | U3.P, (3.4) | not started | 2026-09-01T07:29:09-04:00 | Requires the $T_t^-$ term and specified annular geometry. |
| (3.6): $T_t^+$ error estimate | U3.P, (3.4) | not started | 2026-09-01T07:29:09-04:00 | Requires the $T_t^+$ term and integration-by-parts decay. |
| (3.7): remainder error estimate | U3.P, (3.4) | not started | 2026-09-01T07:29:09-04:00 | Requires the remainder term and annular integral bound. |
| (5.8): sum of the $\mathrm{I}_m$ estimates | U5.C, U5.M, (5.6), (5.7) | not started | 2026-09-01T07:29:09-04:00 | The base-scale/cardinality edge converts endpoint cells to the $\kappa_{j,m}$ sum. |

## Layer 5 -- late source estimates inside the three branches

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.5): eventual comparison of $\theta_n$ and $\theta_*$ | U2.K, (2.4) | complete | 2026-09-01T15:15:49-04:00 | `eventually_brrsSectionTwo_parameter_tail_estimates` proves the eventual pair $\theta_n\geq\theta_*^-$ and $\theta_n\alpha\leq\theta_*\alpha+\varepsilon$; the $\theta_*=0$ case uses the repaired degenerate branch from (2.4). |
| (3.1): localized lower bound | (3.2), (3.4), (3.5), (3.6), (3.7) | not started | 2026-09-01T07:29:09-04:00 | Joins the three-term decomposition, packet norm, and main/error estimates. It does not use entropy to become sharp. |
| (5.4): weighted one-dimensional estimate | (5.5), (5.8) | not started | 2026-09-01T07:29:09-04:00 | The join of the far-source tail and full near-source sum. |

## Layer 6 -- reductions immediately before main displayed bounds

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.6): covering-number estimate at $\theta_*^-$ | U2.S, (2.5) | complete | 2026-09-01T15:15:49-04:00 | `brrsAssouadScaleCoveringNumber_antitone_parameter` and `exists_brrsSectionTwo_covering_tail_of_parameter_tail` prove the power-scale inclusion and the source $\varepsilon/(1-\theta_*^-)$ cover estimate. The repaired $\theta_*=0$ branch has $\theta_*^-=0<1$. |
| U3.S (unnumbered): conversion of (3.1) to sharpness of (1.5) up to $\varepsilon$ | U1.Setup, (1.4), (3.1) | not started | 2026-09-01T09:57:45-04:00 | This is the entropy/limsup extraction after (3.1), not part of the proof of (3.1). |
| (5.3): compact spatial-region reduction | U5.R, U5.K, (5.4) | not started | 2026-09-01T07:29:09-04:00 | Radial inversion, the four-sign majorant, and (5.4) reduce the compact spatial integral. It does not use U5.E. |

## Layer 7 -- the two numbered main bounds

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.1): entropy/spectrum supremum identity for $\alpha\geq0$ | (2.2), (2.3), (2.4), (2.5), (2.6) | complete | 2026-09-01T15:15:49-04:00 | `brrsLegendreAssouadFunction_eq_brrsAssouadLegendreTransform_of_nonempty_of_nonneg` closes the identity; the displayed source substeps (2.2)--(2.6) are now separately closed. The nonempty convention is the accepted degenerate edge convention. |
| (5.2): $\kappa_{j,m}$ dyadic reduction | U5.E, U5.C, (5.3) | not started | 2026-09-01T07:29:09-04:00 | Joins the exterior estimate, the cardinality comparison, and the compact reduction; the entropy consequence is used only afterward in (5.1). |

## Layer 8 -- first named theorem/proposition conclusions

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| Theorem 1.2(i): $\nu_E^\sharp=\nu_E^*$ | U2.Neg, (2.1) | complete | 2026-09-01T15:15:49-04:00 | `brrsTheoremOnePointTwoPartOne` proves the identity for bounded nonempty sets; this is the accepted harmless empty-set convention of the project. |
| (5.1): Proposition 5.1 bound | U5.$\kappa$-ent, (5.2) | not started | 2026-09-01T07:29:09-04:00 | The same assertion as the named proposition; the last entropy-to-$\varepsilon$ reduction is the U5.$\kappa$-ent edge. |
| Proposition 5.1 | U5.$\kappa$-ent, (5.2) | not started | 2026-09-01T07:56:08-04:00 | Same assertion as (5.1), retained as a separate label with no proof-dependency edge between the two rows. |

## Layer 9 -- Theorem 1.2 consequences and realization

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.8): Assouad-spectrum Legendre representation | Theorem 1.2(i) | complete | 2026-09-01T15:15:49-04:00 | `brrsLegendreAssouadFunction_eq_brrsAssouadLegendreTransform_of_nonempty` gives the source representation, subject only to the accepted empty-set convention. |
| Theorem 1.2(ii): characterization of possible profiles | Theorem 1.2(i), U2.D, (2.7), U2.A, U2.R-app | complete | 2026-09-01T15:15:49-04:00 | `brrsTheoremOnePointTwoPartTwo` proves both directions unconditionally: the converse uses `brrsRutarCorollaryB` and the exact (2.7) candidate; the forward direction derives increasingness, convexity, and the identity tail from (i). |

## Layer 10 -- quasi-Assouad identity tail

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (1.9): $\nu_E^\sharp(\alpha)=\alpha$ for $\alpha\geq\dim_{qA}E$ | U2.Q, (2.8) | complete | 2026-09-01T15:15:49-04:00 | `brrsLegendreAssouadFunction_eq_id_of_nonempty_of_quasiAssouadDimension_le` establishes the identity-tail ingredient, subject only to the accepted empty-set convention. |

## Layer 11 -- independent uses of the identity tail and Proposition 5.1

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| Corollary 1.3: identity-tail minimality | U2.C, U2.Q, (1.9), (2.8) | not started | 2026-09-01T07:29:09-04:00 | The source maximizer/minimality argument is not packaged. |
| U1.I (unnumbered): common radial finite-time operator and high-$p$ interpolation | (1.1) at $p=\infty$, (1.9), Proposition 5.1 | not started | 2026-09-01T08:40:03-04:00 | Finite-time Riesz--Thorin transport exists, but the radial-profile density/output-continuity bridge for the actual high-$p$ range does not. |

## Layer 12 -- radial upper estimate

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (1.5): radial upper estimate in Theorem 1.1 | U1.I, Proposition 5.1 | not started | 2026-09-01T09:12:03-04:00 | Joins the subcritical Proposition 5.1 range with high-$p$ interpolation. It is only the displayed upper bound. |

## Layer 13 -- final theorem assembly

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| Theorem 1.1: full radial upper bound and sharpness package | U3.S, (1.5) | not started | 2026-09-01T07:29:09-04:00 | Joins the upper estimate with the separate entropy-to-sharpness conclusion. It does not require Corollary 1.3. Only brrsTheoremOneWithSharpnessStatement_p_two is currently proved. |

## Verification and maintenance

At 2026-09-01T07:46:11-04:00, both lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean and lake build LeanSpherical.Auto.Spherical.FractalDilations.BRRS passed after deletion of disconnected bridge tails. A direct lake env lean LeanSpherical.lean check is blocked before source checking by the absent, unrelated build-cache artifact RSUpperBounds.olean; it does not reference a removed BRRS declaration. A literal sorry/admit/axiom audit of the authorized BRRS modules found no such declaration.

At 2026-09-01T08:13:28-04:00, a fresh direct BRRS compilation after removal of the additionally confirmed disconnected exterior/packet/translation tail reached the two deliberately in-progress developments and therefore did not close. At 2026-09-01T08:49:46-04:00, a fresh root-level direct check verified the repaired lower normalized-base derivative proof, then stopped in active U5.K middle-component assembly.

At 2026-09-01T09:04:41-04:00, a fresh root-level direct BRRS check passed with warnings only. It verified the then-compiling U5.K higher-dimensional assembly and (3.3) carrier helpers, but neither source item advanced. The strict-DAG audit at 2026-09-01T09:57:45-04:00 reclassified U5.K as not source-level active until U5.R is closed, and added the missing U1/U2/U3/U5 prerequisite nodes and edges.

At 2026-09-01T10:39:59-04:00, a fresh direct lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean check completed with warnings only after the local Fresnel-limit normalization repair. The subsequent dependency audit split the definition of $\kappa_{j,m}$ from its entropy consequence and corrected every recorded direct edge; no prerequisite now appears in a later layer.

At 2026-09-01T13:50:00-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean` check passed after the corrected coordinate-free radial-kernel identity was added. The source's printed $K_j$ display omits the forced radial frequency Jacobian; the exact corrected formula is available for the ensuing kernel-majorant proof.

At 2026-09-01T15:15:49-04:00, a source-faithfulness audit reconciled every previously qualified completed row with its declaration and the arXiv v1 proof. The ledger now reserves a qualification only for an unremedied material mismatch. The completed (2.7) candidate/Rutar construction and Theorem 1.2(ii) were corrected from stale status prose; the Section 5 radial formula is documented as a source-display correction, while empty-set and $\theta_*=0$ cases are explicit harmless degenerate conventions.

At 2026-09-01T15:29:48-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean` check completed with zero errors after the audit and the current concurrent Section 3/Section 5 work. No source row advanced from that build alone.

At 2026-09-01T16:05:42-04:00, an independent declaration-level audit of the
completed Section 2 chain confirmed that Theorem 1.2(i), the literal (2.7)
candidate, its Rutar-hypothesis verification and realization, and Theorem
1.2(ii) have closed proofs using only `propext`, `Classical.choice`, and
`Quot.sound`.  It found no material weakening or conditional bridge.  The
recorded empty-set, singular-endpoint, and covering-normalization details are
harmless conventions or forced source-proof repairs, not qualifications of
the intended theorem.

At 2026-09-01T14:06:37-04:00, fresh direct checks of `lake env lean LeanSpherical/Auto/Spherical/LegendreAssouad.lean` and `lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean` both exited successfully with warnings only. The former verifies the closed literal fixed-$\theta$ $\varphi$ limsup identity recorded in U2.S; the latter includes the currently active lower-bound and kernel work.

At 2026-09-01T14:10:25-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/LegendreAssouad.lean` check exited successfully with warnings only after the Section 2 affine maximizer was added. This closes U2.C in the endpoint-qualified form stated above.

At 2026-09-01T14:19:26-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/LegendreAssouad.lean` check exited successfully with warnings only after the source-specific strictly decreasing limsup-realizing scale sequence was added. This verifies U2.L.

At 2026-09-01T14:25:01-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean` check reported no errors after the terminal entropy-to-$\kappa$ comparison was added. This verifies the closed-ball-qualified finite-net package recorded in U5.C.

At 2026-09-01T14:26:17-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/LegendreAssouad.lean` check exited successfully with pre-existing warnings only after the source lower-half maximizer theorem was added. This verifies (2.2) in the qualified form recorded above.

At 2026-09-01T14:43:39-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/LegendreAssouad.lean` check reported no errors after the finite-envelope estimate and shifted exact $\varepsilon$-maximizer sequence were added. This verifies source step (2.3) in the nonempty-set, weighted-endpoint form recorded above.

At 2026-09-01T14:47:35-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/LegendreAssouad.lean` check exited successfully with warnings only after the source-specific compact subsequence theorem was added. This verifies U2.K in the qualified form recorded above.

At 2026-09-01T14:48:59-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean` check reported no errors and `git diff --check` passed. This independently verifies the completed U5.K actual-kernel, four-sign, all-region rapid-$\omega_j$ package recorded above.

At 2026-09-01T14:51:51-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean` check reported no errors after the exact Section 3 half-interval and closed-shell geometry was added. A separate fresh direct `LegendreAssouad.lean` check reported no errors after the source (2.4) left-limit theorem was added. `git diff --check` passed for the shared worktree.

At 2026-09-01T14:56:24-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/LegendreAssouad.lean` check exited successfully with warnings only after the eventual source comparison in (2.5) was added. This verifies the qualified boundary-aware form recorded above.

At 2026-09-01T15:01:06-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean` check reported no errors after the source-weighted strict-intermediate-cell proof was integrated, and the two concurrent unrelated parser/name failures were repaired. This verifies U5.M in the qualified ENNReal/source-normalization form recorded above.

At 2026-09-01T15:02:00-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/LegendreAssouad.lean` check exited successfully after the literal parameter-to-covering tail proof for (2.6) was integrated. `git diff --check` passed for the changed source module.

At 2026-09-01T17:17:27-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean` check exited successfully with warnings only, and `git diff --check` passed. It verifies the new exterior one-dimensional Young core recorded as active U5.E and the scalar `Summable`/`tsum` developments recorded in the evidence for the still-in-progress source step (5.5); neither is being reported as a completed source theorem.

At 2026-09-01T18:03:06-04:00, a fresh direct `lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean` check exited successfully with no errors, and `git diff --check` passed. This verifies the full printed-exponent, literal-one-sign far-source tail theorem recorded for (5.5).
