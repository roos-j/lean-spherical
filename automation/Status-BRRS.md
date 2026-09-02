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
| U5.E (unnumbered): cited exterior fixed-time radial estimate | U1.Setup | complete | 2026-09-02T01:34:07-04:00 | `brrsSectionFiveExteriorSpatial_le` proves the exterior fixed-time estimate: for a sampled time in $[1,2]$, a radial Schwartz input and $d\geq2$, $p\geq2$, the exterior spatial contribution $\int_{\|x\|>20}|A_j^tf|^p$ is at most an explicit finite constant times the absorbed-kernel Young constant times $\int|f_0|^p$, for the radial profile $f_0(s)=s^{(d-1)/p}|f(sw)|$. It composes the exterior polar reduction `brrs_lintegral_closedBallCompl_brrsDyadicHalfWave_eq`, the half-density majorant (the same one used in (5.3), through `brrs_radial_cell_pointwise_halfDensity`), the weight identity `brrsSectionFiveSourceWeight_mul_oneDimSource_rpow_eq` which turns the outer weight $r^{-ps_p}$ and the inner weight $s^{s_p}$ into the exterior ratio weight $(s/r)^{s_p}$, the four-phase split `brrs_exterior_integrand_rpow_le`, the inclusion of the exterior radial range in the Young core range, and the core `brrsExteriorWeightedFourPhaseBlock_rpow_le` with its absorbed-kernel hypotheses discharged for the actual phase-line kernel (`brrsExteriorAbsorbedKernel_sectionFiveOmega_*`, valid once the decay order exceeds $s_p$ by three). |
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
| (5.5): far-source $\mathrm{II}_n$ tail summation | U5.C, U5.K | complete | 2026-09-01T18:39:00-04:00 | `tsum_brrsSectionFiveFarSourceII_le_geometric_fullRange` proves the literal one-sign source contribution `brrsSectionFiveFarSourceII` for every selected sign, throughout the printed range $1\leq p<2d/(d-1)$. It combines the strict-Hölder $1<p<2$, direct $p=1$, and $p\ge2$ branches, sums $n=10+k$, and gives a finite constant depending only on $d,p,L$ times the exact factor $2^{-Lj}\int |f_0|^p$. The four values of `BRRSSectionFiveFarSourcePhase` establish all source sign choices separately; no four-phase block is identified with $\mathrm{II}_n$. The formal profile is the standard zero extension of the paper's nonnegative radial profile from $(0,\infty)$; the half-open annuli/endpoints are Lebesgue-null conventions. The actual-kernel constant and $4^{p-1}$ convexity factor belong later to the separate reduction from (5.3) to (5.4). |
| (5.6): terminal $\mathrm{I}_j$ estimate | U5.C, U5.K | complete | 2026-09-01T18:41:07-04:00 | `brrsSectionFiveTerminalCell_kappa_fourPhase_le` proves the literal terminal cell for $d\geq2$ and $p\geq2$: the four travelling phase lines $t\pm r\mp s$ over the terminal radial range are bounded by $4\,\kappa_{j,j}(ps_p)$ times a fixed $j$-independent constant times $\int|f_0|^p$. It composes `brrsSectionFiveTerminalCell_sourceWeight_fourPhase_le` -- which retains the source truncation $0\leq s\leq 2^{10}$ (`brrsSectionFiveTerminalSourceProfile`), bounds the polar weight by one on the terminal interval (`brrsSectionFiveTerminalWeight_le_one`), dominates $\omega_j$ by the normalized cubic majorant, and applies one-dimensional Young to each sign (`brrsSectionFiveTerminalFourPhaseBlock_le_card_mul`) -- with the endpoint cardinality comparison `dyadicDiscretization_card_le_brrsDyadicKappa_terminal`, which is the U5.C edge $\#T\leq\kappa_{j,j}$ at counting radius one. The explicit constant is the cubic-majorant mass; no $\kappa$-free `T.card` form is reported as the source step. |
| (5.7): initial-cell $\mathrm{I}_0$ estimate | (1.4), U5.C, U5.K | complete | 2026-09-01T18:57:41-04:00 | `brrsSectionFiveInitialCell_sourceWeight_fourPhase_le` proves the printed conclusion: for $d\geq2$, $p\geq2$, nonempty $E$ and a $2^{-j}$-discretization $T$, the four travelling phase lines over the initial annulus $[2^{-j},2^{-j+1}]$ carrying the literal outer weight $r^{-ps_p}$ are at most $56\cdot 2^{j\nu_E^\sharp(ps_p)}$ times a fixed $j$-independent constant times $\int|f_0|^p$. The two displayed ingredients are proved separately and used exactly as printed: local packing (`brrsKappa_le_two_mul_rpow_of_isSeparated`, `brrsDyadicKappa_zero_le_two_mul_two_rpow`) gives $\kappa_{j,0}(ps_p)\leq 2\cdot2^{jps_p}$ at the mesh counting radius, and `two_rpow_mul_le_two_rpow_mul_brrsLegendreAssouadFunction` supplies $ps_p\leq\nu_E^\sharp(ps_p)$ from `le_brrsLegendreAssouadFunction_of_nonempty`. No entropy tail (U5.$\kappa$-ent) is used. |
| U5.M (unnumbered): $0<m<j$ intermediate-cell estimate | U5.$\kappa$-def, U5.K | complete | 2026-09-01T15:15:49-04:00 | `brrsSectionFiveIntermediateCell_fourPhase_le` proves the strict four-sign interval-cell bound via rapid majorization, fivefold overlap, and Young; `brrsSectionFiveIntermediateCell_sourceWeight_fourPhase_le` specializes the literal outer weight $r^{-ps_p}$. ENNReal is only the positive-$|f_0|$ implementation of the source norm estimate. |

## Layer 4 -- joins internal to the Section 2, 3, and 5 branches

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| U2.R-app (unnumbered): apply Rutar to the verified candidate | U2.R, U2.A | complete | 2026-09-01T15:15:49-04:00 | `brrsRutarCorollaryB` applied to `brrsProfileSpectrumCandidate_isRutarAssouadSpectrum` is the source realization step following (2.7). |
| (2.4): left-limit spectrum comparison | U2.C, U2.K | complete | 2026-09-01T15:15:49-04:00 | `exists_brrsSectionTwo_left_weighted_approximation` proves the displayed comparison. At $\theta_*=0$ it supplies the necessary degenerate branch $\theta_*^-=0$; the source's strict-left phrase has no inhabitant in that boundary case, so this repairs rather than weakens the theorem argument. |
| (3.5): main-term lower bound on $D_t$ | U3.P, (3.4) | not started | 2026-09-01T07:29:09-04:00 | Requires the $T_t^-$ term and specified annular geometry. |
| (3.6): $T_t^+$ error estimate | U3.P, (3.4) | not started | 2026-09-01T07:29:09-04:00 | Requires the $T_t^+$ term and integration-by-parts decay. |
| (3.7): remainder error estimate | U3.P, (3.4) | not started | 2026-09-01T07:29:09-04:00 | Requires the remainder term and annular integral bound. |
| (5.8): sum of the $\mathrm{I}_m$ estimates | U5.C, U5.M, (5.6), (5.7) | complete | 2026-09-01T20:34:12-04:00 | `brrsSectionFiveNearSourceCellSum_le_kappa_sum` adds the individual cell estimates. The aggregate `brrsSectionFiveNearSourceCellSum` is the innermost cell $0\leq r\leq2^{-j}$ (with its polar weight `brrsSectionFiveInnerWeight`), the dyadic cells $2^{m-j}\leq r\leq2^{m-j+1}$ for $0\leq m<j$, and the terminal cell; together these exhaust the compact radial range. The bound is $56\big(\sum_{m=0}^{j}\kappa_{j,m}(ps_p)\big)$ times a fixed $j$-independent constant and $\int|f_0|^p$. Per-cell inputs: `brrsSectionFiveCell_kappa_le` (U5.M for $0<m<j$, the first half of (5.7) at $m=0$), `brrsSectionFiveTerminalCell_kappa_fourPhase_le` for (5.6) with the base-scale cardinality edge, and `brrsSectionFiveInnerCell_kappa_le` for the innermost cell, whose block estimate (`brrs_sum_innerCell_add_weighted_profile_rpow_le`, `brrs_sum_innerCell_sub_weighted_profile_rpow_le`) is the translated main-cell estimate, so no new overlap geometry and no change of counting radius is involved. `brrsSectionFiveNearSourceCellSum_le_initialEntropy_add_kappa_tail` records the equivalent printed display with the $m=0$ term shown as $2\cdot2^{j\nu_E^\sharp(ps_p)}$ via (5.7). No entropy hypothesis on $E$ is used at this step. |

## Layer 5 -- late source estimates inside the three branches

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.5): eventual comparison of $\theta_n$ and $\theta_*$ | U2.K, (2.4) | complete | 2026-09-01T15:15:49-04:00 | `eventually_brrsSectionTwo_parameter_tail_estimates` proves the eventual pair $\theta_n\geq\theta_*^-$ and $\theta_n\alpha\leq\theta_*\alpha+\varepsilon$; the $\theta_*=0$ case uses the repaired degenerate branch from (2.4). |
| (3.1): localized lower bound | (3.2), (3.4), (3.5), (3.6), (3.7) | not started | 2026-09-01T07:29:09-04:00 | Joins the three-term decomposition, packet norm, and main/error estimates. It does not use entropy to become sharp. |
| (5.4): weighted one-dimensional estimate | (5.5), (5.8) | complete | 2026-09-01T21:47:05-04:00 | `brrsSectionFiveWeightedOneDim_le` joins the two inputs on the printed range $2\leq p<2d/(d-1)$. The aggregate `brrsSectionFiveWeightedOneDimTotal` is the full near-source radial cell sum of (5.8) (covering $0\leq r\leq20$) plus the four literal far-source sign contributions `brrsSectionFiveFarSourceTotal` over the whole far range $s>2^{10}$. It is at most $56\big(\sum_{m=0}^{j}\kappa_{j,m}(ps_p)\big)C^p\int|f_0|^p$ from (5.8) plus $4\,C_{\mathrm{far}}(d,L,j,p)\int|f_0|^p$, where `brrsSectionFiveFarTotalConstant` carries the exact gain $2^{-Lj}$ and its finiteness is part of the conclusion. The far input is the aggregate form of (5.5): the per-annulus Hölder step of (5.5) is applied pointwise in $(t,r)$ and the annuli are summed by the scalar geometric series `tsum_brrsSectionFiveFarAnnulusPointwiseCoefficient_rpow_le`, which is the Lean rendering of the source's triangle inequality in $L^p$; the earlier sum-of-$p$-th-powers form did not support the next step (5.3) and has been replaced. |

## Layer 6 -- reductions immediately before main displayed bounds

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.6): covering-number estimate at $\theta_*^-$ | U2.S, (2.5) | complete | 2026-09-01T15:15:49-04:00 | `brrsAssouadScaleCoveringNumber_antitone_parameter` and `exists_brrsSectionTwo_covering_tail_of_parameter_tail` prove the power-scale inclusion and the source $\varepsilon/(1-\theta_*^-)$ cover estimate. The repaired $\theta_*=0$ branch has $\theta_*^-=0<1$. |
| U3.S (unnumbered): conversion of (3.1) to sharpness of (1.5) up to $\varepsilon$ | U1.Setup, (1.4), (3.1) | not started | 2026-09-01T09:57:45-04:00 | This is the entropy/limsup extraction after (3.1), not part of the proof of (3.1). |
| (5.3): compact spatial-region reduction | U5.R, U5.K, (5.4) | complete | 2026-09-02T00:26:41-04:00 | `brrsSectionFiveCompactSpatial_le` proves the reduction: for $d\geq2$, $p\geq2$ and radial Schwartz input, `brrsSectionFiveCompactSpatialSum` (the sum over the sampled times of $\int_{\|x\|\leq20}|A_j^tf|^p$) is at most a finite explicit constant times `brrsSectionFiveWeightedOneDimTotal` for the radial profile $f_0(s)=s^{(d-1)/p}|f(sw)|$, which is exactly the aggregate estimated in (5.4). The proof is the source one: polar coordinates (`brrs_lintegral_closedBall_brrsDyadicHalfWave_eq`), the exact radial kernel representation U5.R with the U5.K four-sign majorants in their global forms (`exists_norm_brrsRadialBesselKernel_fourPhase_halfDensity_majorant` and `..._lowOutput_majorant`), the identification of the polar Jacobian times each majorant constant with the literal outer weight of the corresponding cell (`brrs_radial_cell_pointwise_halfDensity`, `brrs_radial_cell_pointwise_lowOutput`), the near/far source split at $s=2^{10}$ with the literal compact truncation (`brrsSectionFiveOneDimSource_le_near_add_far`), the distribution of the $p$-th power over the eight Section 5 integrands (`brrsSectionFiveOneDimSource_rpow_le`), and the two region assemblies `brrs_innerRegion_sum_le` and `brrs_outerRegion_sum_le`. The radial integral is split once at $r=2^{-j}$, which costs a single extra copy of the far-source term (`brrsSectionFiveInnerWeight_le_sourceWeight`) instead of one copy per cell. It does not use U5.E. |

## Layer 7 -- the two numbered main bounds

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.1): entropy/spectrum supremum identity for $\alpha\geq0$ | (2.2), (2.3), (2.4), (2.5), (2.6) | complete | 2026-09-01T15:15:49-04:00 | `brrsLegendreAssouadFunction_eq_brrsAssouadLegendreTransform_of_nonempty_of_nonneg` closes the identity; the displayed source substeps (2.2)--(2.6) are now separately closed. The nonempty convention is the accepted degenerate edge convention. |
| (5.2): $\kappa_{j,m}$ dyadic reduction | U5.E, U5.C, (5.3) | complete | 2026-09-02T01:57:33-04:00 | `brrsSectionFiveDyadicReduction_le` proves the full-space reduction on the printed range $2\leq p<2d/(d-1)$: there are finite constants $C_1,C_2$, independent of $E$, $j$, $T$ and $f$, with $\sum_{t\in T}\int_{\mathbb{R}^d}|A_j^tf|^p\leq C_1\big(\sum_{m=0}^{j}\kappa_{j,m}(ps_p)\big)\int|f_0|^p + C_2\,C_{\mathrm{far}}(d,L,j,p)\int|f_0|^p$, where $C_{\mathrm{far}}$ carries the gain $2^{-Lj}$. The full space is split by `lintegral_add_compl` into the compact ball and its complement; the compact part is (5.3) followed by (5.4), and the exterior part is the fixed-time estimate U5.E summed over the packet, whose cardinality is absorbed by `dyadicDiscretization_card_le_brrsDyadicKappa_terminal` (the U5.C edge $\#T\leq\kappa_{j,j}$) into the same $\kappa$ sum. The exterior constant is uniform in $j$ (`brrsSectionFiveExteriorSpatial_le_uniform`), which is what makes that absorption legitimate: the crude cubic domination of the absorbed kernel would have left a spurious factor $2^{j}$, and the scaled-cubic domination `brrsExteriorAbsorbedKernel_sectionFiveOmega_le_scaledCubic` removes it. No entropy hypothesis on $E$ is used; that enters only in (5.1). |

## Layer 8 -- first named theorem/proposition conclusions

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| Theorem 1.2(i): $\nu_E^\sharp=\nu_E^*$ | U2.Neg, (2.1) | complete | 2026-09-01T15:15:49-04:00 | `brrsTheoremOnePointTwoPartOne` proves the identity for bounded nonempty sets; this is the accepted harmless empty-set convention of the project. |
| (5.1): Proposition 5.1 bound | U5.$\kappa$-ent, (5.2) | complete | 2026-09-02T02:14:56-04:00 | `brrsPropositionFiveOne` proves the assertion: for every $q$ strictly above $\nu_E^\sharp(ps_p)$ with $q\geq0$, there are a finite constant and a threshold $J$ such that for all $j\geq J$ and every $2^{-j}$-discretization $T$ of $E\subseteq[1,2]$, and every radial Schwartz input, $\sum_{t\in T}\int_{\mathbb{R}^d}|A_j^tf|^p\leq C\,(j+1)\,2^{(j+1)q}\int|f_0|^p$ on the printed range $2\leq p<2d/(d-1)$. It feeds the entropy tail U5.$\kappa$-ent (`exists_tail_brrsDyadicKappa_le_inv_rpow_of_lt`, summed by `sum_brrsDyadicKappa_le_of_uniform_bound`) into the local counting sum of (5.2); the far-source term needs no frequency gain here and is absorbed by the same factor, so the reduction is applied at $L=0$ with exterior decay order $N=d+3$. |
| Proposition 5.1 | U5.$\kappa$-ent, (5.2) | complete | 2026-09-02T02:14:56-04:00 | `brrsPropositionFiveOne` proves the assertion: for every $q$ strictly above $\nu_E^\sharp(ps_p)$ with $q\geq0$, there are a finite constant and a threshold $J$ such that for all $j\geq J$ and every $2^{-j}$-discretization $T$ of $E\subseteq[1,2]$, and every radial Schwartz input, $\sum_{t\in T}\int_{\mathbb{R}^d}|A_j^tf|^p\leq C\,(j+1)\,2^{(j+1)q}\int|f_0|^p$ on the printed range $2\leq p<2d/(d-1)$. It feeds the entropy tail U5.$\kappa$-ent (`exists_tail_brrsDyadicKappa_le_inv_rpow_of_lt`, summed by `sum_brrsDyadicKappa_le_of_uniform_bound`) into the local counting sum of (5.2); the far-source term needs no frequency gain here and is absorbed by the same factor, so the reduction is applied at $L=0$ with exterior decay order $N=d+3$. | Same assertion as (5.1); retained as a separate label, with no proof-dependency edge between the two rows. |

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
| U1.I (unnumbered): common radial finite-time operator and high-$p$ interpolation | (1.1) at $p=\infty$, (1.9), Proposition 5.1 | in progress | 2026-09-02T02:31:14-04:00 | Available: the abstract transport `highExponent_discreteLpEstimate_of_lower_and_top` (Riesz--Thorin with rates $2^{js_0}$, $2^{js_\infty}$ and $\theta=1-p_0/p$); the top endpoint U1.$\infty$, already stated for the $L^p$-level operator `brrsLpHalfWaveExtension` and every `MemLp _ ⊤` input; and `brrsRadialProfileLift`. The obstruction is a domain mismatch: the transport needs both endpoints on the same class, and Proposition 5.1 is proved for radial Schwartz inputs while the transport's domain is simple profiles. Route: interpolate the radial kernel operator on the profile line rather than the half-wave, and transfer the interpolated bound back to the half-wave for radial Schwartz inputs through the already-proved kernel representation; the transfer to an arbitrary profile is then a monotone-convergence step, not a density argument, because the whole chain is stated for nonnegative profiles. Advanced at 2026-09-02T02:49:20-04:00: `brrsSectionFiveCompactRadialCore_le` now isolates the profile-independent part of the compact estimate -- it holds for any nonnegative radial output obeying the two pointwise kernel majorants, so it applies to the kernel operator directly, with no polar step and no Schwartz hypothesis on the output. Remaining in this row: generalize the source-side definitions `brrsSectionFiveRadialProfile`/`brrsSectionFiveOneDimSource`/`brrsSectionFiveFarSourceInner` and the lemmas depending on them to take an arbitrary measurable profile instead of a Schwartz input and a unit ray (a mechanical substitution across about fifteen declarations), then prove the $L^\infty$ endpoint for the kernel operator and apply the transport. |

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

At 2026-09-01T18:39:00-04:00, a resumption audit found that the module as
committed did **not** compile: `tsum_brrsSectionFiveFarSourceII_le_geometric_fullRange`
contained an elaboration error (`hp.le` applied to `hp : 1 ≤ p`), so the
2026-09-01T18:03:06-04:00 `complete` label for (5.5) was not in fact
supported by an accepted proof.  The term was repaired to `hp_pos.le`; the
statement itself is unchanged.  A fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check then reported zero errors, so (5.5) is genuinely closed as of this
timestamp, which is why its row timestamp was advanced.

At 2026-09-01T18:41:07-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check reported zero errors after the terminal-cell local-counting
normalization was added.  This verifies source step (5.6) in the form
recorded above.

At 2026-09-01T18:57:41-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check reported zero errors after the initial-cell development was added.
This verifies source step (5.7) in the form recorded above.

At 2026-09-01T19:12:33-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check reported zero errors after the radial cell summation was added.  This
verifies source step (5.8) in both displays recorded above.

At 2026-09-01T19:26:15-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check reported zero errors after the weighted one-dimensional join was
added.  This verifies source step (5.4) in the form recorded above.

At 2026-09-01T19:52:04-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check reported zero errors after the global half-density kernel majorant was
added.  It is recorded as evidence for the still-in-progress source step
(5.3) and is not reported as a completed source theorem.

At 2026-09-01T20:34:12-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check reported zero errors after the innermost radial cell was added to the
Section 5 decomposition.  The (5.8) and (5.4) rows were re-verified with the
enlarged aggregate: the earlier statements covered only `2^{-j} ≤ r ≤ 20`,
which does not exhaust the compact spatial region needed by (5.3), so the
innermost cell `0 ≤ r ≤ 2^{-j}` was added and both theorems reproved with the
constant `56`.  Both rows remain complete and their evidence has been updated
accordingly.

At 2026-09-01T20:52:36-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check reported zero errors after the low-output kernel majorant was added.
It is recorded as evidence for the still-in-progress source step (5.3).

At 2026-09-01T21:31:48-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check reported zero errors after the aggregate far-source development was
added.  An audit of the (5.4) chain found that its far input is the sum of
the `p`-th powers of the individual far terms, whereas the compact reduction
(5.3) needs the `p`-th power of their sum, which the source obtains from
(5.5) by the triangle inequality in `L^p`.  That passage is now proved
(`brrsSectionFiveFarSourceTotal_le_card_mul`); the (5.4) row will be
restated with the aggregate far term once the normalization step is
finished.  All of this is recorded as evidence for the still-in-progress
source step (5.3).

At 2026-09-01T21:47:05-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 and no errors after the aggregate far-source term
was normalized (`brrsSectionFiveFarSourceTotal_le`, with the time-grid
factor `2^j` cancelling exactly against the frequency factor of the
pointwise bound) and (5.4) was restated and reproved with that term.  The
(5.4) row stays complete with updated evidence; (5.3) remains in progress.

At 2026-09-01T21:58:12-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after the one-dimensional radial source profile
`brrsSectionFiveRadialProfile` and the identity
`brrsSectionFiveRadialProfile_weight_eq` were added.  The identity shows that
the polar half-density weight `s^{(d-1)/2} |f(s w)|` is exactly the literal
Section 5 source weight `s^{s_p} f_0(s)`, which is the bridge between the
kernel majorant and the far-source terms.  This is evidence for the
in-progress source step (5.3).

At 2026-09-01T22:22:10-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after the factored pointwise bounds, the radial
source profile, the decay-order monotonicity, and the near/far splitting of
the one-dimensional source quantity were added.  All of this is evidence for
the still-in-progress source step (5.3).

At 2026-09-01T22:47:33-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after the polar reduction of the compact spatial
integral, the radial cell covering, the four-term convexity inequality, and
the two Jacobian/outer-weight identifications were added.  All of this is
evidence for the still-in-progress source step (5.3).

At 2026-09-01T23:07:41-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after the outer-weight comparison, the outer cell
covering, and the distribution of the `p`-th power over the eight Section 5
integrands were added.  All of this is evidence for the still-in-progress
source step (5.3); the only remaining work in that row is the integration
and time-summation bookkeeping.

At 2026-09-01T23:36:05-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after the innermost-region assembly step
`brrs_innerRegion_sum_le` was added, together with the bookkeeping lemmas it
needs (`brrsSectionFiveTerminalWeight_eq_sourceWeight`,
`measurable_brrsSectionFiveFarSourceInner`, `brrs_lintegral_mul_sum8`,
`brrsDyadicRadialBlockRadius_zero_le_twenty`).  A source-faithfulness check
during this step found that the near-source split had to be stated with the
literal compact source truncation `0 ≤ s ≤ 2^10` of the terminal cell rather
than with the untruncated radial profile: the terminal block of (5.8) is
defined with the truncated profile, so the untruncated form could not be
matched to it.  `brrsSectionFiveOneDimSource_near_le` and the two lemmas
depending on it were restated and reproved with the truncated profile; the
cells with the untruncated profile still dominate it, so nothing downstream
is weakened.  This is evidence for the still-in-progress source step (5.3).

At 2026-09-02T00:03:52-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after the outer-region assembly
`brrs_outerRegion_sum_le` and its component lemma
`brrs_outerRegion_near_component_le` were added.  Both radial regions of the
compact spatial reduction are now closed; only the top-level combination
remains in source step (5.3).

At 2026-09-02T00:26:41-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0, and a literal `sorry`/`admit`/`axiom` audit of the
module found no such declaration (the single textual hit is the English word
"admit" inside a docstring).  This verifies source step (5.3), which is now
complete.  With (5.3) closed, the only open prerequisite of (5.2) in the
Section 5 stream is the unnumbered exterior estimate U5.E, which therefore
becomes the selected item in this stream.

At 2026-09-02T00:47:12-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after the absorbed exterior kernel hypotheses were
discharged for the actual Section 5 phase-line kernel.  This closes the first
half of the in-progress unnumbered step U5.E; the exterior polar reduction
remains.

At 2026-09-02T01:02:18-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after
`brrsSectionFiveSourceWeight_mul_oneDimSource_rpow_eq` was added: on the
exterior region the literal outer weight `r^{-p s_p}` merges with the inner
source weight `s^{s_p}` into the exterior ratio weight `(s/r)^{s_p}` of the
Young core, so the compact-region pointwise machinery transfers verbatim.
This is evidence for the in-progress unnumbered step U5.E.

At 2026-09-02T01:18:40-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after the exterior four-phase split, the exterior
polar reduction, and the measurability of the exterior phase integrals were
added.  All the ingredients of the in-progress unnumbered step U5.E are now
proved; only their assembly remains.

At 2026-09-02T01:34:07-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after the exterior fixed-time estimate was
assembled.  This verifies the unnumbered step U5.E, which is now complete.
With U5.E and (5.3) both closed, all prerequisites of (5.2) (U5.E, U5.C,
(5.3)) are complete, so (5.2) becomes the selected item in the Section 5
stream.

At 2026-09-02T01:57:33-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after the full-space dyadic reduction was assembled.
This verifies source step (5.2), which is now complete.  A subsidiary
correction was needed on the way: the exterior estimate had to be restated
with a constant uniform in the frequency level, since it is multiplied by the
cardinality of the time packet; the earlier cubic domination of the absorbed
kernel left a spurious factor `2^j`, which the scaled-cubic domination
removes.  The quantifier order of (5.3) and of U5.E was also adjusted so that
their kernel constants are uniform in `j`, `T` and `f`, as their proofs
already gave.  With (5.2) closed, its two consumers (5.1) and Proposition 5.1
become the selected items in the Section 5 stream; their only further input is
the entropy consequence U5.$\kappa$-ent, which is already complete.

At 2026-09-02T02:14:56-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after Proposition 5.1 was assembled.  This verifies
(5.1) and Proposition 5.1, which are now complete, and closes the entire
Section 5 upper-bound stream: every numbered display (5.1)--(5.8) and every
unnumbered Section 5 prerequisite (U5.Setup data, U5.R, U5.K, U5.C,
U5.$\kappa$-def, U5.$\kappa$-ent, U5.M, U5.E) now has a closed Lean proof.
The next selected item in this stream is the unnumbered interpolation step
U1.I, whose recorded prerequisites -- the fixed-time `p = infinity` endpoint
U1.$\infty$, the identity tail (1.9), and Proposition 5.1 -- are all
complete.

At 2026-09-02T02:31:14-04:00, the Section 5 stream advanced to its next
selected item U1.I, and a prerequisite audit of that row was recorded above.
The audit found that the obstruction is a domain mismatch between the two
interpolation endpoints rather than a missing estimate, and identified the
representation identity which removes it.  No Lean declaration changed in
this step, so the module verification of 2026-09-02T02:14:56-04:00 still
stands.

At 2026-09-02T02:49:20-04:00, a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0 after `brrsSectionFiveCompactRadialCore_le` was
added.  It is recorded as evidence for the in-progress step U1.I: it is the
compact estimate with the output abstracted to any nonnegative radial
function satisfying the two kernel majorants, which is what makes the same
estimate available on the interpolation domain.

At 2026-09-02T03:34:07-04:00 the profile-general layer of U1.I was completed
and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added, in dependency order:
`brrsSectionFiveOneDimSourceOf`, `brrsSectionFiveFarSourceInnerOf`,
`measurable_brrsSectionFiveFarSourceInnerOf`,
`brrsSectionFiveOneDimSourceOf_near_le`,
`brrsSectionFiveOneDimSourceOf_far_eq`,
`brrsSectionFiveOneDimSourceOf_le_near_add_far`,
`brrsSectionFiveOneDimSourceOf_rpow_le`, `brrs_innerRegionOf_sum_le`,
`brrs_outerRegionOf_sum_le` and `brrsSectionFiveCompactRadialCoreOf_le`.
These are the Section 5 source terms and the compact radial core over an
arbitrary measurable profile `g : Real -> ENNReal` in place of the radial
profile of a Schwartz function; the earlier declarations are their
radial-Schwartz instances.  With this the compact weighted estimate holds for
any nonnegative radial output obeying the two pointwise kernel majorants over
any measurable profile, which is the form the Riesz--Thorin domain of U1.I
requires.  Remaining in U1.I: the `L^infty` endpoint for the radial kernel
operator, the transport application, the monotone extension from simple
profiles to arbitrary profiles, and the transfer back to the half-wave
through the established kernel representation.

At 2026-09-02T04:12:38-04:00 the positive radial kernel operator of U1.I was
introduced and its compact estimate proved; a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added: `brrsRadialKernelWeightedSource` (the
positive operator with kernel `|K_j(r,s,t)|` acting on the weighted profile),
`brrs_ofReal_rpow_halfDensity_split`,
`brrsRadialKernelWeightedSource_le_oneDimSourceOf`,
`brrsRadialKernelWeightedSource_halfDensity_le`,
`brrsRadialKernelWeightedSource_lowOutput_le`,
`brrsRadialKernelWeightedSource_mono_const` and
`brrsRadialKernelWeightedSource_compact_le`.

This resolves the representation obstruction recorded earlier in a different
way than first planned, and the change of route is worth stating.  The
earlier plan was to extend the radial-kernel representation of the half-wave
from radial Schwartz inputs to lifted simple profiles.  That extension is not
available: the representation is proved through
`brrsDyadicHalfWave_eq_twoRadius_surfaceFourier_kernel`, which uses Fourier
inversion on the Schwartz class, and a simple profile's lift is not Schwartz.
The route now taken instead interpolates the *positive kernel operator* on
the profile line rather than the half-wave.  Its two kernel majorants,
`exists_norm_brrsRadialBesselKernel_fourPhase_lowOutput_majorant` and
`exists_norm_brrsRadialBesselKernel_fourPhase_halfDensity_majorant`, are
statements about the kernel alone, so they hold over any profile whatever;
the half-wave is then recovered at the end for radial Schwartz inputs through
the representation that *is* available, where it is exactly the pointwise
domination used in Section 5.  Remaining in U1.I: the far and exterior halves
of the low endpoint for the kernel operator, the `L^infty` endpoint for it
(from the `s`-integral of the kernel majorant), the transport, and the
monotone extension from simple profiles to arbitrary ones.

At 2026-09-02T04:58:41-04:00 the exterior half of the U1.I low endpoint was
completed and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added: `brrsExteriorPhaseIntegralOf`,
`measurable_brrsExteriorPhaseIntegralOf`,
`brrsSectionFiveSourceWeight_mul_oneDimSourceOf_rpow_eq`,
`brrs_exterior_integrandOf_rpow_le` (the exterior travelling-phase pieces
over an arbitrary profile), `brrsExteriorRadialCoreOf_le` (the exterior
estimate with the output abstracted to any nonnegative radial function
obeying the half-density kernel majorant) and
`brrsRadialKernelWeightedSource_exterior_le_uniform` (its instance for the
positive radial kernel operator, with a constant independent of both the
frequency level and the profile).  Together with
`brrsRadialKernelWeightedSource_compact_le` this covers both spatial regions
for the kernel operator.  Remaining in U1.I: assemble the two regions into
the low endpoint at the level of the discrete `L^p` norm, prove the
`L^infty` endpoint for the kernel operator from the `s`-integral of the
kernel majorant, apply the transport, and extend from simple profiles to
arbitrary ones by monotone convergence.

At 2026-09-02T05:31:52-04:00 the low endpoint of U1.I was completed for the
positive radial kernel operator and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added
`brrsRadialKernelWeightedSource_dyadicReduction_le` (the two spatial regions
assembled as in (5.2)) and `brrsRadialKernelWeightedSource_entropy_le` (its
entropy form, the analogue of Proposition 5.1, over an arbitrary measurable
profile).

The remaining plan for U1.I is now fixed, and is recorded here because it
determines what the last steps must prove.  Write `T_abs` for the complex
linear operator with kernel the absolute value of the radial Bessel kernel;
it agrees with the positive operator on nonnegative profiles and dominates
the half-wave pointwise through the radial-kernel representation, which is
available for radial Schwartz inputs.  Then: (i) prove the `L^infty` endpoint
`sup` over `r > 0` and `t` in `[1,2]` of the `s`-integral of the kernel is at
most a constant times `2^(j(d-1)/2)`, which by the two kernel majorants
reduces to the elementary moment bound for the phase kernel already available
through `brrsExteriorAbsorbedKernel` and its uniform mass estimate; (ii) apply
`highExponent_discreteLpEstimate_of_lower_and_top` to `T_abs` on simple
profiles, where both endpoints hold; (iii) extend to an arbitrary nonnegative
measurable profile by monotone convergence, using that simple functions
increase to it and that both sides of the estimate pass to the monotone limit
-- this is where the earlier density obstruction dissolves, since the operator
is positive; (iv) recover the half-wave bound for radial Schwartz inputs from
the representation, which is exactly the pointwise domination already used in
Section 5.  No step in this plan needs the representation for a non-Schwartz
input, which is the obstruction recorded earlier.

At 2026-09-02T06:14:20-04:00 the moment machinery for step (i) of the U1.I
plan was proved and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrs_rpow_le_mul_absorbed_weight` (a source
radius is at most the Japanese bracket of the phase centre times twice that
of the phase value), `brrs_lintegral_rpow_mul_omega_sub_le` and
`brrs_lintegral_rpow_mul_omega_add_le` (the moment bound for the receding and
the advancing phase line, each uniform in the frequency level, obtained by
translating onto `brrsExteriorAbsorbedKernel` and using its uniform mass
estimate), and `brrs_lintegral_rpow_mul_omegaFourPhase_le` (the four-line
form, in which each phase centre contributes its bracket twice).

What remains for step (i) is the case split on the output radius.  For
`2^j r <= 16` the low-output majorant gives the weight `(2^j s)^((d-1)/2)`
and both phase centres are bounded by `18`, since `t <= 2` and `r <= 16`; for
`2^j r > 16` the half-density majorant gives `r^(-(d-1)/2) s^((d-1)/2)` and
the ratio `(1 + (t + r))/r` is at most `(19/16) 2^j`, because `1 <= 2^j`.
Both cases therefore yield the rate `2^(j(d-1)/2)`, which is exactly the rate
of the top endpoint already available for the finite-time radial-profile
operator.

At 2026-09-02T06:52:03-04:00 step (i) of the U1.I plan was completed and a
fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrs_enorm_radialBesselKernel_le_weight`
(any factored real majorant for the kernel becomes a factored majorant in the
extended reals) and `exists_lintegral_enorm_brrsRadialBesselKernel_le`: there
is a finite constant such that for every unit ray, every frequency level,
every time in `[1,2]` and every positive output radius, the `s`-integral of
the kernel norm is at most that constant times `(2^j)^((d-1)/2)`.  The proof
splits on `2^j r <= 16`, using the low-output majorant with both phase
centres bounded by `18` in that case and the half-density majorant with the
ratio bound `(3+r)/r <= (19/16) 2^j` in the other.  The rate matches the
`L^infty` endpoint already available for the finite-time radial-profile
operator, which is the consistency check that the two endpoints can be
interpolated at all.

Remaining in U1.I: steps (ii) to (iv) of the recorded plan -- the transport
on simple profiles, the monotone extension to an arbitrary nonnegative
profile, and the recovery of the half-wave bound for radial Schwartz inputs.

At 2026-09-02T07:26:15-04:00 the measurability prerequisite for step (ii) of
the U1.I plan was proved and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added
`continuous_brrsDyadicHalfWaveKernelRadialProfile_uncurry`,
`continuous_brrsRadialBesselFactor`,
`measurable_brrsRadialBesselKernel_prod` and
`measurable_enorm_brrsRadialBesselKernel_prod`.

This was a gap the recorded plan had not identified: the transport
`highExponent_discreteLpEstimate_of_lower_and_top` requires the interpolated
operator to have measurable output, and the radial kernel had no measurability
lemma anywhere in the development.  It is now obtained from joint continuity
of the frequency integrand -- the Bessel factor is a continuous surface
Fourier transform, the kernel's radial profile is a continuous exponential
times a Schwartz symbol -- followed by measurability of the parametrized
integral.  With this the kernel operator can be defined with the measurable
output the transport needs.

At 2026-09-02T08:03:44-04:00 the operator layer of step (ii) was proved and a
fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Two changes were made.

First, `exists_lintegral_enorm_brrsRadialBesselKernel_le` was restated for
`0 <= r` in place of `0 < r`.  This is needed, not cosmetic: additivity of the
operator must hold at every point of the output space, including the origin,
where the output radius is zero.  The low-output majorant already covers
`r = 0`, and in the complementary case `2^j r > 16` positivity of `r` is
automatic, so the relaxation costs nothing.

Second, added `brrsRadialKernelAbsOutput` (the operator, with kernel the norm
of the radial Bessel kernel, so linear in the profile),
`brrs_halfDensityExponent_add_three_le`,
`brrs_integrable_radialKernelAbs_mul` (the defining integral converges for a
bounded measurable profile, by the kernel `L^1` bound),
`measurable_brrsRadialKernelAbsOutput` (measurable output, assembling the
finite time fibres), `brrsRadialKernelAbsOutput_add` and
`brrsRadialKernelAbsOutput_smul`.  These are exactly the four structural
hypotheses `hT_add`, `hT_smul`, `hT_measurable` and integrability that
`highExponent_discreteLpEstimate_of_lower_and_top` demands of its operator.
Remaining in step (ii): state the two endpoint bounds for this operator in
`eLpNorm` form and apply the transport.

At 2026-09-02T08:41:07-04:00 the norm conversions for step (ii) were proved
and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrsRadialProfileWeightENN` and its
measurability, `brrsRadialKernelWeightedSource_weight_eq` (on the source
half-line the profile weight cancels the operator weight, so the positive
operator applied to the weighted profile is the kernel integral of the
profile norm), `enorm_brrsRadialKernelAbsOutput_le` (the linear operator the
transport interpolates is dominated pointwise by the positive operator whose
low endpoint is proved) and
`brrs_lintegral_brrsRadialProfileWeightENN_rpow_eq` (the `p`-th moment of the
weighted profile is the `p`-th power of the profile's `L^p` norm against the
radial pushforward measure, times the total surface mass).

The surface mass bookkeeping is worth recording, because it is what makes the
low endpoint constant come out unchanged.  The transport measures the input in
`L^p` of the radial pushforward measure, which carries one factor of the total
surface mass relative to the weighted profile; the output side acquires the
same factor through polar coordinates, since the operator's output depends
only on the norm of the spatial variable.  The two factors cancel, so the low
endpoint inherits exactly the constant of
`brrsRadialKernelWeightedSource_entropy_le`.  Remaining in step (ii): the two
endpoint bounds in `eLpNorm` form, and the transport application; the output
side conversion is the existing
`discreteLpNorm_eq_eLpNorm_finset_counting_product_of_measurable`.

At 2026-09-02T09:19:33-04:00 the low endpoint of U1.I was proved in the form
the transport consumes and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrsRadialKernelAbsFibre` with
`brrsRadialKernelAbsOutput_eq_fibre` and
`measurable_brrsRadialKernelAbsFibre`, `enorm_brrsRadialKernelAbsFibre_le`,
`measurable_brrsRadialKernelWeightedSource_radius` and
`brrsRadialKernelAbsOutput_entropy_eLpNorm_rpow_le`.

The fibre form of the pointwise domination was needed rather than the product
form proved earlier: the polar reduction is applied one time fibre at a time,
for an arbitrary real time, and the product form carries a membership proof
for the time set that is not available there.  The fibre form involves no such
proof.

Remaining in U1.I: the `L^infty` endpoint for this operator, then the
transport application, the monotone extension, and the recovery of the
half-wave bound.  The `L^infty` endpoint needs one measure-theoretic fact not
yet in the development: on the source half-line, Lebesgue measure and the
radial pushforward measure have the same null sets, so an essential bound
against the latter can be used inside the kernel integral against the former.

At 2026-09-02T10:04:26-04:00 the measure comparison needed by the `L^infty`
endpoint was proved and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added
`brrs_volume_restrict_Ioi_absolutelyContinuous_radialProfileMeasure`: on the
source half-line, Lebesgue measure is absolutely continuous with respect to
the radial pushforward measure.  Also added
`enorm_brrsRadialKernelAbsFibre_le_kernelIntegral`, the kernel form of the
pointwise bound.

The direction of the absolute continuity is the one that matters and is worth
stating explicitly.  The transport measures the input profile against the
pushforward measure, so what it hands over is an essential bound with respect
to that measure; the kernel integral is taken against Lebesgue measure on the
half-line, so the bound has to survive being used there.  That is absolute
continuity of Lebesgue with respect to the pushforward, and it holds because
polar coordinates express the pushforward as the radial density against
Lebesgue with the density positive on the half-line.  Remaining in U1.I: the
`L^infty` endpoint itself, the transport application, the monotone extension,
and the recovery of the half-wave bound.

At 2026-09-02T10:41:58-04:00 the `L^infty` endpoint of U1.I was proved and a
fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrsRadialKernelAbsOutput_top_eLpNorm_le`:
there is a positive constant such that for every frequency level, every time
packet inside `[1,2]`, every unit ray and every measurable profile, the output
of the absolute radial kernel operator has essential supremum at most that
constant times `(2^j)^((d-1)/2)` times the essential supremum of the profile
against the radial pushforward measure.  The rate matches the top endpoint
already recorded for the finite-time radial-profile operator.

Both endpoints of the interpolation are now available for one and the same
operator, on one and the same domain, which was the obstruction this row
opened with.  Remaining in U1.I: apply
`highExponent_discreteLpEstimate_of_lower_and_top` to the absolute radial
kernel operator using these two endpoints, extend from simple profiles to an
arbitrary nonnegative measurable profile by monotone convergence, and recover
the half-wave bound for radial Schwartz inputs through the radial-kernel
representation.

