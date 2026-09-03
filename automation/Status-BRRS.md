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
| (3.3): Bessel asymptotic with $O(|u|^{-3/2})$ remainder | -- | complete | 2026-09-03T00:02:41-04:00 | The literal display is proved in every dimension at least two, in the paper's ordinary-Bessel convention. Bridge: `brrs_surfaceFourier_succ_eq_ordinaryBesselJ` for ambient dimension at least three and `brrs_surfaceFourier_two_eq_ordinaryBesselJ` for the circle identify the repository's normalized surface Fourier transform with $J_{(D-2)/2}$, through the Poisson--Beta representation `brrs_ordinaryBesselJ_poisson_repr` proved here from the series definition (Mathlib has no Bessel functions) together with the recorded sphere slicing. Two-wave display: `exists_brrs_ordinaryBesselJ_zero_twoWave`, `exists_brrs_ordinaryBesselJ_even_twoWave` and `exists_brrs_ordinaryBesselJ_odd_twoWave` give, for the circle and for both nonplanar parities, constants and a threshold-free bound $\lVert J_\nu(u) - u^{-1/2}(c_+e^{-iu}+c_-e^{iu})\rVert \leq C u^{-3/2}$ for $u \geq 1$, at the orders $0$, $n+1$ and $(2n+1)/2$, which are exactly $(D-2)/2$ in the ambient dimensions $2$, $2n+4$ and $2n+3$. The passage from the development's scaled endpoint asymptotics to the paper's travelling-wave normalization is `brrs_twoWave_package`, proved once and instantiated three times; the frequency-independence of the resulting constants is the exact cancellation of the bridge prefactor against the decomposition's weight. The earlier qualification is discharged: the ordinary-Bessel identification and the explicit two-wave packaging are both proved, not assumed. |
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
| (3.2): $\lVert g_I\rVert_p$ packet-norm upper bound | U3.R, U3.P, (3.3) | complete | 2026-09-02T23:31:35-04:00 | `exists_brrs_radialHalfWaveTestPacket_eLpNorm_le` proves the printed display for the source packet: for $d\geq2$, $p\geq2$ and every reference time $t_I\geq1$ (in particular for the endpoints of $I\subseteq[1,2]$ supplied by U3.P), $\lVert g_I\rVert_p\leq C\,2^{j((d+1)/2-1/p)}$ with $C$ independent of $j$ and $t_I$. The packet is the development's own datum `brrsRadialHalfWaveTestPacket`, whose identity with the paper's $g_I$ is the recorded `brrsRadialHalfWaveTestPacket_eq_halfWaveKernel`; no new object is introduced. Two sharp inputs are combined: the sup-norm bound `exists_brrs_norm_radialHalfWaveTestPacket_le` ($\lVert g_I\rVert_\infty\leq C2^{j(d+1)/2}$), and the Plancherel square integral `exists_brrs_integral_norm_sq_radialHalfWaveTestPacket_le` ($\int|g_I|^2\leq C2^{jd}$, by the exact frequency-annulus volume). Both are sharp, and the elementary interpolation $\int|g_I|^p\leq\lVert g_I\rVert_\infty^{p-2}\int|g_I|^2$ reproduces the exponent exactly. The sup-norm bound is proved in three regimes: away from the origin ($\lVert x\rVert\geq1/2$) by the uniform two-wave asymptotic `exists_brrs_surfaceFourier_twoWave` -- newly assembled here from the three parity clauses of (3.3) through `brrs_surfaceFourier_twoWave_of_bridge` -- together with the annular moment bounds `exists_brrs_annularSymbol_moment_le`; near the origin ($\lVert x\rVert\leq1/2$) by the exact spherical Fubini form `brrs_radialHalfWaveTestPacket_eq_sphere_integral` of the U3.R radial inversion, where the phase $t_I-\langle\omega,x\rangle\geq1/2$ never vanishes and the rapid decay `exists_brrs_schwartzFourier_decay` of the Fourier transform of the weighted annular profile (`exists_brrs_weightedAnnularSchwartz`) beats the frequency volume; and at the finitely many levels $2^j<16\pi$ below the two-wave threshold by the crude frequency-mass bound `exists_brrs_norm_radialHalfWaveTestPacket_le_crude`. Qualification: the display is proved on the exponent range $p\geq2$, which is exactly the range of the Layer 13 target `BRRSTheoremOneWithSharpnessStatementFor` (it requires $2\leq p$), so nothing needed later is missing. |
| (3.4): $T_t^-+T_t^++T_t^{\mathrm{rem}}$ decomposition | U3.R, U3.P, (3.3) | complete | 2026-09-02T23:44:26-04:00 | `brrs_dyadicHalfWaveKernel_threeTerm_decomposition` proves the exact decomposition for the annular half-wave kernel of an arbitrary annular cutoff at an arbitrary time and every nonzero point: the kernel is $T^-+T^++T^{\mathrm{rem}}$, where `brrsSectionThreeFocusingTerm` and `brrsSectionThreeSpreadingTerm` are the two travelling terms $\lVert x\rVert^{-(d-1)/2}$ times the one-dimensional annular wave integral `brrsSectionThreeWaveIntegral` at the phases $s-\lVert x\rVert$ and $s+\lVert x\rVert$, and `brrsSectionThreeRemainderTerm` is the intrinsic remainder, namely the radial integral of the two-wave error of the surface Fourier transform. `brrs_dyadicHalfWave_positiveRadialTestPacket_threeTerm_decomposition` instantiates it at the actual propagated Section 3 datum: the half-wave applied to `brrsPositiveRadialHalfWaveTestPacket` at time $t$ is the decomposition for the positive $TT^*$ cutoff at the relative time $t-t_I$, through the recorded `brrsDyadicHalfWave_positiveRadialTestPacket_eq_halfWaveKernelTTStarCutoff`. The identity holds for arbitrary leading constants and with no frequency threshold: the constants of (3.3) and the smallness of the remainder enter only in (3.5)--(3.7). Convergence of each of the three integrals is proved (`brrs_integrableOn_sectionThreeWaveIntegrand`, `brrs_integrableOn_sectionThreeRemainderIntegrand`), which is what makes the splitting legitimate; both rest on the annular radial moments of (3.2) through the reusable `brrs_integrableOn_annular_dominated`. |
| (5.5): far-source $\mathrm{II}_n$ tail summation | U5.C, U5.K | complete | 2026-09-01T18:39:00-04:00 | `tsum_brrsSectionFiveFarSourceII_le_geometric_fullRange` proves the literal one-sign source contribution `brrsSectionFiveFarSourceII` for every selected sign, throughout the printed range $1\leq p<2d/(d-1)$. It combines the strict-Hölder $1<p<2$, direct $p=1$, and $p\ge2$ branches, sums $n=10+k$, and gives a finite constant depending only on $d,p,L$ times the exact factor $2^{-Lj}\int |f_0|^p$. The four values of `BRRSSectionFiveFarSourcePhase` establish all source sign choices separately; no four-phase block is identified with $\mathrm{II}_n$. The formal profile is the standard zero extension of the paper's nonnegative radial profile from $(0,\infty)$; the half-open annuli/endpoints are Lebesgue-null conventions. The actual-kernel constant and $4^{p-1}$ convexity factor belong later to the separate reduction from (5.3) to (5.4). |
| (5.6): terminal $\mathrm{I}_j$ estimate | U5.C, U5.K | complete | 2026-09-01T18:41:07-04:00 | `brrsSectionFiveTerminalCell_kappa_fourPhase_le` proves the literal terminal cell for $d\geq2$ and $p\geq2$: the four travelling phase lines $t\pm r\mp s$ over the terminal radial range are bounded by $4\,\kappa_{j,j}(ps_p)$ times a fixed $j$-independent constant times $\int|f_0|^p$. It composes `brrsSectionFiveTerminalCell_sourceWeight_fourPhase_le` -- which retains the source truncation $0\leq s\leq 2^{10}$ (`brrsSectionFiveTerminalSourceProfile`), bounds the polar weight by one on the terminal interval (`brrsSectionFiveTerminalWeight_le_one`), dominates $\omega_j$ by the normalized cubic majorant, and applies one-dimensional Young to each sign (`brrsSectionFiveTerminalFourPhaseBlock_le_card_mul`) -- with the endpoint cardinality comparison `dyadicDiscretization_card_le_brrsDyadicKappa_terminal`, which is the U5.C edge $\#T\leq\kappa_{j,j}$ at counting radius one. The explicit constant is the cubic-majorant mass; no $\kappa$-free `T.card` form is reported as the source step. |
| (5.7): initial-cell $\mathrm{I}_0$ estimate | (1.4), U5.C, U5.K | complete | 2026-09-01T18:57:41-04:00 | `brrsSectionFiveInitialCell_sourceWeight_fourPhase_le` proves the printed conclusion: for $d\geq2$, $p\geq2$, nonempty $E$ and a $2^{-j}$-discretization $T$, the four travelling phase lines over the initial annulus $[2^{-j},2^{-j+1}]$ carrying the literal outer weight $r^{-ps_p}$ are at most $56\cdot 2^{j\nu_E^\sharp(ps_p)}$ times a fixed $j$-independent constant times $\int|f_0|^p$. The two displayed ingredients are proved separately and used exactly as printed: local packing (`brrsKappa_le_two_mul_rpow_of_isSeparated`, `brrsDyadicKappa_zero_le_two_mul_two_rpow`) gives $\kappa_{j,0}(ps_p)\leq 2\cdot2^{jps_p}$ at the mesh counting radius, and `two_rpow_mul_le_two_rpow_mul_brrsLegendreAssouadFunction` supplies $ps_p\leq\nu_E^\sharp(ps_p)$ from `le_brrsLegendreAssouadFunction_of_nonempty`. No entropy tail (U5.$\kappa$-ent) is used. |
| U5.M (unnumbered): $0<m<j$ intermediate-cell estimate | U5.$\kappa$-def, U5.K | complete | 2026-09-01T15:15:49-04:00 | `brrsSectionFiveIntermediateCell_fourPhase_le` proves the strict four-sign interval-cell bound via rapid majorization, fivefold overlap, and Young; `brrsSectionFiveIntermediateCell_sourceWeight_fourPhase_le` specializes the literal outer weight $r^{-ps_p}$. ENNReal is only the positive-$|f_0|$ implementation of the source norm estimate. |

## Layer 4 -- joins internal to the Section 2, 3, and 5 branches

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| U2.R-app (unnumbered): apply Rutar to the verified candidate | U2.R, U2.A | complete | 2026-09-01T15:15:49-04:00 | `brrsRutarCorollaryB` applied to `brrsProfileSpectrumCandidate_isRutarAssouadSpectrum` is the source realization step following (2.7). |
| (2.4): left-limit spectrum comparison | U2.C, U2.K | complete | 2026-09-01T15:15:49-04:00 | `exists_brrsSectionTwo_left_weighted_approximation` proves the displayed comparison. At $\theta_*=0$ it supplies the necessary degenerate branch $\theta_*^-=0$; the source's strict-left phrase has no inhabitant in that boundary case, so this repairs rather than weakens the theorem argument. |
| (3.5): main-term lower bound on $D_t$ | U3.P, (3.4) | complete | 2026-09-03T00:06:16-04:00 | `exists_brrs_sectionThreeFocusingTerm_lower_bound` and its mirror `exists_brrs_sectionThreeSpreadingTerm_lower_bound` prove the printed lower bound: for $d\geq1$, a nonzero two-wave constant and the positive $TT^*$ cutoff, whenever the travelling phase satisfies $\lvert s\mp\lVert x\rVert\rvert\leq 2^{-j}/32$ and $\lVert x\rVert>0$, the corresponding term of the (3.4) decomposition is at least $c_1\lVert x\rVert^{-(d-1)/2}2^{j(d+1)/2}$ with $c_1>0$ independent of $j$, $s$ and $x$. The radial weight is kept explicit (the earlier form of this row bounded it below using $\lVert x\rVert\leq4$; the present statement is strictly stronger and is what (3.1) needs, since the same weight appears in (3.6) and (3.7) and cancels on comparison). The geometric inputs `brrs_sectionThree_shell_phase_le` and `brrs_sectionThree_shell_phase_le_of_le` show that membership in the source shell `brrsSectionThreeSpatialShell` at mesh $2^{-j}$ gives exactly that phase bound, in the two reflected cases $t_I\leq t$ and $t\leq t_I$ of U3.P. The analytic core is `exists_brrs_sectionThreeWaveIntegral_lower_bound`: for the positive $TT^*$ cutoff the zero-phase wave integral is the exact positive radial moment (`brrs_sectionThreeWaveIntegral_zero_eq`, using `brrs_ttStarAnnularCutoff_symbol_eq_normSq` and the exact moment scaling `brrs_annular_moment_scaling`), that moment is strictly positive (`brrs_annularSymbol_normSq_moment_pos`, from continuity and nontriviality of the cutoff), and the first-order phase estimate $\lVert e^{i\theta}-1\rVert\leq2\lvert\theta\rvert$ costs at most a quarter of it on the shell, because the next moment is at most four times the first on the annulus. Nonvanishing of the leading constants is now proved rather than assumed: the three clauses of (3.3) were strengthened to carry $c_{\mathrm{out}}\neq0$ and $c_{\mathrm{in}}\neq0$, which reduces to the explicit Fresnel value (`brrs_quadraticFresnelLimit_ne_zero` from `brrsQuadraticFresnelLimit_eq_explicit`), the nonvanishing endpoint profiles, and the nonvanishing stationary leading coefficients. |
| (3.6): $T_t^+$ error estimate | U3.P, (3.4) | complete | 2026-09-03T00:15:33-04:00 | `exists_brrs_sectionThreeSpreadingTerm_upper_bound` proves, for every polynomial order $N$, that the spreading term is at most $C\lVert x\rVert^{-(d-1)/2}2^{j(d+1)/2}(1+2^j\lvert s+\lVert x\rVert\rvert)^{-N}$: the same frequency size as the focusing term, with arbitrary decay in the rescaled nonstationary phase. `exists_brrs_sectionThreeFocusingTerm_upper_bound` is the identical statement for the focusing term at the phase $s-\lVert x\rVert$, needed off the shell. Both rest on `exists_brrs_sectionThreeWaveIntegral_decay`, which identifies the travelling wave integral with a rescaled Fourier transform of the weighted annular profile (`brrs_annularOscillatory_realWeight_eq_fourier`, the real-weight form of the identity used for (3.2)) and then applies the rapid decay of the transform of a Schwartz function. This replaces the source's integration by parts: the decay of the Fourier transform of the fixed compactly supported profile is the same phenomenon, and it is uniform in the frequency level because the whole $j$-dependence is the exact scaling $c^{-(d+1)/2}$. |
| (3.7): remainder error estimate | U3.P, (3.4) | complete | 2026-09-03T00:15:33-04:00 | `exists_brrs_sectionThreeRemainderTerm_bound` proves that for $d\geq2$ and $2^j\lVert x\rVert\geq8\pi$ the intrinsic remainder of (3.4) is at most $C\lVert x\rVert^{-(d+1)/2}2^{j(d-1)/2}$, one full power of the frequency below the travelling terms. The proof is the source's: on the support of the annular profile the two-wave error bound of (3.3) applies pointwise (this is exactly where the threshold $2^j\lVert x\rVert\geq8\pi$ is used, so that $\rho\lVert x\rVert\geq1$ throughout the annulus), the radial Jacobian is absorbed into the half power, and the resulting annular moment of order $(d-3)/2$ is finite with the exact scaling. The statement also carries the two-wave constants and their nonvanishing, so that (3.1) can use one set of constants for (3.5), (3.6) and (3.7) simultaneously. |
| (5.8): sum of the $\mathrm{I}_m$ estimates | U5.C, U5.M, (5.6), (5.7) | complete | 2026-09-01T20:34:12-04:00 | `brrsSectionFiveNearSourceCellSum_le_kappa_sum` adds the individual cell estimates. The aggregate `brrsSectionFiveNearSourceCellSum` is the innermost cell $0\leq r\leq2^{-j}$ (with its polar weight `brrsSectionFiveInnerWeight`), the dyadic cells $2^{m-j}\leq r\leq2^{m-j+1}$ for $0\leq m<j$, and the terminal cell; together these exhaust the compact radial range. The bound is $56\big(\sum_{m=0}^{j}\kappa_{j,m}(ps_p)\big)$ times a fixed $j$-independent constant and $\int|f_0|^p$. Per-cell inputs: `brrsSectionFiveCell_kappa_le` (U5.M for $0<m<j$, the first half of (5.7) at $m=0$), `brrsSectionFiveTerminalCell_kappa_fourPhase_le` for (5.6) with the base-scale cardinality edge, and `brrsSectionFiveInnerCell_kappa_le` for the innermost cell, whose block estimate (`brrs_sum_innerCell_add_weighted_profile_rpow_le`, `brrs_sum_innerCell_sub_weighted_profile_rpow_le`) is the translated main-cell estimate, so no new overlap geometry and no change of counting radius is involved. `brrsSectionFiveNearSourceCellSum_le_initialEntropy_add_kappa_tail` records the equivalent printed display with the $m=0$ term shown as $2\cdot2^{j\nu_E^\sharp(ps_p)}$ via (5.7). No entropy hypothesis on $E$ is used at this step. |

## Layer 5 -- late source estimates inside the three branches

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.5): eventual comparison of $\theta_n$ and $\theta_*$ | U2.K, (2.4) | complete | 2026-09-01T15:15:49-04:00 | `eventually_brrsSectionTwo_parameter_tail_estimates` proves the eventual pair $\theta_n\geq\theta_*^-$ and $\theta_n\alpha\leq\theta_*\alpha+\varepsilon$; the $\theta_*=0$ case uses the repaired degenerate branch from (2.4). |
| (3.1): localized lower bound | (3.2), (3.4), (3.5), (3.6), (3.7) | complete | 2026-09-03T00:30:15-04:00 | `exists_brrs_sectionThree_localized_lower_bound` proves the printed localized bound: there are $c>0$ and $K>0$ such that for every level $j$, every reference time and every sampled time with $t_I\leq t$, $R/2\leq t-t_I\leq R$ and $2^jR\geq K$, $$c\,R^{-\frac{d-1}{2}p}\,2^{j\frac{d+1}{2}p}\,R^{d-1}2^{-j}\ \leq\ \int_{D_t}\lvert A_j^t g_I\rvert^p,$$ where $D_t$ is the source shell `brrsSectionThreeSpatialShell` at mesh $2^{-j}$ and $g_I$ is the positive radial test packet. `exists_brrs_sectionThree_localized_lower_bound_sum` is the same estimate summed over a finite set of sampled times, with the cardinality in front. The pointwise input is `exists_brrs_sectionThree_pointwise_lower_bound`: on the shell the focusing term of (3.4) is at least $c_1\lVert x\rVert^{-(d-1)/2}2^{j(d+1)/2}$ by (3.5), while the spreading term is at most a constant times that size divided by $1+2^j\lvert s+\lVert x\rVert\rvert\geq K/2$ by (3.6) with $N=1$, and the remainder is at most a constant times that size divided by $2^j\lVert x\rVert\geq K/4$ by (3.7); so both errors are at most a quarter of the main term as soon as $K$ exceeds an explicit constant built from those three constants (and $32\pi$, for the threshold of (3.7)). The volume input is `brrs_volume_real_sectionThreeSpatialShell_ge`, which computes the shell as a difference of two balls and bounds the difference of the $d$-th powers below by $(a-w)^{d-1}\cdot2w$. The radial weight is then frozen using $\lVert x\rVert\leq2R$ on the shell. Entropy is not used: the cardinality of the sampled set is carried symbolically, exactly as in the source. |
| (5.4): weighted one-dimensional estimate | (5.5), (5.8) | complete | 2026-09-01T21:47:05-04:00 | `brrsSectionFiveWeightedOneDim_le` joins the two inputs on the printed range $2\leq p<2d/(d-1)$. The aggregate `brrsSectionFiveWeightedOneDimTotal` is the full near-source radial cell sum of (5.8) (covering $0\leq r\leq20$) plus the four literal far-source sign contributions `brrsSectionFiveFarSourceTotal` over the whole far range $s>2^{10}$. It is at most $56\big(\sum_{m=0}^{j}\kappa_{j,m}(ps_p)\big)C^p\int|f_0|^p$ from (5.8) plus $4\,C_{\mathrm{far}}(d,L,j,p)\int|f_0|^p$, where `brrsSectionFiveFarTotalConstant` carries the exact gain $2^{-Lj}$ and its finiteness is part of the conclusion. The far input is the aggregate form of (5.5): the per-annulus Hölder step of (5.5) is applied pointwise in $(t,r)$ and the annuli are summed by the scalar geometric series `tsum_brrsSectionFiveFarAnnulusPointwiseCoefficient_rpow_le`, which is the Lean rendering of the source's triangle inequality in $L^p$; the earlier sum-of-$p$-th-powers form did not support the next step (5.3) and has been replaced. |

## Layer 6 -- reductions immediately before main displayed bounds

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.6): covering-number estimate at $\theta_*^-$ | U2.S, (2.5) | complete | 2026-09-01T15:15:49-04:00 | `brrsAssouadScaleCoveringNumber_antitone_parameter` and `exists_brrsSectionTwo_covering_tail_of_parameter_tail` prove the power-scale inclusion and the source $\varepsilon/(1-\theta_*^-)$ cover estimate. The repaired $\theta_*=0$ branch has $\theta_*^-=0<1$. |
| U3.S (unnumbered): conversion of (3.1) to sharpness of (1.5) up to $\varepsilon$ | U1.Setup, (1.4), (3.1) | complete | 2026-09-03T00:58:24-04:00 | `not_uniformEstimateAtExponent_of_lt` proves the conversion: for $d\geq2$, $p\geq2$, nonempty $E\subseteq[1,2]$ and every $s$ strictly below the critical exponent $\nu_E^\sharp(ps_p)/p$, the canonical realization admits no uniform estimate at exponent $s$; `brrsTheoremOneSharpnessStatement_of_two_le` packages this as the source's sharpness clause `BRRSTheoremOneSharpnessStatement` on the whole printed range, superseding the previously proved Hilbert endpoint case. The quantitative bridge is `exists_brrs_weighted_packet_card_upper_of_uniformEstimate`: testing a hypothetical estimate on the Section 3 packet, and combining (3.1) summed over the sampled times with the packet norm (3.2), gives $\#U\leq C\,2^{jps}R^{ps_p}$ for every $2^{-j}$-separated packet of sampled times whose interval satisfies $2^jR\geq K$. The weighted entropy witnesses of (1.4) (`frequently_exists_local_isSeparated_finset_weighted_card_lower_of_lt` at $\alpha=ps_p$) violate that bound for every $q$ with $ps<q<\nu_E^\sharp(ps_p)$, after enlarging the witness interval to $R''=4\max(R,K2^{-j})$ -- whose ratio to $R$ is bounded because the dyadic level satisfies $2^{-j}<\delta/2\leq R/2$ -- and placing the reference time to the right of the interval, where the packet-norm hypothesis $t_I\geq1$ holds. Two auxiliary facts made this possible and are recorded separately: the conjugated cutoff `brrsConjAnnularCutoff` identifies the positive packet propagated in (3.1) with the ordinary packet of (3.2) (`brrsPositiveRadialHalfWaveTestPacket_eq_conj`), and the pointwise lower bound of (3.1) was proved in the sign-free form (distance to the reference time comparable to the interval length), which is what U3.P actually supplies. The degenerate branch $ps<0$ uses no entropy: a single sampled time with $R=\max(1,K)$ already contradicts a negative exponent. |
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
| U1.I (unnumbered): common radial finite-time operator and high-$p$ interpolation | (1.1) at $p=\infty$, (1.9), Proposition 5.1 | complete | 2026-09-02T14:12:36-04:00 | `brrs_discreteLpNorm_highExponent_le`: for every $p_0$ in $[2, 2d/(d-1))$, every $p > p_0$, every $q$ above the Legendre--Assouad value at $p_0 s_{p_0}$ and every $\varepsilon > 0$, there are a constant and a threshold such that for all $j$ beyond it and every dyadic discretization $T$ of $E$ inside $[1,2]$, the discrete $L^p$ norm of the annular half-wave over $T$ on radial Schwartz data is at most $A \, 2^{j((1-\theta)(q+\varepsilon)/p_0 + \theta (d-1)/2)}$ times the Euclidean $L^p$ norm of the input, with $\theta = 1 - p_0/p$. The interpolation is carried out on the positive radial kernel operator rather than on the half-wave: the two kernel majorants are statements about the kernel alone, so both endpoints hold over an arbitrary profile, and the half-wave is recovered at the end through the radial-kernel representation, which is available for radial Schwartz inputs and is exactly the pointwise domination used in Section 5. The chain is `brrsRadialKernelWeightedSource_entropy_le` (low endpoint) and `brrsRadialKernelAbsOutput_top_eLpNorm_le` (top endpoint, from the kernel's $L^1$ bound in the source variable), transported by `highExponent_discreteLpEstimate_of_lower_and_top` in `brrsRadialKernelAbsOutput_highExponent_simple`, extended to an arbitrary profile by monotone convergence in `brrsRadialKernelPosOutput_highExponent_le`, and specialized in `brrs_discreteLpNorm_highExponent_le`. Three prerequisites absent from the development had to be supplied: measurability of the radial kernel, absolute continuity of Lebesgue measure with respect to the radial pushforward on the source half-line, and the absorption of the linear entropy factor into the exponential rate. No assumption wrapper is used: the two `HasBRRSFiniteTimeRadialProfileSimpleBoundTransfer` predicates are not invoked anywhere in this chain. |

## Layer 12 -- radial upper estimate

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (1.5): radial upper estimate in Theorem 1.1 | U1.I, Proposition 5.1 | complete | 2026-09-02T15:52:18-04:00 | `brrsTheoremOneSchwartzCoreStatement_of_two_le`: for every dimension at least two, every annular cutoff, every time set inside $[1,2]$ and every exponent $p \geq 2$, the literal `BRRSTheoremOneSchwartzCoreStatement` holds, that is, for every $\varepsilon > 0$ the annular half-wave satisfies the displayed radial estimate at exponent $\nu_E^\sharp(p s_p)/p + \varepsilon$, over every frequency level and every dyadic discretization, on radial Schwartz data. Below the fixed-time critical exponent this is `brrs_schwartzCoreUniformEstimate_subcritical`, from Proposition 5.1; at and above it, `brrs_schwartzCoreUniformEstimate_supercritical`, from U1.I interpolating at a subcritical exponent chosen close enough to critical. The exponent match in the second range rests on two facts already in the Legendre--Assouad module: the function dominates its penalty, so the target is at least the Sobolev exponent; and it never exceeds one on the unit interval, while the subcritical penalty increases to one at the critical exponent. Supporting: `brrsLegendreAssouadFunction_le_one_of_nonneg_of_le_one`, `brrs_mul_sobolevExponent_eq`. |

## Layer 13 -- final theorem assembly

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| Theorem 1.1: full radial upper bound and sharpness package | U3.S, (1.5) | complete | 2026-09-03T01:49:30-04:00 | `brrsTheoremOneWithSharpnessStatement_of_two_le`: for every dimension at least two, every annular cutoff $\Phi$, every time set $E \subseteq [1,2]$ and every exponent $p \geq 2$, the literal `BRRSTheoremOneWithSharpnessStatement d \Phi E p` holds. Unfolded, this delivers the canonical realization `brrsLpHalfWaveExtension` together with both clauses of the paper's Theorem 1.1 for it: for every $\varepsilon > 0$ the estimate `UniformEstimateAtExponent \Phi W E p (\nu_E^\sharp(p s_p)/p + \varepsilon)$, uniformly over frequency levels $j \geq 1$, over every dyadic discretization $T$ of $E$ at level $j$ and over every a.e.-radial $f \in L^p$; and, when $E$ is nonempty, the failure of that estimate at every exponent strictly below $\nu_E^\sharp(p s_p)/p$. The upper clause is (1.5) (`brrsTheoremOneSchwartzCoreStatement_of_two_le`, radial Schwartz data) transferred by the previously conditional principle `uniformEstimateAtExponent_of_schwartzCore_of_radialSchwartzApproximation`, whose two hypotheses are now theorems: `brrs_hasRadialSchwartzLpApproximation` (radial Schwartz density in the a.e.-radial part of $L^p$) and `brrs_hasRadialSchwartzCoreConvergence` (continuity of the canonical realization along such approximations). The sharpness clause is U3.S (`brrsTheoremOneSharpnessStatement_of_two_le`). Verified: `lake env lean` on the module exits zero with no error and no `sorry`/`admit`, and `#print axioms brrsTheoremOneWithSharpnessStatement_of_two_le` reports only `propext, Classical.choice, Quot.sound`. Qualifications: the input class is `IsAERadial` $L^p$ data, matching the paper's radial setting and the hypothesis already carried by every earlier row; the time variable is sampled through `IsDyadicDiscretization`, the development's formalization of the paper's dyadic sampling of $E$; and the realization is existentially quantified in the statement package and witnessed here by the canonical convolution realization. |

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

At 2026-09-02T11:26:40-04:00 the low endpoint was put into the transport's
rate form and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added
`brrs_natCast_add_one_le_const_mul_two_rpow`, `brrs_ofReal_two_rpow`,
`brrs_entropyRate_le_shifted` and
`brrsRadialKernelAbsOutput_low_transport_form`.

A shape mismatch had to be resolved here and is worth recording, since it
costs an arbitrarily small amount of the exponent.  The transport takes each
endpoint rate literally in the form `A * 2^(j s)`, while the entropy bound
carries the factor `j + 1` and the shift `2^q` from `2^((j+1) q)`.  A linear
factor is dominated by any positive exponential rate -- through
`x + 1 <= exp x` applied to `j eps log 2` -- so for every `eps > 0` there is a
single constant with `(j+1) 2^((j+1) q) <= A 2^(j (q + eps))` for all `j`.
Taking `p`-th roots then gives the rate `2^(j (q + eps) / p)`, which is the
transport's form.  The loss is harmless because the hypothesis on `q` is a
strict inequality against the Legendre--Assouad value, so `q` may be chosen
below any target and the `eps` reabsorbed.

Remaining in U1.I: apply `highExponent_discreteLpEstimate_of_lower_and_top` to
the absolute radial kernel operator with these two endpoints, extend from
simple profiles to an arbitrary nonnegative measurable profile by monotone
convergence, and recover the half-wave bound for radial Schwartz inputs.

At 2026-09-02T12:07:55-04:00 the Riesz--Thorin transport was applied and a
fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrs_two_pow_rpow_eq` and
`brrsRadialKernelAbsOutput_highExponent_simple`: for simple integrable
profiles the absolute radial kernel operator satisfies the interpolated
estimate with constant the geometric mean of the two endpoint constants and
rate the corresponding convex combination of the two endpoint exponents,
namely `(q + eps) / p_0` at the low end and `(d-1)/2` at the top, with weight
`theta = 1 - p_0 / p`.  This is step (ii) of the plan, complete.  The
structural hypotheses of the transport -- additivity, homogeneity and
measurable output -- were discharged from the lemmas proved with the operator,
using that a simple function is bounded, which is what makes the defining
kernel integral converge.

Remaining in U1.I: step (iii), extension from simple profiles to an arbitrary
nonnegative measurable profile by monotone convergence, and step (iv),
recovery of the half-wave bound for radial Schwartz inputs through the
radial-kernel representation.  Then (1.5).

At 2026-09-02T12:44:11-04:00 the first half of step (iii) was proved and a
fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrsRadialKernelPosOutput`,
`measurable_brrsRadialKernelPosOutput` and
`enorm_brrsRadialKernelAbsFibre_eq_posOutput`.

The positive output is the quantity the monotone extension is stated for: it
is defined for every measurable profile in the extended reals, whereas the
interpolated operator is defined through a Bochner integral and so needs
integrability.  On a bounded nonnegative real profile the two agree exactly --
the Bochner integral is then the coercion of a nonnegative real integral,
which equals the corresponding lower integral -- and that agreement is what
lets the bound proved on simple profiles pass to the monotone limit.

Remaining in step (iii): the simple approximants and the monotone limit.  The
approximants are the standard increasing simple functions of a measurable
extended-real profile, cut off to a bounded interval so that they are
integrable against the radial pushforward measure; monotone convergence then
raises the bound from each approximant to the profile, on both sides of the
estimate.

At 2026-09-02T13:31:52-04:00 step (iii) of the U1.I plan was completed and a
fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added the approximants
`brrsProfileApproxSimple`, `brrsProfileApproxReal`, `brrsProfileApprox` with
their pointwise, monotonicity, supremum, boundedness and integrability
lemmas, `brrsRadialProfileMeasure_Iic_lt_top`, the limit ingredients
`brrs_iSup_rpow`, `brrs_eLpNorm_rpow_eq`,
`brrsRadialKernelPosOutput_mono`, `brrsRadialKernelPosOutput_iSup_approx`,
`enorm_brrsProfileApprox`, and the conclusion
`brrsRadialKernelPosOutput_highExponent_le`: the interpolated high-exponent
estimate holds over an arbitrary measurable profile.

This is the step the row opened by calling a density obstruction, and it is
worth recording why it dissolved.  Extending a bound from simple functions to
a general profile is delicate for a general operator, because it needs the
operator to be continuous in the norm one is extending along -- which is what
was being proved.  For a positive operator no such argument is needed: the
standard simple approximants increase to the profile, the positive output
increases with them by monotonicity of the kernel integral, and both sides of
the estimate pass to the monotone limit.  The only genuine work was making the
approximants integrable against the radial pushforward measure, which the
bounded cutoff provides.

Remaining in U1.I: step (iv), recovery of the half-wave bound for radial
Schwartz inputs through the radial-kernel representation.  Then (1.5).

At 2026-09-02T14:12:36-04:00 U1.I was completed and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0; the only matches for `sorry` or `admit` in the
module are the English word "admits" inside two docstrings.  Added
`brrs_lintegral_countProd_eq_sum`, `brrs_lintegral_radialProfile_rpow_eq` and
`brrs_discreteLpNorm_highExponent_le`, and the row above is now marked
complete.

The Section 5 stream's next selected item is (1.5), the radial upper estimate
in Theorem 1.1, which joins the subcritical Proposition 5.1 range with this
high-exponent interpolation.

At 2026-09-02T15:07:41-04:00 the subcritical half of (1.5) was proved and a
fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.

Two structural points had to be settled first, and both are recorded because
they are needed again for the supercritical half.

The source statement is quantified over every frequency level, while both
Proposition 5.1 and U1.I hold only beyond a threshold.  The gap is closed by
a bound valid at every level: Young's inequality against the kernel's `L^1`
norm, with the packet cardinality paid in full.  Its exponent is far worse
than the sharp one, but it applies to the finitely many levels below any
threshold, so the constant absorbs them.  The kernel `L^1` bound needed for
this had to be assembled for every dimension at least two, by joining the
recorded planar square-root bound to the recorded higher-dimensional
half-density bound.

The exponent bookkeeping for the remaining range is as follows.  For
`p >= 2d/(d-1)` the penalty satisfies `p s_p = (d-1)(p/2 - 1) >= 1`, and
`alpha <= nu_E(alpha)` always holds, so the target exponent
`nu_E(p s_p)/p` is at least `s_p = (d-1)(1/2 - 1/p)`.  U1.I at a subcritical
`p_0` with `q` slightly above `nu_E(p_0 s_{p_0})` gives the exponent
`(q + eps)/p + (1 - p_0/p)(d-1)/2`, which is at most `s_p + eps'` exactly
when `q + eps <= p_0 s_{p_0} + p eps'`.  Since `nu_E(alpha) <= 1` for every
penalty `alpha` in `[0,1]`, and `p_0 s_{p_0}` increases to `1` as `p_0`
increases to the critical exponent, choosing `p_0` close enough to critical
makes that inequality available with room to spare.  The two ingredients
`le_brrsLegendreAssouadFunction_of_nonempty` and
`brrsAssouadLegendreTransform_le_one_of_nonneg_of_le_one` are already
proved in the Legendre--Assouad module.

At 2026-09-02T15:52:18-04:00 (1.5) was completed and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.

What remains for Theorem 1.1 is now exactly two things, and neither is an
upper-bound estimate.

First, the Layer 13 target is the joint package
`BRRSTheoremOneWithSharpnessStatement`, whose upper clause is
`UniformEstimateAtExponent` for an `L^p` realization of the half-wave, over
every a.e.-radial `MemLp` input, whereas (1.5) is the estimate on radial
Schwartz data.  Passing from one to the other is a density and continuity
step for the realization, not a new estimate; it is the same interface issue
that the `HasBRRSFiniteTimeRadialProfileSimpleBoundTransfer` predicates were
introduced for, now on the output side, and it must be discharged rather than
assumed.

Second, the sharpness clause needs U3.S from the Section 3 lower-bound
stream, whose active item is still (3.3), the literal Bessel asymptotic.  That
stream is untouched by this work.

At 2026-09-02T16:38:05-04:00 the Section 3 stream resumed on its selected
item (3.3) and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrsBesselPoissonTerm`,
`continuousOn_brrsBesselPoissonTerm`, `brrs_tsum_brrsBesselPoissonTerm`,
`brrs_integral_brrsBesselPoissonTerm`, `brrs_integrableOn_betaKernel_Ioo`,
`brrs_integrableOn_brrsBesselPoissonTerm` and
`brrs_integral_norm_brrsBesselPoissonTerm_le`.

The route to the missing bridge is now fixed and is recorded so that the
remaining steps are unambiguous.  The paper's asymptotic is stated for the
ordinary `J_{(d-2)/2}`, while the development's spherical Fourier transform
carries the repository normalization; the two are related through the
classical Poisson--Beta representation of `J_nu`.  Its coefficient arithmetic
was already available in `RadialFourierTransform`
(`real_betaIntegral_eq_gamma_mul_div`, `ordinaryBessel_beta_moment`,
`ordinaryBessel_gamma_half_factorial_identity`,
`ordinaryBessel_beta_coefficient`), and what has now been proved is the
analytic half: the cosine expansion of the Poisson--Beta integrand converges
to it pointwise on the open unit interval, each term is integrable there with
the Beta value as its integral, and the integrated norms are dominated by a
cosine series times a fixed Beta integral.

Remaining for (3.3), in order: interchange the series with the integral
through `integral_tsum_of_summable_integral_norm`, which the last bound makes
available, to obtain the Poisson representation of `ordinaryBesselJ`; prove
the sphere-slice identity expressing `surfaceFourier` in dimension at least
two as the equatorial one-dimensional cosine integral; combine the two to get
the literal `J_{(d-2)/2}` bridge; and package the two travelling waves with
the `O(|u|^{-3/2})` remainder against the already-proved all-parity
decomposition `exists_brrs_surfaceFourier_threeWave_leading_remainder_all_dimensions`.

At 2026-09-02T17:09:44-04:00 the Poisson--Beta representation was proved and
a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrs_summable_even_pow_div_factorial` and
`brrs_ordinaryBesselJ_poisson_repr`: for every nonnegative order and every
positive argument,

  J_nu(x) = (x/2)^nu / (sqrt(pi) Gamma(nu + 1/2))
              times the integral over the open unit interval of
              u^(-1/2) (1-u)^(nu - 1/2) cos(x sqrt u).

This is the classical Poisson representation, in the substituted variable
`u = t^2`, and it is the first half of the missing bridge for (3.3): the
paper's asymptotic is stated for the ordinary Bessel function, and this
identity expresses that function as a one-dimensional cosine integral of
exactly the shape the spherical Fourier transform produces.  Mathlib has no
Bessel functions, so the series definition in `RadialFourierTransform` and
this representation are the whole of the available theory; nothing here is
assumed.

The second half is the sphere-slice identity: in dimension at least two the
surface Fourier transform of a vector equals a constant times the same
one-dimensional cosine integral with `nu = (d-2)/2` evaluated at the vector's
norm.  That is the next step in this stream.

At 2026-09-02T17:41:29-04:00 the sphere-slice half of the (3.3) bridge was
proved and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrsSliceDensity` with its continuity and
evenness, `brrs_surfaceFourier_succ_ordinary_integral` and
`brrs_surfaceFourier_succ_cos_integral`: in every ambient dimension at least
three, the surface Fourier transform equals the surface mass of the equatorial
sphere times twice the integral over the unit interval of the height density
against the cosine of the frequency times the height.

The slicing itself was already available as
`surfaceFourier_succ_height_integral`, which records the transform as an
integral of the exponential against the height density in the withDensity
form.  What was missing, and is proved here, is its conversion to an ordinary
integral and the reflection of the height variable that turns the exponential
into a cosine on half the interval.  The density is exactly
`(1 - t^2)^((d-2)/2)` in the ambient dimension `d+1`, which is the Poisson
kernel of order `nu = (d-1)/2`, that is `(D-2)/2` in ambient dimension `D`:
this is the order at which the paper's Bessel display is stated, so the two
halves of the bridge are now stated at matching order.

Remaining for (3.3): substitute the square of the height to bring the slice
integral to the Poisson variable, combine with
`brrs_ordinaryBesselJ_poisson_repr` to obtain the literal ordinary-Bessel
bridge, and package the two travelling waves with the remainder against the
already-proved all-parity decomposition.

At 2026-09-02T18:26:53-04:00 the ordinary-Bessel bridge required by (3.3) was
proved and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrsSliceDensity_eq_rpow`,
`brrs_image_sq_Ioo`, `brrs_slice_cos_integral_eq_poisson` and
`brrs_surfaceFourier_succ_eq_ordinaryBesselJ`.

The bridge states that in every ambient dimension `d+1` with `d >= 2`, for a
nonzero frequency,

  surfaceFourier (d+1) xi
    = surfaceMass d * sqrt(pi) * Gamma(d/2) / (pi ||xi||)^((d-1)/2)
        * J_{(d-1)/2}(2 pi ||xi||),

where `J` is the ordinary Bessel function of the first kind as defined by its
classical series.  The order `(d-1)/2` is `(D-2)/2` in the ambient dimension
`D = d+1`, which is the order at which the paper states its asymptotic
display.  This closes the gap the (3.3) row recorded as necessary: the
identification of the repository's normalized surface Fourier transform with
the paper's ordinary Bessel function is now proved rather than assumed, and it
rests only on the Poisson--Beta representation proved here and the sphere
slicing already recorded in `SurfaceMeasureDecay`.

What remains for (3.3) is the explicit two-wave phase packaging: expressing
the paper's outgoing and incoming waves with the `O(|u|^{-3/2})` remainder
against the already-proved all-parity decomposition
`exists_brrs_surfaceFourier_threeWave_leading_remainder_all_dimensions`, now
that the Bessel normalization on both sides is identified.

At 2026-09-02T19:03:11-04:00 the conversion core for the two-wave packaging
was proved and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrs_amplitude_error_of_scaled` and
`brrs_threeWave_error_bound`.

These are the arithmetic step the packaging needs in every parity case.  The
development's stationary-phase decomposition states each endpoint asymptotic
in a scaled form: a factor carrying the decay multiplies the amplitude, and
the difference from the literal leading coefficient is bounded by one inverse
frequency.  The paper's display instead exhibits two travelling waves with the
decay in front and a remainder one further order down.  The first lemma moves
the scale into the error, which is exactly where the extra order comes from;
the second adds the two endpoint errors and the middle term, using that both
phases have unit modulus.

What remains for (3.3) is to instantiate this against each parity clause of
`exists_brrs_surfaceFourier_threeWave_leading_remainder_all_dimensions` and
transport the result through the ordinary-Bessel bridge, together with the
planar bridge for ambient dimension two, whose slice is the angular form
`integral_comp_last_unitSurfaceMeasure_two` rather than the height form used
above.

At 2026-09-02T20:02:47-04:00 the planar half of the (3.3) bridge was proved
and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrs_cos_integral_sub_poisson`,
`brrs_angular_symmetry`, `brrs_image_cos_Ioo`,
`brrs_angular_cos_integral_eq_halfLine`,
`brrs_angular_sin_integral_zero`,
`brrs_angular_cos_integral_eq_besselJ_zero` and
`brrs_surfaceFourier_two_eq_ordinaryBesselJ`.

The circle needed separate treatment for two reasons, both now handled.  Its
slice is the angular meridian integral rather than a height integral, so the
substitution to the Poisson variable goes through the cosine, with the
Jacobian cancelling the inverse sine that the kernel produces; and its
Poisson exponent is `-1/2`, which the slice form of the density never
produces, so the substitution had to be proved for an arbitrary kernel
exponent.  The sine part of the angular exponential integrates to zero by
reflection about the right angle, leaving the cosine integral, which is
`pi` times the Bessel function of order zero.  The constant checks against
the total surface mass: at frequency zero both sides are the circumference.

The ordinary-Bessel identification of (3.3) is therefore complete in every
dimension at least two.  What remains for the row is the two-wave packaging:
instantiating `brrs_threeWave_error_bound` against each parity clause of
`exists_brrs_surfaceFourier_threeWave_leading_remainder_all_dimensions` and
transporting the result through these two bridges.

At 2026-09-02T21:04:56-04:00 the two-wave packaging of (3.3) was proved for
the circle and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `exists_brrs_ordinaryBesselJ_zero_twoWave`:
there are constants such that for every frequency at least one, the ordinary
Bessel function of order zero differs from the inverse square root times the
two unit-modulus carriers by at most a constant times the inverse three-halves
power.  This is the literal shape of the paper's display, at the order
`(d-2)/2 = 0` of ambient dimension two.

The derivation is the one the conversion core was built for: the decomposition
supplies the two endpoint amplitudes in scaled form and the middle amplitude
with arbitrary rapid decay, the scale is moved into the error, and the whole
identity is transported through the planar bridge.  Choosing the frequency as
`u/(2 pi)` on a unit ray makes the decomposition's frequency variable exactly
`u`.

Remaining for (3.3): the same packaging for the two nonplanar parity clauses.
Their algebra has been checked in advance and comes out at the same shape: in
ambient dimension `2n+4` the decomposition carries the extra factor
`((2u) i)^(n+1)` together with the square root, and the bridge contributes
`(u/2)^(n+1)`, so the powers of `u` cancel to leave the inverse square root
with the remainder one order below; in ambient dimension `2n+3` the square
root is absent from the decomposition and the bridge contributes
`(u/2)^((2n+1)/2)`, and the powers again leave exactly the inverse square
root.

At 2026-09-02T22:11:33-04:00 the packaging lemma was proved and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added `brrs_twoWave_package`.

Writing the even nonplanar case directly made clear that the three parity
cases differ only in their arithmetic, not in their structure, and that
repeating the structural argument three times invites exactly the kind of
bookkeeping error the ledger is meant to prevent.  The lemma therefore states
the passage once: from a three-wave representation with scaled endpoint
asymptotics, unit-modulus carriers, and the two constant identities that turn
scaled coefficients into travelling-wave coefficients, it concludes the
two-wave display with the three errors added.  One further fact the direct
attempt exposed is that the incoming clause of the nonplanar decompositions
carries the negated weight, not the same weight as the outgoing clause, so the
lemma takes the two weights separately.

Remaining for (3.3): instantiate the packaging lemma in the even and odd
nonplanar cases, each of which needs its own constant identity and its own
comparison of the resulting rate with the inverse three-halves power.

At 2026-09-02T23:07:12-04:00 the even nonplanar case of the (3.3) packaging
was proved and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Added
`exists_brrs_ordinaryBesselJ_even_twoWave`: for every `n`, the ordinary
Bessel function of order `n+1` differs from the inverse square root times two
unit-modulus carriers by at most a constant times the inverse three-halves
power, for every frequency at least one.  The order `n+1` is `(D-2)/2` in the
ambient dimension `D = 2n+4`, which is the even nonplanar case of the source
display.

The cancellation is exact and worth recording: the bridge contributes the
prefactor `(u/2)^(n+1)`, the decomposition's weight contributes
`(2u)^(n+1)`, and their quotient is the constant `4^(-(n+1))`, independent of
the frequency.  That is why the two-wave display has the same inverse square
root in every dimension.  The middle term needed the decay order `N = n+3`,
one order beyond the leading power, so that after multiplication by the
prefactor it is still below the inverse three-halves power.

Remaining for (3.3): the odd nonplanar case, whose decomposition carries the
same weight but no square root, so the bridge prefactor
`(u/2)^((2n+1)/2)` is what supplies the half power.

At 2026-09-03T00:02:41-04:00 (3.3) was completed and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0; the only matches for `sorry` or `admit` in the
module are the English word "admits" in two docstrings.  Added
`exists_brrs_ordinaryBesselJ_odd_twoWave`, completing the third parity case.

In the odd nonplanar dimensions the decomposition carries no square root, so
the half power of the display comes from the bridge prefactor
`(u/2)^((2n+1)/2)` rather than from the decomposition.  Rescaling the weight
by the inverse square root puts the estimate into the form the packaging
lemma takes, after which the arithmetic is the same cancellation as in the
even case: the surviving constant is frequency-independent and the remainder
sits one full order below the leading power.

The Section 3 stream's next selected item is (3.2), the packet-norm upper
bound, whose prerequisites U3.R, U3.P and (3.3) are now all complete.

At 2026-09-02T23:31:35-04:00 (3.2) was completed and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  The only `sorry`/`admit` grep hits in the module
remain the English word ``admits'' in two docstrings.

Note on timestamps: the (3.3) row and the entries just above it carry clock
times about ninety minutes ahead of the true Eastern time of that work; the
present entry and everything after it use the machine's Eastern clock, so
this entry is stamped slightly earlier than the (3.3) row it follows.  No row
ordering or dependency is affected.

Three things were established for (3.2), in dependency order.

First, the uniform two-wave form of (3.3):
`exists_brrs_surfaceFourier_twoWave` states that in every dimension at least
two there are constants with

  surfaceFourier d xi = |xi|^{-(d-1)/2} (c_out e^{-2 pi i |xi|}
      + c_in e^{2 pi i |xi|}) + O(|xi|^{-(d+1)/2})   for |xi| >= 1.

It is assembled from the three parity clauses of (3.3) by the single
transport lemma `brrs_surfaceFourier_twoWave_of_bridge`, which carries an
ordinary-Bessel two-wave display through an ordinary-Bessel bridge; the three
instantiations are the planar bridge, the odd-ambient bridge at Bessel order
`(2m+1)/2`, and the even-ambient bridge at order `m+1`.  This is the form in
which (3.3) is actually used downstream, and (3.4) will use it too.

Second, the two sharp norm inputs for the packet.  The Plancherel side is
immediate: the packet's Fourier transform is its annular symbol, of modulus
at most a fixed Schwartz seminorm and supported in the ball of radius
`4/brrsFrequencyScale j`, so its square integral is at most a constant times
`2^{jd}` by the ball-volume scaling.  The sup-norm side is where the work is,
and it splits at `|x| = 1/2`.  Away from the origin the two-wave form gives
the integrand of the radial inversion the majorant
`rho^{(d-1)/2}|Phi(c rho)| + rho^{(d-3)/2}|Phi(c rho)|` after the radial
Jacobian is absorbed, and the annular moment lemma
`exists_brrs_annularSymbol_moment_le` -- finiteness and exact scaling of
`int rho^a |Phi(c rho)| d rho` for every real `a` -- turns this into
`2^{j(d+1)/2}`.  Near the origin the two-wave asymptotic is unavailable,
because the argument `rho |x|` of the surface transform is not large there;
instead the sphere is integrated first.  Unfolding `surfaceFourier` and
applying Fubini gives the exact identity

  g_I(x) = int_{S^{d-1}} int_0^infty rho^{d-1} Phi(c rho)
              e^{-2 pi i rho (t_I - <omega,x>)} d rho d omega,

recorded as `brrs_radialHalfWaveTestPacket_eq_sphere_integral`, and the inner
integral is exactly a rescaled one-dimensional Fourier transform of the
weighted annular profile `u^{d-1} Phi(u)`
(`brrs_annularOscillatory_eq_fourier`).  The weighted profile is again
Schwartz (`exists_brrs_weightedAnnularSchwartz`: a real power weight may be
absorbed into an annular Schwartz profile, since the annulus avoids the
origin), so its transform decays rapidly, and for `|x| <= 1/2` and
`t_I >= 1` the phase is bounded below by `1/2`, which converts the decay into
a bound independent of the frequency level.  This is the only place where the
hypothesis `t_I >= 1` is used.

Third, the interpolation.  Choosing `p >= 2` and using the pointwise
inequality `|g|^p <= ||g||_infty^{p-2} |g|^2` gives
`int |g_I|^p <= C 2^{j((d+1)p/2 - 1)}`, whose `p`-th root is the printed
exponent `(d+1)/2 - 1/p`.  Both inputs are sharp, so the exponent is not
lossy; the conversion from the `p`-th power integral to the `L^p` seminorm is
the reusable `brrs_eLpNorm_le_of_integral_rpow_le`.

A design decision worth recording: no new packet was defined.  The paper's
`g_I` was already present in the development as
`brrsRadialHalfWaveTestPacket`, defined as the inverse Fourier transform of
the annular symbol back-propagated from the reference time, with its identity
with the annular half-wave kernel recorded at the point of definition.  All
of (3.2) is therefore a statement about the existing object, which keeps
(3.4) and (3.1) on the same datum.

The Section 3 stream's next selected item is (3.4), the
`T_t^- + T_t^+ + T_t^rem` decomposition, whose prerequisites U3.R, U3.P and
(3.3) are complete; it is independent of (3.2) and will reuse the uniform
two-wave form proved here.

At 2026-09-02T23:44:26-04:00 (3.4) was completed and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.

The decomposition is stated for the annular half-wave kernel of an arbitrary
annular cutoff `Psi` at an arbitrary time `s`, because that is exactly the
shape of the propagated Section 3 datum: the development already records that
the half-wave applied to the positive radial test packet is the relative-time
kernel for the positive `TT*` cutoff.  So one identity serves both the
abstract and the concrete form, and the concrete instantiation is a two-line
corollary.

Three definitions were added, matching the source's three terms.
`brrsSectionThreeWaveIntegral d Psi j v` is the one-dimensional annular wave
integral `int_0^infty rho^{(d-1)/2} Psi(c rho) e^{2 pi i rho v} d rho` at the
frequency scale `c = brrsFrequencyScale j`; the travelling terms
`brrsSectionThreeFocusingTerm` and `brrsSectionThreeSpreadingTerm` are
`|x|^{-(d-1)/2}` times this integral at `v = s - |x|` and `v = s + |x|`, with
the leading constants of (3.3) in front; and
`brrsSectionThreeRemainderTerm` is the radial integral of the two-wave error
`surfaceFourier d (-rho x) - (rho|x|)^{-(d-1)/2}(c_out e^{-2 pi i rho |x|}
+ c_in e^{2 pi i rho |x|})` against the kernel's radial profile.  The
remainder is therefore intrinsic, not defined as a difference of the other
terms; the identity is what has to be proved, and its content is that the
three integrals converge separately.

Convergence is where the work is.  Both travelling integrands are dominated
by the annular radial moment of order `(d-1)/2` and the remainder integrand
by the sum of the moments of orders `d-1` and `(d-1)/2`, using only the
trivial bound `|surfaceFourier| <= surfaceMass` and the triangle inequality
on the two-wave term; all three follow from the annular moment lemma proved
for (3.2), packaged here as the reusable `brrs_integrableOn_annular_dominated`.
The pointwise algebra -- absorbing the radial Jacobian into the half power and
combining the surface phase with the profile phase -- is a single
`linear_combination` over the three rewriting identities, which avoids the
fragile large rewrites.

No frequency threshold and no hypothesis on the leading constants is needed
for (3.4): the identity is exact for every `c_out`, `c_in`, every `j`, every
`s`, and every `x != 0`.  The two-wave constants of (3.3) and the threshold
`2^j >= 16 pi` will enter in (3.5)--(3.7), where the terms are estimated.

The Section 3 stream's next selected item is (3.5), the main-term lower bound
on `D_t`, whose prerequisites U3.P and (3.4) are now complete.

At 2026-09-03T00:06:16-04:00 (3.5) was completed and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.

Two things had to be settled for (3.5), and both are recorded because they
change what earlier rows provide.

First, the nonvanishing of the two-wave leading constants.  The lower bound
on the focusing term is `|c_out| |x|^{-(d-1)/2} |W(s - |x|)|`, so it is
vacuous unless `c_out != 0`, and the existential form of (3.3) proved earlier
discarded that information.  The constants are explicit in the three
constructions, so the three clauses of (3.3)
(`exists_brrs_ordinaryBesselJ_zero_twoWave`,
`exists_brrs_ordinaryBesselJ_even_twoWave`,
`exists_brrs_ordinaryBesselJ_odd_twoWave`), the transport lemma
`brrs_surfaceFourier_twoWave_of_bridge` and the uniform form
`exists_brrs_surfaceFourier_twoWave` were all strengthened to carry
`c_out != 0` and `c_in != 0`.  The additional content is elementary once the
right facts are located: the leading constant is a positive multiple of
`surfaceMass` times a stationary leading coefficient times a stationary
carrier, the coefficients are nonzero by the recorded
`brrsEvenQuadraticLeadingCoefficient_ne_zero` and
`brrsOddQuadraticLeadingCoefficient_ne_zero`, and the carrier is the endpoint
profile's value at the stationary point times the Fresnel constant, which the
development already evaluates in closed form as
`(sqrt(pi/2))(1+i)/2`.  Its nonvanishing is now `brrs_quadraticFresnelLimit_ne_zero`,
and the two carrier corollaries are
`brrs_evenQuadraticBaseCarrier_smoothEndpointProfile_ne_zero` and
`brrs_evenQuadraticBaseCarrier_planarEndpointProfile_ne_zero`.  No estimate
was weakened; only conclusions were added.

Second, the positivity of the propagated density.  The propagated packet
carries the cutoff `Phi * conj Phi`, and the development had already isolated
this as `brrsTTStarAnnularCutoff` precisely so that the propagated density is
nonnegative even for a complex-valued cutoff.  That is exactly what the lower
bound needs: `brrs_ttStarAnnularCutoff_symbol_eq_normSq` identifies the
positive cutoff's profile with the squared modulus, so the zero-phase wave
integral is the exact moment `int rho^{(d-1)/2} |Phi(c rho)|^2 d rho`, which
is strictly positive.  Both the exact scaling of that moment
(`brrs_annular_moment_scaling`, an equality, unlike the inequality used for
(3.2)) and its strict positivity (`brrs_annularSymbol_normSq_moment_pos`) are
proved here; positivity uses only continuity of the profile and its
nontriviality, through a shrinking-interval argument.

The phase estimate is first order and needs no frequency threshold: on the
shell the phase satisfies `2 pi rho |v| <= 1/8` for every `rho` in the
annulus, so `|e^{i theta} - 1| <= 2|theta|` applies, and the resulting error
is at most a quarter of the main moment because `u^{(d+1)/2} <= 4 u^{(d-1)/2}`
on the support of the cutoff.  The conclusion is therefore
`(3/4) c^{-(d+1)/2} N_0 <= |W(v)|`, uniformly in the frequency level.

The Section 3 stream's next selected item is (3.6), the `T_t^+` error
estimate, whose prerequisites U3.P and (3.4) are complete.

At 2026-09-03T00:15:33-04:00 (3.6) and (3.7) were completed and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  The same check covers the restatement of (3.5) in
relative form.

The three estimates are now stated in a shape that composes.  Each term of
the (3.4) decomposition carries an explicit radial weight, and the estimates
keep it:

  |T^-| >= c_1 |x|^{-(d-1)/2} 2^{j(d+1)/2}      when 2^j |s - |x|| <= 1/32,
  |T^+| <= C   |x|^{-(d-1)/2} 2^{j(d+1)/2} (1 + 2^j |s + |x||)^{-N},
  |T^rem| <= C |x|^{-(d+1)/2} 2^{j(d-1)/2}      when 2^j |x| >= 8 pi.

So the ratio of the spreading term to the focusing term is at most a constant
times `(1 + 2^j|s + |x||)^{-N}`, and the ratio of the remainder to the
focusing term at most a constant times `(2^j |x|)^{-1}`, both with no residual
power of `|x|`.  That is precisely the form (3.1) needs: on the source shell
`|x|` is comparable to `|t - t_I|`, which is comparable to the interval length
`R`, so both ratios are small exactly when `R` is large compared with the mesh
`2^{-j}`, which is the regime of the sharpness argument.  An earlier version
of (3.5) bounded the radial weight below by `4^{-(d-1)/2}` using `|x| <= 4`;
that form would have forced (3.1) to absorb a power of `R` into the decay, so
it was replaced by the weighted form before (3.6) was proved.

(3.6) does not integrate by parts.  Instead
`brrs_annularOscillatory_realWeight_eq_fourier` writes the travelling wave
integral as `c^{-(d+1)/2}` times the Fourier transform of the weighted annular
profile at the rescaled phase `v/c`, and the transform of a Schwartz function
decays rapidly.  The weighted profile is Schwartz by the absorption lemma
proved for (3.2).  This is the same mechanism as the source's integration by
parts, in the form that is available here.

The Section 3 stream's next selected item is (3.1), the localized lower
bound, whose prerequisites (3.2), (3.4), (3.5), (3.6) and (3.7) are now all
complete.

At 2026-09-03T00:30:15-04:00 (3.1) was completed and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.

Section 3 is now closed except for the conversion U3.S.  The chain runs
(3.3) -> (3.4) -> (3.5), (3.6), (3.7) -> (3.1), with (3.2) supplying the
packet norm, and every step is proved for the development's own datum
`brrsPositiveRadialHalfWaveTestPacket`, whose propagation is the relative-time
annular half-wave kernel for the positive `TT^*` cutoff.

Three things are worth recording about (3.1).

First, the threshold.  The source's smallness of the errors is quantitative
here: the constant `K` is built explicitly from the three constants of (3.5),
(3.6) and (3.7), and the hypothesis is `2^j R >= K`.  That is the only regime
in which the localized bound is claimed, and it is the regime the sharpness
argument uses, since there `R = delta^theta` with `theta < 1` and
`delta = 2^{-j}`, so `2^j R = delta^{theta - 1}` tends to infinity.

Second, the choice `N = 1` in (3.6).  Because the errors only have to be
beaten by a constant factor, and because the phase is already large
(`2^j|s + |x|| >= K/2`), a single power suffices; no large-`N` bookkeeping is
needed anywhere.

Third, the shell volume.  It is computed exactly, not estimated: the shell is
the difference of a closed ball and an open ball, the difference of measures
is the difference of the `d`-th powers times the volume of the unit ball, and
the elementary inequality `y^{m}(x - y) <= x^{m+1} - y^{m+1}` turns that into
`(a - w)^{d-1} \cdot 2w` times the unit-ball volume.  With `a >= R/2` and
`w <= R/32` this is at least `(R/4)^{d-1} 2^{-j}/16` times that volume.

The Section 3 stream's next selected item is U3.S, the conversion of (3.1) to
the sharpness of (1.5) up to `epsilon`, whose prerequisites U1.Setup, (1.4)
and (3.1) are now all complete.  That step is where the entropy of `E` and the
`limsup` in the definition of the Legendre--Assouad function enter, together
with the packet norm (3.2).

At 2026-09-03T00:58:24-04:00 U3.S was completed and a fresh direct
`lake env lean LeanSpherical/Auto/Spherical/FractalDilations/BRRS.lean`
check exited with code 0.  Section 3 is now closed: (3.1)--(3.7), U3.P, U3.R
and U3.S are all complete.

The conversion has three moving parts, and each is recorded because it
changes what the earlier rows deliver.

First, the packet identification.  (3.1) propagates the positive packet, whose
cutoff is conjugated, while (3.2) was proved for the ordinary packet.  The
conjugated annular cutoff `brrsConjAnnularCutoff` closes the gap: the adjoint
half-wave symbol of a cutoff is the forward half-wave symbol of the conjugated
cutoff, so `brrsPositiveRadialHalfWaveTestPacket Φ j t_I` is literally
`brrsRadialHalfWaveTestPacket (brrsConjAnnularCutoff Φ) j t_I`, and (3.2)
applies verbatim to the datum used in (3.1).

Second, the sign-free form of (3.1).  U3.P supplies the reference time as one
of the two endpoints of the interval, so the sampled times may lie on either
side of it, and the focusing and spreading terms of (3.4) exchange roles
accordingly.  The pointwise lower bound is therefore stated with the
hypothesis `R/2 <= |t - t_I| <= R` and proved by cases on the side, with the
algebraic step factored out as `brrs_norm_lower_of_threeTerm`.  This replaced
the earlier sign-restricted form of the (3.1) row, which would have needed a
duplicated mirror proof.

Third, the geometry of the test.  The entropy witness gives an interval of
length `R >= delta` and a `delta/2`-separated subset of `E` inside it, while
(3.1) needs `2^j R >= K` and `t_I >= 1`.  Both are arranged at once: the
interval is enlarged to `R'' = 4 max(R, K 2^{-j})`, which satisfies
`2^j R'' >= 4K` and `R'' <= 4(1+K) R` (because the chosen dyadic level has
`2^{-j} < delta/2 <= R/2`), and the reference time is placed at
`(a + R) + 3R''/4`, to the right of the interval, which is at least one
because the interval meets `E \subseteq [1,2]`.  Every sampled time then has
`|t - t_I| \in [R''/2, R'']`, so (3.1) applies to the whole witness packet at
once, and the resulting weighted cardinality bound contradicts the witness's
entropy lower bound as soon as `2^{j(q - ps)}` exceeds a fixed constant.

What remains for Theorem 1.1 is the Layer 13 join: the upper clause of
`BRRSTheoremOneWithSharpnessStatement` is `UniformEstimateAtExponent` for the
canonical realization over every a.e.-radial `MemLp` input, whereas (1.5) is
the estimate on radial Schwartz data.  That passage is a density and
continuity step for the realization, not a new estimate, and it is the last
open item in the chain; the sharpness clause is now available on the whole
range `p >= 2` from U3.S.
## Theorem 1.1: the Layer 13 join (2026-09-03T01:49:30-04:00)

The last open item was the passage from (1.5), the estimate on radial Schwartz
data, to the upper clause of `BRRSTheoremOneWithSharpnessStatement`, which asks
for the same estimate for the canonical realization on every a.e.-radial `MemLp`
input.  The conditional transfer principle
`uniformEstimateAtExponent_of_schwartzCore_of_radialSchwartzApproximation` had
been in place since Layer 12 with two explicit hypotheses; both are now proved,
so the principle applies unconditionally and Theorem 1.1 follows.

Output continuity (`brrs_hasRadialSchwartzCoreConvergence`) is the easier half.
The canonical realization is convolution against a fixed Schwartz kernel, so
Young's inequality for that kernel -- already available as
`brrs_eLpNorm_schwartz_convolution_le_of_memLp` -- bounds the difference of
outputs by a constant times the difference of inputs in $L^p$.  Summing the
finitely many sampled times gives continuity of the discrete norm, hence
convergence along any $L^p$-convergent sequence of radial Schwartz inputs.

Density (`brrs_hasRadialSchwartzLpApproximation`) is the substantive half.  The
ambient Schwartz density theorem does not respect the radial subspace, so the
approximants are built by hand in two steps, and both steps are arranged to be
radial by construction.

The mollifier is radial because it is a one-dimensional `ContDiffBump`
composed with the *squared* norm: `brrsRadialBump d delta x = B(||x||^2/delta^2)`.
Using the squared norm rather than the norm keeps the composition smooth at the
origin, which is exactly where a norm-composed profile would fail to be smooth;
the bump's `rIn = 1/2`, `rOut = 1` then give a function that is one on
`||x|| <= delta/2`, vanishes for `||x|| >= delta`, and is radial by inspection.
Normalizing by its integral, which is positive because the function is one near
the origin, yields `exists_brrs_radial_mollifier`.

The mollification error is estimated by the classical Lipschitz argument, not by
an approximate-identity limit: a smooth compactly supported comparison function
`g` is Lipschitz with constant `C = sup ||Dg||`
(`exists_brrs_lipschitz_of_contDiff_of_hasCompactSupport`), so the pointwise
error `|g - psi_delta * g|` is at most `C delta` everywhere and vanishes off a
fixed compact set, whence its $L^p$ norm is at most `C delta |K|^{1/p}`
(`brrs_eLpNorm_le_of_bound_of_support`).  Choosing `delta` after `C` and the
volume factor makes this term as small as required.  The three-term split
`f - psi*f = (f - g) + (g - psi*g) + (psi*g - psi*f)` is closed by
`hf.exist_eLpNorm_sub_le` on the first term, the Lipschitz estimate on the
second, and Young's inequality with `int |psi| = 1` on the third; radiality of
`psi*f` comes from `brrsConvolution_isRadial` applied to a norm-radial
representative of `f`, which is available because `IsAERadial` is an a.e.
equality with a genuinely radial function and `convolution_congr` only needs
that.

The truncation step then costs nothing extra.  `exists_brrs_radial_mollified_close`
is stated so as to return, besides the mollification `v`, the auxiliary function
`w = psi * (f - g)` of small $L^p$ norm together with a radius `Rv` beyond which
`v` and `w` agree -- they agree because `psi * g` has compact support inside
`B_{Rv}`.  Cutting `v` off with the radial bump at scale `2 Rv`, which is one on
`B_{Rv}`, therefore changes `v` only where `v = w`, so the truncation error is
pointwise dominated by `|w|` and its $L^p$ norm is bounded by that of `w`.  The
truncated function is smooth, compactly supported and radial, hence a radial
Schwartz function via `HasCompactSupport.toSchwartzMap`, and the total error is
`eps`.  Running this with `eps = 1/(n+1)` and `Lp.tendsto_Lp_iff_tendsto_eLpNorm`
produces the convergent sequence the transfer principle expects.

Two points of the design are worth recording because they are what makes the
argument short.  Returning `w` and `Rv` from the mollification lemma is what
removes any need for a tail estimate at the truncation step: without it one
would have to know that `v` itself is small far away, which is true but requires
a separate argument.  And bounding the mollification error by the Lipschitz
oscillation on a fixed compact set, rather than invoking an approximate-identity
theorem, avoids needing continuity of translation in $L^p$, which the
development does not have.

With this, every row of the ledger that Theorem 1.1 depends on is complete, and
the theorem itself is `brrsTheoremOneWithSharpnessStatement_of_two_le`.  The two
rows still marked `not started`, U2.Q and Corollary 1.3, are outside its
dependency cone.
