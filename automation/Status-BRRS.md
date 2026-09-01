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

Complete means a literal source item has a closed Lean proof. Complete with
qualification records a closed declaration plus its exact mismatch from the
paper, and is not an unqualified source milestone. In progress means the
currently available source-level target. Not started means no faithful proof
of that source item has begun. The initial audit timestamp was
2026-09-01T07:29:09-04:00. Timestamps change only when a row status changes.
Rows added by the first strict-DAG audit are timestamped
2026-09-01T09:57:45-04:00; rows added or split by the later direct-edge audit
are timestamped 2026-09-01T10:39:59-04:00.

## Layer 0 -- irreducible definitions and imported inputs

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| U1.Setup (unnumbered): annular cutoff $P_j$, $s_p$, and a $2^{-j}$-discretization $E_j$ | -- | complete with qualification | 2026-09-01T09:57:45-04:00 | BRRSAnnularCutoff, dyadicTimeScale, and IsDyadicDiscretization give the operational setup. The maximal-set wording is represented by a finite cover/separation interface rather than a literal maximality predicate. |
| (1.4): definition of the Legendre--Assouad function $\nu_E^\sharp$ | -- | complete with qualification | 2026-09-01T09:12:03-04:00 | brrsLegendreAssouadFunction, brrsLegendreAssouadProfile, brrsEntropyNumber, and brrsInterval encode the finite-scale expression. The EReal-limsup/toReal representative leaves the empty-set convention qualified. |
| U2.S (unnumbered): Assouad-spectrum and $\varphi(\delta,\theta)$ starting data | -- | not started | 2026-09-01T09:57:45-04:00 | Literal equality-scale $\gamma_E(\theta)=\dim_{A,\theta}E$, the source $\varphi$, and $\limsup_{\delta\to0}\varphi(\delta,\theta)=\gamma_E(\theta)$. Existing cover-exponent APIs do not isolate this full source package. |
| (1.7): Legendre-transform convention | -- | complete with qualification | 2026-09-01T09:12:03-04:00 | brrsAssouadLegendreTransform implements the instance needed on Icc 0 1, not a general arbitrary-closed-interval API. |
| (1.1) at $p=\infty$: fixed-time annular endpoint for interpolation | -- | complete with qualification | 2026-09-01T09:12:03-04:00 | exists_brrs_dyadicHalfWave_fixedTimeLInfinity_bound_dim_ge_three and exists_brrs_planarDyadicHalfWave_fixedTimeLInfinity_top_bound establish both dimension cases. This is only the endpoint used in Section 5. |
| U2.R (unnumbered external input): Rutar spectrum realization | -- | complete with qualification | 2026-09-01T08:23:44-04:00 | brrsRutarCorollaryB is available; it can be applied only after construction and verification of the candidate. |
| U2.Comp (unnumbered imported input): sequential compactness of $[0,1]$ | -- | complete with qualification | 2026-09-01T10:39:59-04:00 | Mathlib supplies compactness/subsequence extraction for the compact interval. The literal source-specialized extraction of the particular $(\theta_n)$ is still part of U2.K. |
| U3.R (unnumbered): radial Fourier inversion before (3.3) and (3.4) | -- | complete with qualification | 2026-09-01T09:57:45-04:00 | RadialFourierTransform.fourierInv_radial_eq_sphereFourier_integral and SurfaceMeasureDecay.fourierInv_radial_eq_surfaceFourier_integral give exact polar/surface-Fourier forms. The paper's explicit Bessel presentation remains part of the (3.3)/(3.4) route. |
| (3.3): Bessel asymptotic with $O(|u|^{-3/2})$ remainder | -- | in progress | 2026-09-01T07:56:08-04:00 | The all-order endpoint/Fresnel route now has genuine Abel-damped tail and limit lemmas, but has not yielded the literal all-dimensional Bessel statement. |
| U5.$\kappa$-def (unnumbered): definition of the local-counting coefficient $\kappa_{j,m}$ | -- | complete with qualification | 2026-09-01T10:39:59-04:00 | The finite-dyadic local-counting expression is represented by brrsDyadicKappa. This root row is only the definition; its entropy consequence is recorded separately below. |

## Layer 1 -- first consequences of the root data

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (1.8): Assouad-spectrum potential $\nu_E(\theta)$ | U2.S | complete with qualification | 2026-09-01T09:12:03-04:00 | brrsAssouadSpectrum and brrsAssouadPotential encode the potential and value at $\theta=1$, with the equality-scale convention qualified. |
| U2.C (unnumbered): continuity and compact maximum for the spectrum expression | U2.S | not started | 2026-09-01T08:40:03-04:00 | The source uses continuity of $\theta\mapsto(1-\theta)\gamma_E(\theta)$ to choose maximizers before (2.2) and (2.4). Existing weighted-spectrum continuity lemmas do not package this exact source assertion. |
| U2.Q (unnumbered): quasi-Assouad limit and domination | U2.S | not started | 2026-09-01T09:57:45-04:00 | This is $\gamma=\lim_{\theta\to1-}\gamma_E(\theta)$ and $\gamma_E(\theta)\leq\gamma$. brrsAssouadSpectrum_le_quasiAssouadDimension supplies only one formal comparison. |
| U2.L (unnumbered): decreasing limsup-realizing sequence $\delta_n$ | U2.S | not started | 2026-09-01T08:40:03-04:00 | The monotone extraction immediately before (2.3) has no exact Lean declaration. |
| U2.D (unnumbered): restricted-convex-duality setup $\nu=\tau^*$ for Theorem 1.2(ii) | (1.7) | complete with qualification | 2026-09-01T08:40:03-04:00 | The profile-conjugate/candidate API gives the construction, but not the source preparation under its printed name. |
| U3.P (unnumbered): the $I'$, $t_I$, $g_I$, $J_t$, and $D_t$ packet/separated-time geometry | U1.Setup | not started | 2026-09-01T09:57:45-04:00 | This is the interval selection, packet, shell geometry, and packing comparison around (3.1)--(3.4). Existing helpers do not yet form the literal source package. |
| U5.$\kappa$-ent (unnumbered): entropy control of $\kappa_{j,m}$ | U1.Setup, (1.4), U5.$\kappa$-def | complete with qualification | 2026-09-01T10:39:59-04:00 | brrsDyadicKappa_le_profile_of_isDyadicDiscretization and exists_tail_brrsDyadicKappa_le_inv_rpow_of_lt prove a finite-dyadic version. This is the final entropy-to-$\varepsilon$ input for (5.1), not an input to (5.2). |
| U5.C (unnumbered): discretization cardinality and $\kappa$ comparisons | U1.Setup, U5.$\kappa$-def | not started | 2026-09-01T09:57:45-04:00 | Packages $\#E_j\lesssim N(E,2^{-j})$, $N(E,2^{-j})\lesssim\max_m\kappa_{j,m}$, and base-scale comparison for endpoint cells. |
| U5.E (unnumbered): cited exterior fixed-time radial estimate | U1.Setup | not started | 2026-09-01T09:57:45-04:00 | The [19, Proposition 3.2] exterior-region bound used after (5.2), kept distinct from cardinality comparisons. |
| U5.R (unnumbered): radial kernel representation and power-weight conjugation for (5.3) to (5.4) | U1.Setup, U3.R | in progress | 2026-09-01T09:57:45-04:00 | The exact repo-normalized scalar kernel, its $ds$ half-wave identity, and the power conjugation now elaborate locally. It is not yet the literal printed $K_j$: Mathlib has no classical Bessel-$J$ API and, under the standard surface-Fourier/Bessel normalization plus $\lambda=2\pi\rho$, the integrand carries a $\lambda$ factor apparently absent from the arXiv display. That convention/erratum issue (and the $r,s>0$ comparison domain) must be resolved before this row can advance. |

## Layer 2 -- first source choices and kernel inputs

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| U2.Neg (unnumbered): $\alpha\leq0$ branch of Theorem 1.2(i) | (1.4), (1.7), (1.8) | complete with qualification | 2026-09-01T08:40:03-04:00 | brrsLegendreAssouadFunction_eq_zero_of_nonpos and the all-real transform theorem supply the formal nonempty-set endpoint branch. |
| (2.2): maximizing $\theta_\alpha$ for the lower half of (2.1) | (1.8), U2.C | not started | 2026-09-01T07:29:09-04:00 | The printed maximizer selection has not been isolated faithfully. |
| (2.3): $\varepsilon$-maximizing $\theta_n$ selection | U2.L | not started | 2026-09-01T07:29:09-04:00 | No Lean declaration records the exact approximate-supremum selection. |
| (2.7): $\gamma(\theta)=-\nu(\theta)/(1-\theta)$ candidate construction | U2.D | not started | 2026-09-01T07:29:09-04:00 | brrsProfileSpectrumCandidate has the matching formula, but not the source construction and hypotheses isolated as (2.7). |
| U5.K (unnumbered): four-sign Bessel/two-radius kernel majorant and rapid $\omega_j$ decay | U5.R | not started | 2026-09-01T09:57:45-04:00 | Preliminary components are not counted while U5.R is open: all-nine high--high blocks compile in $d\ge3$ and $d=2$, as do $d\ge3$ and planar low--high blocks. Global high--low reflection and low--low endpoint absorption must wait. |

## Layer 3 -- first analytic consequences

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| U2.K (unnumbered): convergent subsequence $\theta_n\to\theta_*$ | (2.3), U2.Comp | not started | 2026-09-01T08:40:03-04:00 | No source-faithful compactness extraction theorem exists. |
| U2.A (unnumbered): verification that the (2.7) candidate meets Rutar's hypotheses | U2.D, (2.7) | complete with qualification | 2026-09-01T08:40:03-04:00 | brrsProfileSpectrumCandidate_isRutarAssouadSpectrum proves the corresponding candidate package, though not under the source label. |
| (3.2): $\lVert g_I\rVert_p$ packet-norm upper bound | U3.R, U3.P, (3.3) | not started | 2026-09-01T07:56:08-04:00 | Requires the literal radial/Bessel input for its $L^\infty$ bound and the specified packet. |
| (3.4): $T_t^-+T_t^++T_t^{\mathrm{rem}}$ decomposition | U3.R, U3.P, (3.3) | not started | 2026-09-01T07:29:09-04:00 | Independent of (3.2), but requires radial inversion and the Bessel asymptotic. |
| (5.5): far-source $\mathrm{II}_n$ tail summation | U5.C, U5.K | not started | 2026-09-01T07:29:09-04:00 | Requires rapid kernel decay, the source Holder/decay calculation, and cardinality. |
| (5.6): terminal $\mathrm{I}_j$ estimate | U5.C, U5.K | not started | 2026-09-01T07:29:09-04:00 | Requires the four-sign kernel, cardinality comparison, and Young's inequality in the weighted reduction. |
| (5.7): initial-cell $\mathrm{I}_0$ estimate | (1.4), U5.C, U5.K | not started | 2026-09-01T07:29:09-04:00 | Its printed conclusion is $2^{j\nu_E^\sharp(ps_p)}$. It uses local packing and $ps_p\leq\nu_E^\sharp(ps_p)$, not U5.$\kappa$-ent merely to prove that displayed inequality. |
| U5.M (unnumbered): $0<m<j$ intermediate-cell estimate | U5.$\kappa$-def, U5.K | not started | 2026-09-01T08:23:44-04:00 | The change-of-variables/interval-decomposition estimate used with (5.6) and (5.7) for (5.8). |

## Layer 4 -- joins internal to the Section 2, 3, and 5 branches

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| U2.R-app (unnumbered): apply Rutar to the verified candidate | U2.R, U2.A | complete with qualification | 2026-09-01T08:40:03-04:00 | Packaged through brrsRutarCorollaryB and brrsProfileSpectrumCandidate_isRutarAssouadSpectrum; the printed (2.7)-based application is not isolated. |
| (2.4): left-limit spectrum comparison | U2.C, U2.K | not started | 2026-09-01T07:29:09-04:00 | No faithful standalone formalization of the displayed continuity comparison exists. |
| (3.5): main-term lower bound on $D_t$ | U3.P, (3.4) | not started | 2026-09-01T07:29:09-04:00 | Requires the $T_t^-$ term and specified annular geometry. |
| (3.6): $T_t^+$ error estimate | U3.P, (3.4) | not started | 2026-09-01T07:29:09-04:00 | Requires the $T_t^+$ term and integration-by-parts decay. |
| (3.7): remainder error estimate | U3.P, (3.4) | not started | 2026-09-01T07:29:09-04:00 | Requires the remainder term and annular integral bound. |
| (5.8): sum of the $\mathrm{I}_m$ estimates | U5.C, U5.M, (5.6), (5.7) | not started | 2026-09-01T07:29:09-04:00 | The base-scale/cardinality edge converts endpoint cells to the $\kappa_{j,m}$ sum. |

## Layer 5 -- late source estimates inside the three branches

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.5): eventual comparison of $\theta_n$ and $\theta_*$ | U2.K, (2.4) | not started | 2026-09-01T07:29:09-04:00 | Requires subsequential convergence and the left approximation. |
| (3.1): localized lower bound | (3.2), (3.4), (3.5), (3.6), (3.7) | not started | 2026-09-01T07:29:09-04:00 | Joins the three-term decomposition, packet norm, and main/error estimates. It does not use entropy to become sharp. |
| (5.4): weighted one-dimensional estimate | (5.5), (5.8) | not started | 2026-09-01T07:29:09-04:00 | The join of the far-source tail and full near-source sum. |

## Layer 6 -- reductions immediately before main displayed bounds

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.6): covering-number estimate at $\theta_*^-$ | U2.S, (2.5) | not started | 2026-09-01T07:29:09-04:00 | No exact source-labelled covering estimate exists. |
| U3.S (unnumbered): conversion of (3.1) to sharpness of (1.5) up to $\varepsilon$ | U1.Setup, (1.4), (3.1) | not started | 2026-09-01T09:57:45-04:00 | This is the entropy/limsup extraction after (3.1), not part of the proof of (3.1). |
| (5.3): compact spatial-region reduction | U5.R, U5.K, (5.4) | not started | 2026-09-01T07:29:09-04:00 | Radial inversion, the four-sign majorant, and (5.4) reduce the compact spatial integral. It does not use U5.E. |

## Layer 7 -- the two numbered main bounds

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.1): entropy/spectrum supremum identity for $\alpha\geq0$ | (2.2), (2.3), (2.4), (2.5), (2.6) | complete with qualification | 2026-09-01T07:29:09-04:00 | Its conclusion is proved for nonempty sets by brrsLegendreAssouadFunction_eq_brrsAssouadLegendreTransform_of_nonempty, but the displayed source substeps remain unisolated and are not thereby closed. |
| (5.2): $\kappa_{j,m}$ dyadic reduction | U5.E, U5.C, (5.3) | not started | 2026-09-01T07:29:09-04:00 | Joins the exterior estimate, the cardinality comparison, and the compact reduction; the entropy consequence is used only afterward in (5.1). |

## Layer 8 -- first named theorem/proposition conclusions

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| Theorem 1.2(i): $\nu_E^\sharp=\nu_E^*$ | U2.Neg, (2.1) | complete with qualification | 2026-09-01T07:29:09-04:00 | brrsTheoremOnePointTwoPartOne proves the identity for nonempty bounded sets; the empty-set case is not literal. |
| (5.1): Proposition 5.1 bound | U5.$\kappa$-ent, (5.2) | not started | 2026-09-01T07:29:09-04:00 | The same assertion as the named proposition; the last entropy-to-$\varepsilon$ reduction is the U5.$\kappa$-ent edge. |
| Proposition 5.1 | U5.$\kappa$-ent, (5.2) | not started | 2026-09-01T07:56:08-04:00 | Same assertion as (5.1), retained as a separate label with no proof-dependency edge between the two rows. |

## Layer 9 -- Theorem 1.2 consequences and realization

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (2.8): Assouad-spectrum Legendre representation | Theorem 1.2(i) | complete with qualification | 2026-09-01T07:29:09-04:00 | brrsLegendreAssouadFunction_eq_brrsAssouadLegendreTransform_of_nonempty gives the representation, with the nonempty-set qualification. |
| Theorem 1.2(ii): characterization of possible profiles | Theorem 1.2(i), U2.D, U2.R-app | complete with qualification | 2026-09-01T07:29:09-04:00 | brrsTheoremOnePointTwoPartTwo proves the nonempty realization package. The source (2.7) construction/application remains separately tracked and cannot be skipped in a faithful source-proof route. |

## Layer 10 -- quasi-Assouad identity tail

| Source item | Immediate prerequisites | Status | Status timestamp (ET) | Lean evidence / exact remaining point |
| --- | --- | --- | --- | --- |
| (1.9): $\nu_E^\sharp(\alpha)=\alpha$ for $\alpha\geq\dim_{qA}E$ | U2.Q, (2.8) | complete with qualification | 2026-09-01T08:40:03-04:00 | brrsLegendreAssouadFunction_eq_id_of_nonempty_of_quasiAssouadDimension_le establishes the identity-tail ingredient, with a formal nonempty-set qualification. |

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
