# Report — Roos–Seeger Theorem 1.1

Executive summary of the formalization of Thm. 1.1 of [arXiv:2004.00984](https://arxiv.org/abs/2004.00984).
Standing instructions: [`instructions-rs.md`](instructions-rs.md).

## Milestones (recorded only when fully finished)

1. **Cotlar–Stein almost orthogonality lemma** — `LeanSpherical/Auto/CotlarStein.lean`
   (460 lines, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`).
   `Auto.CotlarStein.norm_sum_le_of_cotlar_stein`: for a finite family `T i : E →L[𝕜] F` of
   operators between Hilbert spaces, if all column sums `∑ k, ‖(T i)* ∘ T k‖^(1/2)` and all row
   sums `∑ k, ‖T i ∘ (T k)*‖^(1/2)` are `≤ A`, then `‖∑ i, T i‖ ≤ A`.

2. **Calderón--Vaillancourt theorem** — `LeanSpherical/Auto/CalderonVaillancourt.lean`
   (~2450 lines, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`).
   * `Auto.CalderonVaillancourt.exists_cv_bound`: isotropic `S⁰_{0,0}` form.  For every `d` there
     is `c > 0` such that every symbol `a` on `ℝ^d × ℝ^d` with
     `‖∂_x^n a(·,ξ)‖ ≤ A` and `‖∂_ξ^n a(x,·)‖ ≤ A` for all `n ≤ 4d` satisfies
     `‖P_a f‖_{L²} ≤ c A ‖f‖_{L²}`, where `P_a f(x) = ∫ e^{2πi⟪x,ξ⟫} a(x,ξ) f(ξ) dξ`.
   * `Auto.CalderonVaillancourt.exists_cv_bound_aniso`: the anisotropic form actually used in the
     paper.  Same conclusion for `‖∂_x^n a(·,ξ)‖ ≤ A σ^n`, `‖∂_ξ^n a(x,·)‖ ≤ A τ^n`, `σ τ ≤ 1`.
   The proof is the classical one: a `ℤ^d × ℤ^d` smooth partition of unity in `x` and in `ξ`, an
   oscillatory estimate for the composed kernels obtained from the decay of `𝓕Ψ`, a Schur test,
   and the Cotlar--Stein lemma of Milestone 1.

3. **Section 4 of the paper: all three estimates for `S[F,b]`** —
   `LeanSpherical/Auto/Spherical/FractalDilations/RS.lean` (~8500 lines so far, `sorry`-free,
   axioms `[propext, Classical.choice, Quot.sound]`).  With `S[F,b](ξ,t) =
   ∫ e^{±2πit(|ξ-η|+|η|)} b(t,ξ,η) 𝓕F(ξ-η,η) dη` and `b` a `(j,m)`-adapted symbol:
   * `prop41` — the **trivial estimate**
     `∑_{t∈ℰ} ‖S[F,b](·,t)‖₂² ≤ 2^{12} B² 2^{2j-m} (#ℰ) ‖F‖₂²`, from Cauchy–Schwarz in `η` and the
     measure `≲ 2^{2j-m}` of the `η`-support.
   * `prop42` — the **almost orthogonality estimate**
     `∑_{t∈ℰ} ‖S[F,b](·,t)‖₂² ≤ c B² 2^{2j} N 2^{-m} ‖F‖₂²` for a strictly adapted symbol and an
     `ℰ` that meets each interval of length `2^{2m-j}` in at most `N` points.  Proved by a
     finite-dimensional Gram/Schur argument (avoiding `L²` duality) with the off-diagonal decay
     `(1 + 2^{j-2m}|t-t'|)^{-2}` obtained from two integrations by parts in polar coordinates
     against the phase `τ(ρ) = |ξ-ρθ| + ρ`.
   * `offdiag_Sop` — the **off-diagonal estimate**: if `F` is supported where
     `2^{l-m+19} ≤ |y-z| ≤ 2^{l-m+21}` and `|b| ≤ B`, `|∂_η b| ≤ B 2^{-(j-m)}`, then
     `‖S[F,b](·,t)‖₂ ≤ c B √(2^{3m}) 2^{-l} ‖F‖₂` with `c` absolute.  Proved by one integration by
     parts in a coordinate direction of `η` (with a globally smooth phase and a globally
     non-vanishing `Ψ`, so no case distinctions), a finite Neumann expansion of `1/Ψ` into `j+3`
     *separated* symbols plus a remainder, Plancherel for each separated term, and Cauchy–Schwarz
     in `w` over the annulus.

## In progress — `LeanSpherical/Auto/Spherical/FractalDilations/RS.lean`

Built strictly forwards along the paper's logical path; everything in the file is `sorry`-free and
depends only on `[propext, Classical.choice, Quot.sound]`.

* §4.1 complete: the sector `Θ_j` (`Theta`), the `(j,m)`-adapted symbol class (`IsAdapted`), the
  operator `S[F,b]` (`Sop`), the planar slab volume bound (`volume_slab_le`), the bound
  `|Θ_j ∩ (ξ - Θ_j) ∩ {∠(ξ,·) ≤ 2^{-m+5}}| ≤ 2^{2j-m+12}` (`volume_SuppSet_le`), and Plancherel
  on `ℝ⁴` (`lintegral_enorm_sq_fourier_schwartz`).
* §4.2 complete: **Proposition 4.1** (`prop41`), the trivial estimate
  `‖S[F,b]‖_{L²(ℝ²×ℰ)} ≤ c B 2^{j-m/2} (#ℰ)^{1/2} ‖F‖_{L²(ℝ⁴)}`.
* §4.3 (Proposition 4.2, almost orthogonality): all the machinery is in place and verified —
  * `integral_osc_ibp`, `norm_integral_osc_ibp_twice`: the one-dimensional non-stationary phase
    estimate (two integrations by parts gain `λ^{-2}`);
  * `integral_polar`, `enorm_integral_polar_le`: polar coordinates on the plane with the angular
    variable outermost;
  * `tauf`, `tauf1`, `tauf2`, `tauf3` with all derivative formulas, `tauf1_pos`, and the three
    quantitative bounds `tauf1_lower`, `tauf2_abs_le`, `tauf3_abs_le` (`τ' ≥ D/(2g²)`,
    `|τ''| ≤ (2/g)τ'`, `|τ'''| ≤ (6/g²)τ'`);
  * `bfun`, `bfun1`, `cfun` with `hasDerivAt_*` and `norm_cfun_le`
    (`|cfun| ≤ (4|A''|g⁴ + 24|A'|g³ + 72|A|g²)/D²`), and `norm_integral_radial_le`;
  * `sin_angle_eq`, `angle_le_of_cone`, `disc_eq`, `gf_eq_norm`: the planar angle geometry and the
    polar frame;
  * `schur_sum_le`: `∑_{t'∈ℰ}(1+|t-t'|/δ)^{-2} ≤ 12 sup_{|I|=δ} #(ℰ∩I)`;
  * `sum_norm_inner_sq_le`: the Gram/Schur almost-orthogonality lemma in a Hilbert space, and
    `sum_lintegral_SopK_le`: the `TT*` reduction of `‖S[F,b]‖_{L²(ℝ²×ℰ)}` to a Schur bound on the
    Gram matrix `∫ K_t(ξ,η) conj(K_{t'}(ξ,η)) dη`.
  * `cprod`, `cprod1`, `cprod2`, `ampl`, `ampl1`, `ampl2` with their `hasDerivAt_*` and
    `norm_*_le`: the amplitude `ρ ↦ ρ · b(t,ξ,ρθ) conj b(t',ξ,ρθ)` and its first two
    derivatives, from the symbol hypotheses;
  * `AngSet`, `mem_AngSet_of_mem_SuppSet`, `AngSet_subset`, `volume_AngSet_le`: the angular
    support meets only a set of angles of measure `≤ 2^{12-m}` (mean value theorem applied to
    `φ ↦ det(ξ, (cos φ, sin φ))`, whose derivative is `≳ 2^j` on the relevant interval).
  * `SuppSetStrict`, `IsStrictlyAdapted`, `XiData`, `AngSetStrict`, `disc_lower`: strict
    adaptedness forces the discriminant `D = ‖ξ‖² - ⟪ξ,θ⟫²` to be at least `2^{2j-2m-14}`, i.e.
    the phase is nondegenerate;
  * `RayData`, `OutAnn`, `ray_vanish`: the symbol and its first two radial derivatives vanish
    identically off the annulus `2^{j-1} ≤ |ρ| ≤ 2^{j+1}`;
  * `cfun_numeric_bound`: with `P = 2^j`, `Q = 2^m`, the twice-integrated-by-parts amplitude is
    bounded by `2^{47} B² Q⁴ / P`.
  What is left in §4.3 is only the final assembly: feeding the amplitude into
  `norm_integral_radial_le`, then the polar bound `enorm_integral_polar_le`, giving the
  Gram-matrix bound `≤ c B² 2^{2j-m}(1 + 2^{j-2m}|t-t'|)^{-2}`, and combining it with
  `schur_sum_le` and `sum_lintegral_SopK_le`.
* §4.3 **complete**: **Proposition 4.2** (`prop42`),
  `‖S[F,b]‖²_{L²(ℝ²×ℰ)} ≤ 12·2^61·B²·2^{2j-m}·N·‖F‖²_{L²(ℝ⁴)}` where `N` bounds the number of
  points of `ℰ` in an interval of length `2^{2m-j}` — the squared form of the paper's
  `c B 2^{j-m/2}(sup_{|I|=2^{-j+2m}}#(ℰ∩I))^{1/2}‖F‖`.  The route: `norm_gram_cfun_le` →
  `norm_radial_gram_le` / `norm_radial_gram_trivial_le` → `radial_gram_integral_eq` →
  `enorm_gram_integral_le` (the Gram bound `≤ 2^{61}B²2^{2j-m}(1+2^{j-2m}|t-t'|)^{-2}`) →
  `schur_sum_le` + `sum_lintegral_SopK_le`.
* §4.4 (Proposition 4.3, off-diagonal decay) in progress.  Complete so far:
  * `sliceSchwartz`, `lintegral_partial_plancherel`: the Fourier transform in the first planar
    variable is an `L²` isometry on `ℝ⁴`;
  * `sigmaLM`/`shearCLE`/`shearSchwartz`, `lintegral_comp_shear`,
    `lintegral_enorm_sq_shearSchwartz`: the shear `(y,z) ↦ (y, y-z)` turns the support hypothesis
    `|y - z| ≥ R` into a condition on the second variable;
  * `ee`, `fourier_shear_eq`, `Gf`, `fourier_pr_eq`: the `w`-representation
    `𝓕F(ξ-η, η) = 𝓕(G_ξ)(-η)` with `G_ξ(w) = ∫ e^{-2πi⟪y,ξ⟫}F(y, y-w) dy`;
  * `integral_deriv_eq_zero`, `integral_partial_fst_eq_zero`, `integral_partial_snd_eq_zero`:
    integration by parts on the plane (the integral of a coordinate partial derivative of a
    compactly supported `C¹` function vanishes);
  * `ph`, `phd`, `hasDerivAt_norm_line`, `hasDerivAt_ph`: the phase
    `⟪w,η⟫ + ε t(|ξ-η| + |η|)` and its directional derivative
    `⟪w,u⟫ + ε t ⟪η/|η| - (ξ-η)/|ξ-η|, u⟫`;
  * `norm_unit_diff_le`, `angle_eta_le`, `abs_phd_sub_le`: on the support the correction to the
    phase derivative is at most `2^{10-m}`, so for `|w| ≥ 2^{-m+ℓ+20}` the derivative is
    comparable to `⟪w,u⟫`;
  * `CartData`: the paper's symbol hypothesis `|∂_η^α b| ≤ B 2^{-(j-m)|α|}`, `|α| ≤ 9`, with
    `CartData.norm_le` and `CartData.dir_deriv_le`;
  * `exists_deriv_bound`, `norm_iteratedFDeriv_comp_affine`: a smooth compactly supported function
    has all derivatives bounded, and composition with an affine map costs `‖L‖ ^ n`;
  * `annB`, `gsm`, `shrinkS`, `clampLow`, `cut`, `wc0p`/`wc1p`/…: one-dimensional smooth cutoffs
    with explicit derivative scaling, and a partition of unity on `{lam |w| ≥ 256}`;
  * `unitVec`, `Vt`, `Vt_eq`, `norm_iteratedFDeriv_Vt_le`: a globally smooth, compactly supported
    replacement for `η ↦ η_i/|η| - (ξ-η)_i/|ξ-η|` agreeing with it on the support of the symbol,
    with derivatives `O(2^{-jn})`;
  * `nrm`, `Ntl`, `phsm`, `gnrm`, `oscph`: a globally smooth phase agreeing with
    `⟪w,η⟫ + ε t(|ξ-η| + |η|)` on the support, together with its line derivatives;
  * `Vhat`, `Psi`, `abs_Psi_ge`, `Psi_eq_of_mem`: a globally smooth, nowhere vanishing replacement
    for the `i`-th coordinate of the phase gradient, satisfying `|Psi| ≥ |w_i| - 2^{12-m}`;
  * `ibp44`: **the integration by parts identity**
    `∫ e^{2πi Φ} b dη = -(2πi)^{-1} ∫ e^{2πi Φ} ∂_{e_i}(b/Psi) dη`,
    valid with no case distinctions because both the phase and `Psi` are globally smooth;
  * `inv_add_geom`, `cAmp`, `rAmp`, `Amp_eq_sum`, `Ampd_decomp`: the finite Neumann expansion of
    the amplitude into `K` separated symbols plus a remainder, and the same for its coordinate
    derivative;
  * `SymbData`: the symbol hypotheses actually used (`|b| ≤ B`, `|∂_η b| ≤ B 2^{-(j-m)}`);
  * `norm_cAmpd_le`: the pointwise bound
    `|∂_{e_i} (b (-ε t Vhat)^k)| ≤ B 2^{-(j-m)} (2^{11-m})^k + B k (2^{11-m})^{k-1} · O(2^{-j})`;
  * `phcAS`, `lintegral_enorm_sq_fourier_phcA`: each separated term is a Schwartz function, so
    Plancherel applies to it;
  * `integral_oscph_mul_cAmpd`: the `η`-integral of the `k`-th term is the Fourier transform in `w`
    of that Schwartz function;
  * `exists_coord_large`, `abs_Psi_lower`, `Psi_ne_zero`: the choice of the coordinate direction and
    the lower bound `|Psi| ≥ |w_i|/2` on the region `|w_i| ≥ 2^{13-m}`;
  * `phasm_eq_phase`, `phase_mul_b_eq`, `integrable_Gf`: the smooth kernel agrees with
    `phase · e^{-2πi⟪w,η⟫}` against `b`, and the partial Fourier transform `Gf` is integrable
    (dominated by the `L¹` norm of the slice).

  * `lintegral_enorm_mul_le_sq`, `enorm_integral_mul_le`, `lintegral_comp_neg`,
    `lintegral_enorm_sq_le_of_bound`: the `L²` toolkit (Cauchy–Schwarz, reflection invariance, and
    the bound `‖f‖₂² ≤ ‖f‖_∞² · |supp f|`);
  * `cBound`, `lintegral_enorm_sq_cAmpd_le`, `lintegral_enorm_sq_fourier_neg_le`: the `L²` norm in
    `w` of the `k`-th term equals the `L²` norm in `η` of `∂_{e_i}(b(-ε t Vhat)^k)`, which is at
    most `cBound(k) · 2^{j - m/2 + 6}`;
  * `sum_geom_le`, `sum_cBound_div_le`: the summed Neumann bound
    `∑_{k<K} cBound(k)/A^{k+1} ≤ 2 B 2^{-(j-m)}/A + O(B 2^{-j})/A²` whenever `A ≥ 4·2^{11-m}`;
  * `fderiv_Psi_apply`, `rAmpd_eq`, `norm_rAmpd_le`: the derivative of the remainder amplitude and
    its bound `≲ (cBound(K)/|w_i| + B (2^{11-m})^K 2^{-j}/|w_i|²)/|w_i|^K`, which carries the
    factor `(2^{11-m}/|w_i|)^K ≤ 4^{-K}`.

  * `stronglyMeasurable_Gf`, `fourier_F_eq_integral_w`, `Sop_eq_integral_w`: **the
    `w`-representation** `S[F,b](ξ,t) = ∫ Gf(H)(ξ,w) (∫ e^{2πi Φ} b dη) dw`, obtained from the shear,
    the iterated Fourier transform and Fubini (integrability by domination against
    `B·1_{SuppSet}(η)·|Gf(w)|`);
  * `integral_oscph_mul_b_eq`: **the decomposed inner integral**
    `∫ e^{2πi Φ} b dη = -(2πi)^{-1}(∑_{k<K} 𝓕(phasm · ∂_{e_i}(b(-εtVhat)^k))(-w)/w_i^{k+1} + Rem)`;
  * `enorm_integral_term_le`, `enorm_integral_rem_le`: Cauchy–Schwarz in `w` for one Neumann term
    and for the remainder.

  * `lintegral_sum_terms_le`, `enorm_main_terms_le`: the sum of the `K` main terms is bounded by
    `√(2^{2j-m+12}) · (2B2^{-(j-m)}/A + O(B 2^{-j})/A²) · ‖g‖₂` whenever `A ≥ 4·2^{11-m}`;
  * `norm_integral_oscph_rAmpd_le`, `lintegral_rem_le`: the remainder contributes
    `rBound(K,A) · 2^{2j-m+12} · |supp g|^{1/2} · ‖g‖₂`, with `rBound` carrying the factor
    `(2^{11-m}/A)^K`;
  * `measurable_inner_integral`, `norm_le_two_mul_abs_snd`, `lintegral_offdiag_region`,
    `lintegral_offdiag_two_regions`: **the structural assembly is complete** — the `w`-integral is
    split into the two coordinate-dominant regions `{|w| ≤ 2|w_0|}` and its complement, and on each
    the estimate above applies with the corresponding coordinate direction;
  * `volume_closedBall_le`, `sqrt_two_zpow_mul`, `sqrt_two_zpow_even`, `sqrt_vol_eq`,
    `sqrt_neg_mul_sq`: the planar ball volume and the dyadic square-root identities needed to put
    the bound in closed form.

  * `main_term1_eq`, `main_term2_eq`, `main_bound_closed`: **the main term in closed form** — with
    `A = 2^{ℓ-m+18}`,
    `√(2^{2j-m+12}) · (2B2^{-(j-m)}/A + 8B·O(2^{-j})/A²) ≤ (1 + 32 Cs CV)·B·√(2^{3m})·2^{-ℓ}`,
    the constant being absolute.

  * `rem_bound_closed`, `lintegral_offdiag_kernel`, `Gf_eq_zero_of_localized`, `offdiag_Sop`:
    §4.4 is **complete** (recorded as Milestone 3 above).

  * `tsum_two_rpow_neg_le` (`∑_n (2^{-a})^n ≤ 3/a` for `0 < a ≤ 1`, via `1 - 2^{-a} ≥ a/3`),
    `Ann`, `lintegral_eq_tsum_Ann` (the `w`-plane splits into dyadic annuli
    `2^{k+20} ≤ |w| < 2^{k+21}` and the `lintegral` splits accordingly): the two ingredients of
    §4.6's summation.

  * `sepCLM`, `sepCut`, `hasTemperateGrowth_sepCut`, `farPart`, `nearPart`,
    `add_nearPart_farPart`, `farPart_support`, `nearPart_support`: the near/far split of `F` by a
    single smooth cutoff in `|y-z|²`, both pieces Schwartz (via `SchwartzMap.smulLeftCLM` and the
    temperate-growth API), with the support facts `1 < c|y-z|²` on the far piece and
    `c|y-z|² < 2` on the near piece.

  * `wMass`, `wMassW`, `volume_sepCLM_eq_zero`, `lintegral_enorm_sq_le_wMass`,
    `lintegral_sq_ann_le_wMassW`: the weight `w_γ(y,z) = |y-z|^{-(2γ-1)}` in both the `x = (y,z)`
    and the `w = y-z` variable, and the two comparisons `‖·‖₂ ≤ R^{(2γ-1)/2}‖·‖_{L²(w_γ)}` (the
    diagonal `{y=z}` is null, being a proper subspace of `ℝ⁴`);
  * `lintegral_ann_offdiag_le`, `coefFar`, `lintegral_offdiag_far`, `tsum_coefFar_le`,
    `lintegral_offdiag_far_closed`: **the far half of §4.6 is complete** —
    `∫ ‖g(w) ∫ e^{2πiΦ} b dη‖ dw ≤ c·B·2^{m(2-γ)}·‖g‖_{L²(|w|^{-(2γ-1)})}` for `g` vanishing where
    `|w| < 2^{21-m}`, with `c` absolute.  The `m`-power `2^{m(2-γ)}` is exactly what cancels
    against `2^{jγ/2}` when `m < j/2`.

  * `wMass`/`wMassW` are stated with the `ℝ≥0∞`-valued weight `‖·‖ₑ^{-(2γ-1)}` — unconditional
    measurability, and the value `+∞` on the diagonal is the correct one, which removes the need for
    an a.e. argument (`one_le_ofReal_mul_enorm_rpow` is the single pointwise inequality behind both
    comparisons);
  * `lintegral_wMassW_Gf`: **the weighted partial Plancherel identity**
    `∫_ξ ‖Gf(shear F)(ξ,·)‖²_{L²(|w|^{-(2γ-1)})} = ‖F‖²_{L²(w_γ)}` — Tonelli, Plancherel in `ξ` for
    each fixed `w`, and the shear change of variables;
  * `CFar`, `offdiag_Sop_far`: **the far part of Proposition 3.1** — for `F` supported where
    `|y-z| ≥ 2^{21-m}`, `‖S[F,b](·,t)‖₂ ≤ c·B·2^{m(2-γ)}·‖F‖_{L²(w_γ)}`;
  * `near_Sop`: **the near part** — Proposition 4.2 combined with the weight comparison, for `F`
    supported where `|y-z| ≤ 2^{22-m}`;
  * `fourier_schwartz_add`, `exists_fourier_bound`, `integrable_SopK_integrand`, `Sop_add`:
    additivity of `S[·,b]` in `F`, which is what lets the near/far split be combined.

  * `enorm_add_sq_le`, `nearPart_sep_le`, `farPart_sep_ge`, `norm_nearPart_le`, `norm_farPart_le`,
    `measurable_Sop`: the elementary tools for the near/far combination, with the cutoff parameter
    `c = 2^{2m-42}` chosen so the near piece sits in `|y-z| ≤ 2^{22-m}` and the far piece in
    `|y-z| ≥ 2^{21-m}`;
  * `prop31_single`: **Proposition 3.1 for one angular scale `m`** — the near/far split combined,
    `∑_{t∈ℰ} ‖S[F,b](·,t)‖₂² ≤ 4(near + (#ℰ)·far)`.  Needs `Sop_add` and a joint-measurability
    hypothesis on the symbol (`IsAdapted` only gives measurability in `η` for each fixed `ξ`, which
    is not enough to split a `lintegral` in `ξ`);
  * `not_three_in_interval`, `card_le_two_of_separated`, `card_le_two_mul_card_of_cover`: the bridge
    from covering numbers to interval counts — a `σ`-separated set meets an interval of length `σ`
    in at most two points, so `#ℰ ≤ 2·#(cover)`.  This is what will turn the repository's
    `HasSubpowerAssouadCoverBound` into the `IsIntervalCount` hypothesis of `prop42`.

  * `intervalCount_of_assouad`: **the Assouad bridge** — a `2^{-j}`-separated `ℰ ⊆ E ∩ [1,2]` has
    `IsIntervalCount ℰ 2^{2m-j} (2 + 2C·2^{jη}·2^{2mγ})` whenever
    `HasSubpowerAssouadCoverBound E γ η C`.  (`RS.lean` now imports the repository's
    `QuasiAssouadBridge`, so the paper's `χ^E_{A,γ}(2^{-j})` is the repository's `C·2^{jη}`.)
  * `prop31_combine`, `prop31_single`, `prop31_single_triv`: the near/far combination with the near
    bound abstracted, instantiated both with Proposition 4.2 (strictly adapted pieces) and with
    Proposition 4.1 (the smallest-angle piece, which is adapted but not strictly adapted).

  **Next:** the angular partition of unity.  Using `v = (2^{-2j} det(ξ,η))²` and
  `A_m(v) = smoothTransition(4^m v - 1)`, the pieces `ψ_0 = A_0`, `ψ_m = A_m - A_{m-1}`
  (`1 ≤ m ≤ M`), `ψ_{M+1} = 1 - A_M` with `M = ⌊j/2⌋` telescope to `1` exactly, and `det` being
  bilinear is what makes both the radial (`RayData`) and Cartesian (`SymbData`) derivative bounds
  come out at the right scales. — the weighted `L²` estimate for `T_j` with weight
  `w_γ(y,z) = |y-z|^{-(2γ-1)}`.  The three §4 estimates are combined there by decomposing `F`
  dyadically in `|y-z|` (index `ℓ`) and the symbol as `b_j = ∑_{0<m<j/2} b_{j,m} + R_j`, using
  `∑_ℓ min(2^{-ℓ/2}, 2^{ℓ(γ-1/2)}) ≲ (2γ-1)^{-1}`.  After that: §3 (Theorem 2.5 via radius
  discretization, bilinearization, Stein interpolation and one-dimensional fractional integration),
  then §2 (Corollary 2.6 and Theorem 1.1, wiring into `exists_q4_sector_dyadic_rate` and
  `exists_q4_ltwo_sector_dyadic_rate` in `ProofSkeleton.lean` to drop the `hd` hypothesis).
* Then: §4.6, §3, §2.

### Route chosen for the off-diagonal estimate of §4.4

The paper obtains the off-diagonal estimate by verifying the symbol estimate
`|∂_w^β ∂_η^α a_{t,ξ}(w,η)| ≲ B 2^{-(j-2m+ℓ)} 2^{m|β|} 2^{-(j-m)|α|}` for `|α|,|β| ≤ 9` and then
quoting Calderón–Vaillancourt (which is formalized here in full, in both an isotropic and an
anisotropic form, and is available as `exists_cv_bound_aniso`).

In the regime that actually occurs the `w`-dependence of the symbol enters only through
`1/Ψ_i(w,η)` with `Ψ_i = w_i + ε t V_i(η)`, `|V_i| ≤ 2^{9-m}` on the support and `|w_i| ≳ 2^{ℓ-m+20}`
on the relevant piece, so `|ε t V_i / w_i| ≤ 1/8`.  A finite Neumann expansion of length `K = j+1`
therefore writes the symbol as a sum of `K` symbols that are *products* of a function of `w` alone
and a function of `η` alone, plus a remainder of size `8^{-K} ≤ 2^{-3j}`.  Each product symbol is
handled by plain Plancherel, and the remainder by the trivial `L¹` bound; the resulting estimate is
the same one, with the same powers of `2`, and it needs only **one** `η`-derivative of the symbol
instead of nine.  This route is taken here.

### Cross-check of §4 against the source, and the plan for §4.6

The three §4 statements were checked against the paper (fetched from `ar5iv`):
Prop 4.1 `≤ c‖b‖_∞ 2^{j-m/2}(#ℰ)^{1/2}‖F‖₂`, Prop 4.2
`≤ cB 2^{j-m/2}(sup_{|I|=2^{-j+2m}}#(ℰ∩I))^{1/2}‖F‖₂` under radial-derivative bounds for
`N = 0,1,2`, and Prop 4.3 `≤ cB 2^{3m/2-ℓ}(#ℰ)^{1/2}‖F‖₂` for `F` supported where
`|y-z| ≥ 2^{-m+ℓ+20}`.  These are exactly `prop41`, `prop42` and `offdiag_Sop`; the formalized
hypotheses are equal or weaker in each case (`offdiag_Sop` needs only `|∂_η b| ≤ B2^{-(j-m)}`,
i.e. `|α| ≤ 1`, instead of the paper's `|α| ≤ 9`, and asks for `F` in the dyadic annulus
`2^{ℓ-m+19} ≤ |y-z| ≤ 2^{ℓ-m+21}`, which is what the application supplies).

Plan for §4.6.  Rather than the paper's full decomposition `F = ∑_{k∈ℤ} F_k`, only **two** pieces
are used: `F = F·(1-ψ_m) + F·ψ_m` with a single smooth cutoff `ψ_m` in `|y-z|²`, so both pieces are
Schwartz and `Sop` splits by ordinary linearity.
* Near piece (`|y-z| ≲ 2^{21-m}`): Proposition 4.2 directly, together with
  `‖F·(1-ψ_m)‖₂ ≤ 2^{(21-m)(2γ-1)/2}‖F‖_{L²(w_γ)}` since `|y-z|^{2γ-1}` is increasing.  The powers
  of `2^m` cancel exactly against `N^{1/2} ≤ [χ^E_{A,γ}]^{1/2} 2^{mγ}`, giving `c 2^j [χ]^{1/2}`.
* Far piece: the dyadic decomposition is done on the `w`-side, where it is only a partition of the
  domain of a `lintegral` (`lintegral_eq_tsum_Ann`) and needs no smoothness — the kernel-form
  estimate `lintegral_offdiag_kernel` applies to `g·1_{Ann k}` for each `k`.  Summing gives
  `∑_{ℓ≥1} 2^{-ℓ(3/2-γ)} = O(1)` since `γ ≤ 1`, and the `m`-powers again combine to
  `2^{jγ/2}2^{m(2-γ)} ≤ 2^j` precisely because `m < j/2`.
Cauchy–Schwarz over the `j/2` values of `m` then produces the factor `j^{1/2}`.  Proposition 3.1 is
stated in the paper's form `min(j^{1/2}/(2γ-1), j)`, which is weaker than what this route yields
(the factor `(2γ-1)^{-1} ≥ 1` is kept so the statement matches the source).

### The remainder `R_j` of §4.6: why no separate argument is needed

The paper decomposes `b_j = ∑_{0<m<j/2} b_{j,m} + R_j` and (per the `ar5iv` summary) bounds `R_j` by
Proposition 4.1.  That accounting does **not** close: Prop 4.1 gives
`2^{j-m/2}(#ℰ)^{1/2}` and with `(#ℰ)^{1/2} ≤ [χ]^{1/2}2^{jγ/2}` one needs `3/4 + γ/2 ≤ 1`, i.e.
`γ ≤ 1/2`, which is exactly the range this paper is *not* about.  (The summarizer had already
garbled `q₄`, so the summary is not reliable at this level of detail.)

The correct accounting, verified here, is that **every piece is `(j,m)`-adapted for some
`0 ≤ m ≤ ⌊j/2⌋`, and the weight supplies the missing power**.  Writing the near-piece exponent with
both the estimate and the weight factor `2^{-m(2γ-1)/2}` included:

* Prop 4.2 (needs *strictly* adapted, so `0 ≤ m < ⌊j/2⌋`), with `N ≤ 2C·2^{jη}2^{2mγ}`:
  `j - m/2 + mγ - m(2γ-1)/2 = j`, exactly, for every `m`.
* Prop 4.1 (needs only adapted — used for the smallest-angle tail `m = ⌊j/2⌋`, which has no lower
  angle bound and so is not strictly adapted), with `(#ℰ)^{1/2} ≤ [χ]^{1/2}2^{jγ/2}`:
  `j - m/2 + jγ/2 - m(2γ-1)/2 = j` at `m = j/2`, again exactly.
* the far piece: `m(2-γ) + jγ/2 ≤ j` precisely when `m ≤ j/2`.

So the decomposition is taken as `b_j = ∑_{0 ≤ m ≤ ⌊j/2⌋} b_{j,m}` with *tail* cutoffs at both ends
(the `m = 0` piece absorbing all large angles, the `m = ⌊j/2⌋` piece all small ones), every piece
`(j,m)`-adapted, and no separate `R_j` term.  Cauchy–Schwarz over the `⌊j/2⌋+1` values of `m` then
produces the factor `j^{1/2}`.

### Use of the exception clause (one extra file)

Mathlib contains **no** Hardy--Littlewood--Sobolev inequality and no Riesz-potential bound (checked
by search: zero hits).  Section 3 of the paper needs one-dimensional fractional integration, so on
2026-08-26 the user explicitly authorized the `instructions-rs.md` exception clause for it:
`LeanSpherical/Auto/HardyLittlewoodSobolev.lean` will be created for that prerequisite.  This is
the first and so far only use of the clause.

## Judgment calls

1. **Only pure derivatives.** The hypotheses of the Calderón--Vaillancourt theorem above use only
   the *pure* iterated derivatives in each of the two variables separately, not the mixed
   derivatives `∂_w^β ∂_η^α a` of the classical `S⁰_{1/2,1/2}` statement.  This is a weaker
   hypothesis, hence a stronger theorem, and it is what the symbol estimates verified in
   Roos--Seeger §4.4 (`|∂_w^β ∂_η^α a| ≲ B 2^{-(j-2m+ℓ)} 2^{m|β|} 2^{-(j-m)|α|}`) supply, with
   `A = B 2^{-(j-2m+ℓ)}`, `σ = 2^m`, `τ = 2^{-(j-m)}` and `σ τ = 2^{2m-j} ≤ 1` since `m ≤ j/2`.

2. **Normalization.** All phases in `RS.lean` carry the factor `2π` of `Mathlib`'s Fourier
   transform, which is the normalization used everywhere in this repository
   (`Auto.Spherical.SurfaceCore.surfacePhase`).  This multiplies the paper's phases by `2π` and
   changes only absolute constants.

3. **Schwartz data in §4.**  The §4 propositions are stated for Schwartz `F` on `ℝ⁴`.  This is
   what the application needs (in §3 the input is `f ⊗ f` with `f` in the repository's Schwartz
   core, and §4.6 multiplies it by smooth dyadic cutoffs in `|y - z|`, which preserves the
   Schwartz class), and it makes Plancherel available directly.

4. **What the new content is.** The repository's AHRS formalization
   (`Auto.Spherical.FractalDilations.Theorems.theorem_one`) already proves `R(β,γ) ⊆ T_E` under
   `3 ≤ d ∨ (d = 2 ∧ γ ≤ 1/2)`. RS Thm. 1.1 is the same inclusion with that hypothesis removed, so
   the work is the case `d = 2`, `γ > 1/2` (paper §3–§4), plus the interpolation of §2 that glues it
   to the existing `Q₁/Q₂/Q₃` estimates. The final statement is phrased so that it is literally the
   paper's Theorem 1.1, with no side hypothesis on `d` or `γ`.
