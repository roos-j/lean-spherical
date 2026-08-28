# Report — Roos–Seeger Theorem 1.1

Executive summary of the formalization of Thm. 1.1 of [arXiv:2004.00984](https://arxiv.org/abs/2004.00984).
Standing instructions: [`instructions-rs.md`](instructions-rs.md).

## Milestones (recorded only when fully finished)

**Rule (set by the user on 2026-08-27).**  An entry counts as a *milestone* only if it
**completely proves a significant step or part of the paper** (a numbered theorem, proposition or
corollary, or a self-contained section of the logical path).  Everything else — infrastructure,
instantiations, refactors, partial steps — is recorded under a `Progress` heading.  Every entry,
milestone or progress, carries a timestamp taken from the system clock.

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

4. **Proposition 3.1 of the paper (all of §4)** —
   `Auto.Spherical.FractalDilations.RS.prop31` (`RS.lean`, ~11 960 lines, `sorry`-free,
   axioms `[propext, Classical.choice, Quot.sound]`).  For a `(j,0)`-adapted symbol `b` with
   `|b| ≤ B`, `|∂_η b| ≤ B 2^{-j}` and radial derivative bounds `|∂_ρ^N b| ≤ B 2^{-jN}`
   (`N = 0,1,2`), and a set of radii `ℰ ⊂ [1,2]` whose count in every interval of length
   `2^{2m-j}` is at most `Na·2^{2mγ}` (and `#ℰ ≤ Na·2^{(2M+2)γ}`), with `M = ⌊j/2⌋`:
   `∑_{t∈ℰ} ‖S[F,b](·,t)‖₂² ≤ c (M+2)² B² Na 2^{2j} ‖F‖²_{L²(w_γ)}`,
   `w_γ(y,z) = |y-z|^{-(2γ-1)}`, `c` absolute.  This is the paper's Proposition 3.1 in the
   `j`-alternative of its `min(j^{1/2}(2γ-1)^{-1}, j)` (see the judgment call below).
   The proof is the angular decomposition `b = ∑_{m=0}^{M+1} b·ψ_m(2^{-2j}det(ξ,η))`, where the
   `ψ_m` telescope to `1` (`sum_angH`); each `b·ψ_m` is verified to be strictly `(j,m)`-adapted
   for `m ≤ M` (`bpiece_strict_supp`) and `(j,M+1)`-adapted for the tail, with
   `SymbData j m` (`bpiece_symbData`) and `RayData j` (`bpiece_rayData`) at the cost of a
   constant factor `1+192C_st`; Proposition 4.2 + the off-diagonal estimate handle
   `m ≤ M` (`prop31_single`), Proposition 4.1 + the off-diagonal estimate the tail
   (`prop31_single_triv`); all powers of `2^m` cancel exactly (`near_factor_le`,
   `triv_factor_le`, `far_factor_le`), and Cauchy–Schwarz over the `M+2` pieces
   (`enorm_sq_sum_le`) gives the factor `(M+2)²`.

5. **The bilinear Hardy--Littlewood--Sobolev inequality on the line** —
   `LeanSpherical/Auto/HardyLittlewoodSobolev.lean` (1 140 lines, `sorry`-free, axioms
   `[propext, Classical.choice, Quot.sound]`).
   `Auto.HardyLittlewoodSobolev.lintegral_bilinear_riesz_le`: for `0 < λ < 1` and
   `r = 2/(2-λ)` (so that `1/r + 1/r + λ = 2`, the homogeneity forced by scaling),
   `∫∫ |s-u|^{-λ} h(s) g(u) ds du ≤ c_λ (∫ h^r)^{1/r} (∫ g^r)^{1/r}` with
   `c_λ = 32/((1-λ)(1 - 2^{-λ/(2-λ)}))`, for arbitrary measurable `h, g : ℝ → [0,∞]` —
   stated with `lintegral`s throughout, so no integrability hypotheses appear.
   This is the authorized extra prerequisite file (Mathlib has neither Riesz potentials nor
   Marcinkiewicz interpolation).  The proof is self-contained and uses no interpolation theorem:
   the "bathtub" bound `∫_B |s-u|^{-λ}du ≤ (2/(1-λ))|B|^{1-λ}` (proved by comparing `B` with the
   ball of the same measure centred at `s`), the dyadic level-set decomposition
   `h ≤ ∑_{m∈ℤ} 2^{m+1}1_{A_m}`, and the resulting double sum
   `∑_{m,n} 2^{-(r-1)|m-n|}(x_m + y_n)` with `x_m = 2^{mr}|A_m|`, `∑_m x_m ≤ 1`, which converges
   because `r > 1`.

6. **The `L¹_{y₁}L^∞_{y₂} → L^∞` endpoint of §3 (the paper's (3.14))** — `RS.lean`
   (~18 300 lines, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`).
   * `lintegral_norm_kern_le` — the **kernel estimate (K)**: for `M ≥ 7` with `2^{-M} ≤ 1/100`,
     `j ≤ 2M ≤ j + 14` and `⌈π 2^M⌉ ≤ 2^L`, uniformly in `w`,
     `∫⁻_v ‖k_{j,t}(w,v)‖ ≤ 7·10⁸(1+stC)B₀·2^M(10(L+1)+1)`, i.e. `≲ 2^{j/2}(1+j)`.
     Choosing `M = max 7 ⌊(j+1)/2⌋`, `L = M+2` makes the hypotheses hold for every `j`.
   * `enorm_TopS_le_mix` — the **operator endpoint**: `‖T_tf(x)‖ ≤ C·‖f‖_{L¹_{y₁}L^∞_{y₂}}`
     with the same constant, for every `x` and every `1 ≤ t ≤ 2`, `|ε| = 1`.
   The route (all of it new, since no sector-localized wave-kernel asymptotics exist in Mathlib or
   the repository) is: polar coordinates for `k_{j,t} = 𝓕⁻(mfull)` (`kern`), a **plate
   decomposition of the angle** at scale `Q = 2^{-M}` (`kern_eq_sum_plates`), and per plate the
   better of two integrations by parts — four radial ones (the radial phase is *linear* in `ρ`,
   `norm_radial_integral_le`) and two angular ones (`norm_angular_plate_le`) — combined without
   square roots by `le_of_sq_le_mul`.  On each plate the phase is the affine function
   `ψ(v) = a v + A_ν/…` of the second coordinate with `a = sin φ_ν ≥ 4/5` and the *`v`-independent*
   parameter `A_ν = w + εt cos φ_ν` (`psi1_ref_identity`), which yields a single pointwise
   majorant (`norm_kernPlate_far_majorant`), an integrable envelope
   (`exists_plate_majorant`, `exists_plate_majorant'`) with `∫G ≲ (1+stC)B₀/max(Q,|A_ν|)`, and
   finally the **plate sum** `∑_ν 1/max(Q,|A_ν|) ≤ 2^M(10(L+1)+1)` (`plate_sum_le`), which comes
   from the separation `|A_ν - A_{ν'}| ≥ (2/5)|ν-ν'|Q` (`plA_separated`) via a minimizing plate and
   the dyadic harmonic bound (`harmonic_int_le`).  The operator step uses the convolution
   representation `T_tf = k_{j,t} * f` (`TopS_eq_convolution`, from Mathlib's Schwartz convolution
   theorem) and iterated integration on the plane (`lintegral_Pl_eq_prod`).

7. **The `L^p` estimate of §3 — the analytic interpolation, complete** — `RS.lean`
   (~23 700 lines, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`).
   `lintegral_pow_Top2_le`: for `2 < p`, `1/2 < γ ≤ 1` and data `F` of finite interpolated norm,
   `(∑_{t∈ℰ} ∫ |𝒯_j F(t,x)|^p dx)^{1/p} ≤ A^{1/p}·B^{1-2/p}`, where `A` is the constant of
   Proposition 3.1 (`prop31_Top2_wmass`) times `N = ‖F‖^{p'}_{X}`, and `B` is the square of the
   endpoint constant (K) times `N`.  This is the paper's §3 conclusion, and it required, in order:
   * the explicit **Calderón factorization** of the couple `(L²(w₁), L¹_{y₁}L^∞_{y₂})`
     (`calderon_factorization`, `gZero`, `gOne`) and the two analytic families
     `F_ζ = sgn F·G₀^{1-ζ}G₁^ζ` (`Ffam`), `φ_ζ = sgn φ·|φ|^{p'(1+ζ)/2}` (`phifam`), which
     reproduce `F` and `φ` at `θ = 1 - 2/p` (`ae_Ffam_at_theta`, `phifam_at_theta`) and satisfy the
     two edge bounds (`enorm_pairT_edge0`, `enorm_pairT_edge1`);
   * **holomorphy and continuity of the pairing** `Ψ(ζ) = ⟨𝒯_j F_ζ, φ_ζ⟩` on the strip.  Both are
     proved by dominated convergence and **Morera's theorem** (`differentiableOn_Top2_Ffam`,
     `differentiableOn_pairT_fam`), the wedge integrals being exchanged with the `ℝ⁴`- and the
     `ℝ²`-integral by the swap lemmas `intervalIntegral_integral_swap_gen`; the ζ-independent
     majorants are `majB` (level one, integrable by `integrable_majB`, which is where the two
     kernel bounds `lintegral_kern_gZero_le` and `lintegral_kern_gOne_le` are used) and
     `majP = U·(|φ|^{p'/2} + |φ|^{p'})` (level two, integrable because the test function is bounded
     with compact support, `U` coming from the ζ-uniform bound `enorm_Top2_Ffam_le`);
   * **Hadamard's three lines** (`three_lines`, from Mathlib's Phragmén–Lindelöf) applied with a
     positive slack `δ` that is then let to zero, which removes all degenerate cases
     (`norm_pairT_interp`);
   * **duality** (`lintegral_pow_le_of_pairing_le`): the truncated dual family
     `φ = χ_{|x|≤n, |h|≤n}·conj(h)|h|^{p-2}` turns the pairing bound into the `ℓ^pL^p` bound, the
     truncation being removed by monotone convergence.

8. **§3 complete up to the discretization: the `L^{q₄}` estimate for the linear operator** —
   `RS.lean` (~24 400 lines, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`).
   `lintegral_pow_TopS_le`: for `p = p₄ = (3+2γ)/2`, `q₄ = 2p₄` and a uniformly `2^{-j}`-separated
   `ℰ ⊆ [1,2]` with the Assouad counting data,
   `(∑_{t∈ℰ} ‖T_t f‖_{q₄}^{q₄})^{1/q₄} ≤ C₃^{1/2}‖f‖_{p₄}` for every Schwartz `f`, where
   `C₃` (`C3`) is the product of the Proposition 3.1 constant to the power `1/p`, the endpoint
   constant to the power `1-2/p` and the Hardy–Littlewood–Sobolev constant to the power `1-1/p`.
   The two new ingredients:
   * **the fractional integration step** (`normNpp_tensF_le`): Hölder in the base variable turns the
     interpolated norm of a tensor product into a Riesz form, and the repository's bilinear
     Hardy–Littlewood–Sobolev inequality (`Auto.HardyLittlewoodSobolev.lintegral_bilinear_riesz_le`)
     applies *exactly* at `p = p₄`, because `r = 2/(2-λ) = p/p'` forces `p = (3+2γ)/2` — this is
     where the exponent `p₄` comes from.  With it, `N_{p}(f⊗g) ≤ c(‖f‖_p‖g‖_p)^{p'}`;
   * **the bilinearization** (`Top2_tens`, already available): `𝒯_j(f⊗f)(x,t) = (T_tf(x))²`, so the
     `L^{p₄}` bound for `𝒯_j` is the `L^{q₄}` bound for `T_t`, and the side conditions
     (finiteness of the fibre profiles and of the interpolated norm for a Schwartz tensor product)
     are supplied by `fibProf_tensF_schwartz_ne_top` and `normNpp_tensF_schwartz_ne_top` from the
     Schwartz decay.

9. **§3 complete: Theorem 2.1 for the single-scale operator** — `RS.lean` (~25 300 lines,
   `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`).
   `lintegral_pow_iSup_TopS_le_of_assouad`: for `E ⊆ [1,2]` with a subpower Assouad cover bound,
   `p = p₄ = (3+2γ)/2`, `q₄ = 2p₄` and every `j ≥ 1`,
   `‖sup_{t∈E}|T_tf|‖_{q₄} ≤ (C₃(m)^{1/2} + 2^{-j+1}C₃(m̃)^{1/2})‖f‖_{p₄}` for Schwartz `f`,
   where `m̃` is the `t`-derivative multiplier.  The new pieces:
   * the **discretization**: `exists_delta_net` (a maximal `δ`-separated subset of `E` is a
     `δ`-net), `card_le_of_isIntervalCount`, `IsIntervalCount.subset/.translate/.mono` and
     **`exists_net_counting_data`** — at `δ = 2^{-j}` and `M_c = ⌊j/2⌋` the net's interval counts
     are exactly the hypotheses of Proposition 3.1, with `N_a ≤ 6 + 6C2^{jη}` from the repository's
     Assouad bridge `intervalCount_of_assouad`;
   * the **FTC step**: `iSup_enorm_TopS_le` bounds the supremum over `E` by the `ℓ^{q}`-sum over the
     net plus the `ℓ^q`-sum of the local integrals `∫_{-δ}^{δ}|T_{t'+s}[m̃]f|ds`, and
     **`lintegral_pow_derTr_le`** bounds the latter by `2δ·C₃(m̃)^{1/2}‖f‖_p` — Hölder in the
     dilation parameter (`lintegral_Ioc_pow_le`), Tonelli, and the §3 estimate applied to each
     translated net `(ℰ+s) ∩ [1,2]`;
   * `exists_plate_params`: `M = max 7 ⌈j/2⌉`, `L = M+2` satisfy the endpoint hypotheses for every
     `j`, so no scale is excluded.

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

  **Next:** §3 of the paper (plan settled after reading §3 verbatim from the source, and after
  auditing the repository's `hd : 3 ≤ d ∨ d = 2 ∧ γ ≤ 1/2` dependency chain):

  1. ~~`Auto/HardyLittlewoodSobolev.lean`~~ — done, Milestone 5 above.
  1b. **Done:** the §3 symbol bridge in `RS.lean` — `MultData j m m2 B₀` (the hypotheses on the
     single-factor multiplier `m(t,ω) = χ_j(ω)a(tω)`: smooth, supported in `Θ_j`, values and the
     first two directional derivatives bounded by `B₀2^{-jN}`), the product symbol
     `bprod m t ξ η = m(t,ξ-η)m(t,η)` with its radial derivatives `bq1`, `bq2`, the packages
     `bprod_symbData`, `bprod_rayData`, `measurable_bprod`, and the corollary `prop31_bprod`:
     Proposition 3.1 holds for the §3 symbol with `B = 4B₀²`.
  2. The physical-space operators.  Concretely: with
     `M(t,ω) = e^{2πiεt‖ω‖}m(t,ω)` (so that `phase·bprod m = M(ξ-η)M(η)`), put
     `k_t = 𝓕⁻(M(t,·))` (Schwartz, since `M(t,·)` is smooth and compactly supported),
     `T_tf = 𝓕⁻(M(t,·)·𝓕f)`, and `𝒯_jF(·,t) = 𝓕⁻(S[F,bprod m](·,t))`.  Note
     `S[F,b](·,t)` is *compactly supported* (it vanishes for `‖ξ‖ > 2^{j+2}`) and continuous, so
     Fourier inversion applies to it directly.  The identities to prove are
     (I1) `𝒯_jF(x,t) = ∫∫ k_t(x-y)k_t(x-z)F(y,z)dydz` (change of variables
     `(σ,η) = (w₁+w₂,w₂)`, which has determinant one, plus Fubini);
     (I2) `T_tf = k_t ∗ f`;
     (I3) `𝒯_j(f⊗g) = T_tf·T_tg` (immediate from I1, I2);
     (I4) `𝓕_x(𝒯_jF(·,t)) = S[F,bprod m](·,t)` (Fourier inversion), whence
     `‖𝒯_jF(·,t)‖_{L²} = ‖S[F,b](·,t)‖_{L²}` and Proposition 3.1 transfers.
     **Route settled and partly built.**  Everything stays inside the Schwartz class, so the
     repository's Schwartz Plancherel suffices — no `MemLp 2` Fourier theory is needed:
     * `mfull j ε m t ω = e^{2πiεt·Ntl j ω}·m(t,ω)` uses the *globally smooth* `Ntl j`
       in place of `‖ω‖` (they agree on `Θ_j`, which contains the support of `m`), hence is
       smooth and compactly supported, hence Schwartz (`mfullS`);
       `phase_bprod_eq : phase·bprod m = mfull(ξ-η)·mfull(η)` holds *everywhere*.
     * `TopS hm ε t f = 𝓕⁻(mfull · 𝓕f)` is Schwartz, with
       `fourier_TopS : 𝓕(T_tf) ω = mfull(ω)·𝓕f(ω)` and `fourier_TopS_eq_zero` off `Θ_j`.
     * `lintegral_enorm_sq_fourierInv_schwartz_Pl`: Plancherel for `𝓕⁻` (via
       `𝓕⁻ h x = 𝓕 h (-x)` and reflection invariance).  **Done, all of the above.**
     * `tens f g : 𝓢(ℝ⁴,ℂ)` — the Schwartz tensor product, built by hand (Mathlib has none):
       the `decay'` field comes from `norm_iteratedFDeriv_mul_le`,
       `norm_iteratedFDeriv_comp_affine` and `SchwartzMap.one_add_le_sup_seminorm_apply`, giving
       the constant `Kf·Kg·(‖π₁‖+‖π₂‖)^n`.  `fourier_tens`: `𝓕(f⊗g)(pr u v) = 𝓕f(u)·𝓕g(v)`.
     * `Amul hm ε t f = mfull·𝓕f` (Schwartz), `Sop_tens_eq_convolution`:
       `S[f⊗g, bprod m](ξ,t) = (Amul g ⋆ Amul f)(ξ)`, and `TopS_mul_eq`:
       `T_tf·T_tg = 𝓕⁻(Amul g ⋆ Amul f)` — the latter from Mathlib's
       `Real.fourier_mul_convolution_eq` together with `𝓕⁻ h x = 𝓕 h (-x)`, no Fubini needed.
     * `lintegral_enorm_sq_TopS_mul`: `∫|T_tf·T_tg|² = ∫|S[f⊗g,bprod m](·,t)|²`, and hence
       **`prop31_phys`** — Proposition 3.1 in physical space, the `L²` endpoint of §3:
       `∑_{t∈ℰ}‖T_tf·T_tg‖²_{L²(ℝ²)} ≤ c(M+2)²B₀⁴Na 2^{2j}‖f⊗g‖²_{L²(w_γ)}`.
       **All of step 2 is done.**
  3. The sectorial `L^∞` endpoint `sup_{x,t}|𝒯_jF| ≲ 2^j ∫_{(y_1,z_1)} sup_{(y_2,z_2)}|F|`.
     For a tensor this is the *linear* statement
     `sup_x|T_tf(x)| ≤ c 2^{j/2} ∫_ℝ sup_{y_2}|f(y_1,y_2)| dy_1`, and since
     `T_tf = k_t ∗ f` with `k_t = 𝓕⁻(M(t,·))` it reduces to the single kernel estimate
     `sup_{u_1} ∫_ℝ |k_t(u_1,u_2)| du_2 ≤ c 2^{j/2}`.
     The mechanism (worked out, not yet formalized): write
     `k_t(u) = ∫∫ e^{2πi(u·ω + εt‖ω‖)}M(t,ω)dω_1dω_2`.
     * In `ω_2` the phase derivative is `u_2 + εt·ω_2/‖ω‖ ≈ u_2 ± εt`, and the `ω_2`-range is
       `≈2^j`, so repeated integration by parts gives
       `|k_t(u)| ≲ 2^{3j/2}(1 + 2^j|u_2 ± εt|)^{-N}`; integrating in `u_2` costs `2^{-j}` and
       yields exactly `2^{j/2}`.
     * The extra factor `2^{j/2}` (rather than the trivial `2^j` from `‖M‖_{L^1}≈2^{2j}`) comes
       from the `ω_1`-integral: there `∂_{ω_1}^2(εt‖ω‖) = εtω_2^2/‖ω‖^3 ≈ 2^{-j}`, so the
       van der Corput second-derivative test gives `|∫dω_1| ≲ (2^{-j})^{-1/2} = 2^{j/2}`.
       This `2^{j/2}` is *not* optional: with the trivial bound the interpolation loses
       `2^{j(2γ-1)/(3+2γ)}`, which is exactly the gain the theorem is about.
     **Done — van der Corput's second-derivative test** (`norm_integral_osc_vdc`):
     if `τ'' ≥ kap > 0`, `‖A‖ ≤ M` and `‖A'‖ ≤ M₁` then
     `‖∫_a^b e^{i·lam·τ}A‖ ≤ (10M + 2M₁(b-a))/√(lam·kap)`.  Built from
     * `integral_osc_ibp_bdry` / `norm_integral_osc_ibp_bdry` — the first-derivative
       (non-stationary phase) test *with boundary terms* and with the hypotheses on `τ'` local to
       `uIcc a b`, which §4.3's `integral_osc_ibp` (amplitude vanishing at both endpoints,
       `τ'` nonvanishing globally) cannot provide;
     * `incr_of_deriv_ge` and `exists_stationary_lower` — the convexity of the phase gives a
       point `c ∈ [a,b]` with `kap|x-c| ≤ |τ' x|` throughout;
     * `norm_integral_osc_side` — the one-sided estimate `(4M + M₁(β-α))/(lam·mu)` on an interval
       where `|τ'| ≥ mu`, whose `τ''`-term is handled by the telescoping identity
       `∫ τ''/(τ')² = 1/τ'(α) - 1/τ'(β) ≤ 2/mu`, making it independent of any *upper* bound on
       `τ''` (essential: in the application `τ''` is of size `2^{-j}` but no upper bound is
       cheap to state).
     Remaining for the `L^∞` endpoint: apply this to the `ω_1`-integral, do the `ω_2`
     integration by parts (where `integral_osc_ibp` *does* apply, since `M(t,·)` is compactly
     supported), and assemble the two-variable estimate.
     Also available in the repository: `Auto.Spherical.FractalDilations.QuadraticStationaryPhase`
     (`exists_quadraticMoment_zero_decay`: `‖∫_0^1 h(u)e^{iλu²}du‖ ≤ C/√λ` for smooth `h`, and
     a change-of-variables reduction `smoothEndpointQuadraticIntegral_eq_quadraticMomentIntegral`),
     plus the integration-by-parts files `OscillatoryIBP`, `RepeatedOscillatoryIBP`,
     `CompactOscillatoryIBP`.  The next concrete task is to reduce the `ω_1`-integral to that
     form (or prove van der Corput directly) and then assemble the two-variable estimate.
  4. The interpolation of 2 against 3.  This is a *bilinear mixed-norm* complex interpolation:
     after applying the bilinear HLS of step 1 to the weight (legitimate because
     `|y-z| ≥ |y_1-z_1|`), the two endpoints read
     `|Λ(f,g,φ)| ≤ M_0‖f‖_X‖g‖_X‖φ‖_2` with `X = L^{4/(3-2γ)}_{y_1}L^2_{y_2}` and
     `|Λ| ≤ M_1‖f‖_Y‖g‖_Y‖φ‖_1` with `Y = L^1_{y_1}L^∞_{y_2}`, and both mixed exponents
     interpolate at `θ = 4/(3+2γ)` to `L^{p_4}(ℝ²)`, `p_4 = (3+2γ)/2` — checked.  Because the
     endpoints are mixed-norm, the repository's `stein_interpolation` (which needs a single
     `L^p(μ)` on each side) does not apply; the interpolation is done directly from
     `Complex.PhragmenLindelof.vertical_strip` on the explicit Calderón family, which is a finite
     sum of exponentials in `z` for simple `f, g, φ` and hence entire.
  4. ~~The interpolation of 2 against 3~~ — done, Milestone 7.
  4b. ~~Fractional integration and bilinearization~~ — done, Milestone 8:
     `normNpp_tensF_le`, `lintegral_pow_Top2_tensF_le`, `lintegral_pow_TopS_le`.
  5. §3 assembly.  **The FTC step in `t` is done**: `mtil` (`m̃ = 2πiε‖ω‖m + ∂_tm`),
     `hasDerivAt_mfull`, `TopS_eq_integral` (the operator as an explicit Fourier integral),
     **`hasDerivAt_TopS`** (differentiation under the integral, by
     `hasDerivAt_integral_of_dominated_loc_of_deriv_le` — the `ω`-integrand is dominated by
     `B̃₀|𝓕f|` uniformly in `t`), `continuous_TopS_t`, and
     **`norm_TopS_le_add_intervalIntegral`**:
     `|T_bf(x)| ≤ |T_af(x)| + ∫_a^b |T_s[m̃]f(x)|ds` for `a ≤ b`.
     The `MultData` package for `m̃` and the `t`-derivative data for `m` are hypotheses, to be
     supplied when the symbol class is instantiated (`B̃₀ ≈ 2^jB₀`, paid for by the length
     `2^{-j}` of the interval).
     **Next:** the discretization itself — `ℰ_j = {n2^{-j} : I_{n,j} ∩ E ≠ ∅}` with its counting
     data from the Assouad bridge (`intervalCount_of_assouad`), the pointwise `ℓ^q`-bound for
     `sup_{t∈E}` in terms of the `ℰ_j`-sum, and Minkowski's integral inequality for the
     `ds`-integral, giving Theorem 2.1 (the paper's `thm:Q4`).
  6. §2 and the bridge into the repository.  The concrete target is the repository's leaf
     `exists_q4_sector_dyadic_rate` (and its `L²` and lower-input variants), whose statement is:
     for exponents strictly inside the region there are `C < ∞` and `ρ < 1` with
     `‖fractalDyadicBandpassMaximal d E (absoluteDyadicBandpass φ j) f‖_q ≤ Cρ^j‖f‖_p`.  So the
     endpoint estimate of §3 has to be transferred to the repository's dyadic bandpass maximal
     operator and then interpolated against the `L²` bound (exactly as the repository's
     `Q4PlanarCriticalParameters`/`...upper_sector_strict_dyadic_rate` does for `γ ≤ 1/2`).
     The audit shows the `hd` hypothesis is consumed at
     only three genuinely `γ`-dependent leaves — `exists_q4_sector_dyadic_rate`,
     `exists_q4_ltwo_sector_dyadic_rate`, `exists_q4_lower_sector_explicit_dyadic_rate` — while
     the remaining uses are spurious (`exists_theoremOneSharpSurfaceFourierInput`, for instance,
     discards `γ ≤ 1/2` and needs only `2 ≤ d`), and the `Seg` branch for `d = 2` needs
     `γ ≤ 1/2` only to get `β < 1`, which for `p > 2` is supplied instead by the repository's
     unconditional `Auto.Spherical.Bourgain.bourgainCircularMaximal`.

  **Old next (superseded):** §3 of the paper.  Radius discretization (`ℰ_j = {n2^{-j} : I_{n,j} ∩ E ≠ ∅}`) and the
  fundamental theorem of calculus to pass from `sup_{t∈E}` to `sup_{t∈I_{n,j}}`; bilinearization
  `(∑_t ‖T_t f‖_q^q)^{1/q} = ‖𝒯_j(f⊗f)‖_{L^{q/2}}^{1/2}`; analytic (Stein) interpolation of
  Proposition 3.1 against the trivial `L^∞` bound, using the repository's `stein_interpolation`;
  and one-dimensional fractional integration, for which
  `LeanSpherical/Auto/HardyLittlewoodSobolev.lean` is authorized and not yet created.
  Then §2 (interpolation with `Q₁,Q₂,Q₃`, summation over `j`) and the wiring into
  `exists_q4_sector_dyadic_rate` / `exists_q4_ltwo_sector_dyadic_rate`.

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

### The `L^1_{y_1}L^∞_{y_2} → L^∞` endpoint of §3 (eqn. (3.14) of the paper)

The interpolation in §3 needs, besides Proposition 3.1, the endpoint

  `sup_{x,t} |𝒯F(x,t)| ≲ 2^j ∫ sup_{y_2,z_2} |F(y,z)| d(y_1,z_1)`,

which the paper deduces from a pointwise bound for the kernel `K_{j,t}(y,z) = k_{j,t}(y) k_{j,t}(z)`
(a linear combination of five explicit terms).  Since the bilinear kernel factors, everything
reduces to the *single* kernel estimate

  (K)   `sup_{u_1} ∫ |k_{j,t}(u_1,u_2)| du_2 ≲ 2^{j/2}`  where `k_{j,t} = 𝓕^{-1}(mfull)`.

The paper's five-term kernel bound is the classical asymptotics of the Fourier transform of the
circle (Bessel asymptotics with symbol-valued amplitudes).  Rather than formalizing an asymptotic
expansion, (K) is obtained here by a **plate decomposition in polar coordinates**, which needs only
integration by parts:

* in polar coordinates the phase is exactly `ρ ψ_u(φ)` with `ψ_u(φ) = ⟨u,θ(φ)⟩ + εt`, i.e. it is
  *linear in the radius*, so the radial integration by parts is trivial and gains
  `(2^j|ψ|)^{-1}` per step with no error terms (`norm_integral_osc_linear_ibp4`);
* the angle is cut into plates of length `2^{-M}`, `M = ⌈j/2⌉`, by the telescoping cutoffs
  `plateC M ν` (`plateC_nonneg`, `plateC_le_one`, `sum_plateC`, `plateC_eq_zero_of_nonpos`,
  `plateC_eq_zero_of_two_le`, `abs_plateC_deriv_le`).  On each plate two integrations by parts in
  the angle, whose phase derivative is `ρψ'_u(φ)`, gain `(2^{M}|ψ'|)^{-1}` per step
  (`norm_integral_osc_ibp2_bound`, via the explicit chain `chainB`, `chainC`);
* the two bounds are then combined by `min(a,b) ≤ √(ab)`, which turns the radial gain `4` and the
  angular gain `2` into the *integer* exponents `2` and `1`, with the powers of `2^{±M}`
  cancelling exactly:

    `|k_ν(u)| ≲ B₀ 2^{2j-M} (1 + 2^jμ_ν(u))^{-2} (1 + 2^{M}μ'_ν(u))^{-1}`,
    `μ_ν = min_{plate}|ψ_u|`, `μ'_ν = min_{plate}|ψ'_u|`;

* integrating in `u_2` (where `∂_{u_2}ψ = cosφ ≈ 1`) costs `2^{-j}`, and summing over the
  `≈ 2^{M-10}` plates costs `O(j)` because `2^{M}ψ'_u(φ_ν)` is spaced by `≈ t ≥ 1` in `ν`.
  The total is `2^{2j-M}·2^{-j}·O(j) ≈ 2^{j/2}·O(j)`.

The polynomial loss `O(j)` (from using the exponent `1` rather than `1+δ` in the angular factor) is
harmless: as recorded in judgment call 5, the target downstream is a geometric rate `Cρ^j`,
`ρ < 1`, so any factor `(1+j)^C` is absorbed.

Both plate estimates are now proved: **`norm_radial_integral_le`** (radial, four integrations by
parts, `‖∫_ρ‖ ≤ B₀ 2^{-2j}|ψ|^{-4}`) and **`norm_angular_plate_le`** (angular, two integrations by
parts on a plate, `‖∫_φ‖ ≤ 5·stC·B₀(1+‖u‖)² 2^M/(r·μ'²)` whenever `μ' ≥ 2^{-M}` on the plate).
The plate decomposition is also in place: `kernRad`, `kernPlate`, `mem_sector_angle` (the angular
support is contained in `(1,π/2)`), `integrableOn_kernRad`, `integrableOn_plate_kernRad`,
**`kern_eq_sum_plates`** (`kern = ∑_{ν ∈ [0, ⌈π2^M⌉]} kernPlate ν`, the plate cutoffs telescoping
to `1` on the angular support), `norm_kernRad_le_trivial`, and **`norm_kernPlate_le_radial`**
(the radial route for one plate).  The angular route is also complete:
`sin_cos_pos_of_ne`, `kernPlate_eq_radius_outer` (the Fubini swap putting the radius outside),
`plateC_eq_zero_of_not_mem`, `angular_integral_eq` (for a fixed radius the plate-weighted angular
integral is the interval integral of `osc·angAmp` over the plate), `angular_integral_eq_zero`
(vanishing off the frequency annulus) and **`norm_kernPlate_le_angular`**
(`‖kernPlate ν‖ ≤ 80·stC·B₀ 2^M/μ'²`, whose hypotheses bound `|ψ''| = |εt - ψ|` and
`|ψ'''| = |ψ'|` on the plate rather than `‖u‖`, so that no factor of `‖u‖` enters).

The remaining assembly of (K), designed and verified on paper, integrates in `u_2 = v` (with
`u_1 = w` fixed) and sums over plates.  The bookkeeping that makes it work:

* the two routes are combined *without* square roots by `K ≤ R, K ≤ A, R·A ≤ Z² ⟹ K ≤ Z`;
* the radial route is first capped against the trivial bound, `min(T,R) ≤ 512·Q·B₀2^{2j}(1+2^jμ)^{-4}`,
  so that the resulting `u_2`-bound is integrable; with `A = c·stC·B₀·2^M/μ'²` this gives
  `‖kernPlate ν‖ ≤ c'·stC·B₀·2^j(1+2^jμ_ν)^{-2}/μ'_ν`;
* `μ_ν` is the *minimum* of `|ψ|` over the plate, and the difference from its value at the plate's
  endpoint `φ_ν` is at most `2Q·max_{plate}|ψ'| ≤ 16Qμ'_ν`.  Each plate's `v`-integral is therefore
  split at `|ψ(φ_ν)| = 32Qμ'_ν`: on `{|ψ(φ_ν)| ≥ 32Qμ'_ν}` one has `μ_ν ≥ |ψ(φ_ν)|/2` and, since
  `ψ(φ_ν)` is *affine in `v`* with slope `sin φ_ν ≥ sin 1 > 0.8`, `integral_inv_one_add_abs_sq_le`
  gives `∫(1+2^jμ_ν)^{-2}dv ≲ 2^{-j}`, whence a contribution `≲ stC·B₀/μ'_ν`; on the complementary
  set — of measure `≲ Qμ'_ν` — the *angular* bound `A` is used instead, contributing
  `≲ stC·B₀·2^M·Q/μ'_ν` as well.  Both are `≲ stC·B₀·2^M/k` for the plate at distance `k` from the
  resonant one, so the plate sum is `≲ stC·B₀·2^M·log(2^M)`, i.e. `2^{j/2}` up to a factor `j`;
* the resonance geometry comes from the exact sinusoid form `ψ = ‖u‖ sin(φ+δ) + εt`,
  `ψ' = ‖u‖ cos(φ+δ)`, which gives `μ'_ν ≳ ‖u‖·|θ_ν - θ*| ≳ ‖u‖ k Q` with `θ*` the nearest zero of
  the cosine, together with `‖u‖ ≥ 1/2` wherever `|ψ| ≤ 1/2`;
* since `|ψ''| = |εt - ψ|` is bounded by `2 + |ψ| ≤ 3 + 24μ'` on all the sets where the angular
  route is used, the angular estimate is stated with that hypothesis, and no restriction on `‖u‖`
  is needed anywhere.

All the ingredients of this assembly are now proved: `norm_kernPlate_le_of_kernRad_le` (with the
radial, trivial and **capped** specializations `norm_kernPlate_le_radial`,
`norm_kernPlate_le_trivial`, `norm_kernPlate_le_capped`), `le_of_sq_le_mul` (the square-root-free
combination), `integral_inv_one_add_abs_sq_le` (`∫(1+A|av+b|)^{-2}dv ≤ 2π/(Aa)`, by domination by
the Cauchy kernel), `exists_phase_shift` (the sinusoid form), `abs_sin_ge_half` (Jordan),
`cosDist` with `cosDist_le`, `abs_cos_ge`, `cosDist_le_of_int`, `cosDist_sub_le` and
**`abs_psi1_ge`** (`‖u‖·cosDist(φ+δ)/2 ≤ |ψ'(φ)|`), `abs_sub_le_cosDist_add` (the clustering of the
resonant plates, using that the zeros of the cosine are `π`-separated), and `harmonic_dyadic` /
`harmonic_le` (`∑_{k≤2^L} 1/k ≤ L+1`).

The assembly itself is now under way, in the form described below.  Proved so far:
`psi2_eq` (`ψ'' = εt - ψ`), `psi3_eq_neg` (`ψ''' = -ψ'`), `psiu_mk2`/`psi1_mk2` (both are affine in
the second coordinate `v`), `sq_psi1_add_sq` (`ψ'² + (ψ-εt)² = ‖u‖²`), `norm_le_psi`,
`abs_psiu_sub_le`/`abs_psi1_sub_le` (`‖u‖`-Lipschitz in the angle) and the sharper mean value
versions `abs_psiu_sub_le_of_bound`/`abs_psi1_sub_le_of_bound`, `sin_ge_of_near`/`abs_cos_le_of_near`
(the sector angles have `sin φ ≥ 4/5`, `|cos φ| ≤ 3/5`), **`psi1_ref_identity`**
(`ψ'(φ)·sin φ = cos φ·ψ(φ) - (w + εt cos φ)`, which is what makes the plate parameter
`A_ν := w + εt cos φ_ν` *independent of `v`*), **`plate_bounds_far`** (on a far plate, in the region
`|ψ(φ_ν)| ≤ |A|/2`: `|ψ'| ∈ [|A|/3, 8|A|/3]`, `|ψ''| ≤ 3 + 24(|A|/3)` and
`|ψ| ≥ |ψ(φ_ν)| - 6Q|A|`), **`norm_kernPlate_far_le`** (the combined bound
`‖kernPlate ν‖ ≤ 4000·stC·B₀·2^j(1+2^jμ)^{-2}/|A|`), and **`integral_capped_le`**
(`∫(1 + A·max 0 (|av+b| - slack))^{-2}dv ≤ 5·slack + 5π/A`).

The far plates are now completely done: `plate_bounds_far2` and `norm_kernPlate_far2_le` (the
complementary region `|ψ(φ_ν)| > |A|/2`, where the capped radial route alone suffices),
`norm_kernPlate_ang_le`, **`norm_kernPlate_far_majorant`** (a single pointwise majorant valid for
all `v`, made of two capped quadratic bumps: the flat core uses the angular bound, the intermediate
region the combined bound, the far region the capped radial bound), and
**`lintegral_kernPlate_far_le`**:

  `∫⁻_v ‖kernPlate ν (w,v)‖ₑ ≤ 2·10⁶ · stC · B₀ / |A_ν|`   for every plate with `|A_ν| ≥ 100·2^{-M}`.

The near plates and the geometry of the plate parameters are done as well:
`plate_bounds_near`, **`exists_near_majorant`** (`∫ G ≤ 7·10⁶·B₀·2^M`),
`kernPlate_eq_zero_of_angle` (a plate whose reference angle is more than `3/5` from `π/2` misses the
angular support entirely), **`exists_plate_majorant`** — a *uniform* statement covering all three
cases (far, near, outside):

  `∫ G_ν ≤ 7·10⁸·(1+stC)·B₀ / max(2^{-M}, |A_ν|)`,

and **`plA_separated`**: `(2/5)|ν-ν'| 2^{-M} ≤ |A_ν - A_{ν'}|` for two plates in the angular range,
because the `w` cancels in `A_ν - A_{ν'} = εt(cos φ_ν - cos φ_{ν'})` and
`|cos x - cos y| = 2|sin((x+y)/2)||sin((x-y)/2)| ≥ 2·(4/5)·|x-y|/4`.

What remains for (K) is the plate sum `∑_ν 1/max(2^{-M},|A_ν|) ≲ 2^M(1+M)` — which follows from the
separation via the minimizing plate `ν₀`, the bound `|A_ν| ≥ (1/5)|ν-ν₀|2^{-M}` and `harmonic_le` —
and then the assembly.

The sinusoid form makes every case distinction of that assembly elementary.  Writing
`ψ = R sin θ + εt`, `ψ' = R cos θ`, `ψ'' = -R sin θ`, `ψ''' = -ψ'` with `R = ‖u‖`, `θ = φ + δ`:

* on the `v`-region `|ψ(φ_ν)| ≤ 1/2` one has `R|sin θ| ≤ 3/2`, hence `|ψ''| ≤ 3` — the angular
  estimate's hypothesis holds for *every* plate, with no bound on `R`; and `R|sin θ| ≥ t - 1/2 ≥ 1/2`
  gives `R ≥ 1/2`, which is what the plate sum `∑ 1/(R d_ν)` needs;
* a *near* plate (`d_ν := cosDist(φ_ν+δ) ≲ Q`) has `|cos θ| ≲ Q`, hence `|sin θ| ≥ 1/2` and
  therefore `R ≤ 6` on that region — the slack `2Q·max|ψ'| ≤ 2QR·(d_ν+2Q)` in the radial bound is
  then `O(4^k 2^{-j})` as needed;
* a *far* plate has `μ'_ν ≈ R d_ν` with `d_ν ≳ Q`, so `|ψ''| ≤ R ≤ 24 μ'_ν` holds however large `R`
  is, and the angular route applies;
* on the complementary `v`-region `|ψ(φ_ν)| > 1/2`, a near plate has `|sin θ| ≈ 1`, hence
  `R ≈ |ψ|`, so the slack `2QR` is a *fraction* of `|ψ(φ_ν)|` and the capped radial bound keeps its
  decay; a far plate again uses the angular route.

Built and verified so far for this endpoint: `norm_integral_osc_ibp_thrice`,
`norm_integral_osc_linear_ibp3`, `norm_integral_osc_linear_ibp4`, `norm_integral_osc_ibp2_bound`
(with `chainB`, `chainB1`, `chainC`, `norm_chainC_le`), `integral_polar_angle_outer`,
`integral_polar_radius_outer`, `enorm_integral_polar_le_angle`, `enorm_integral_polar_le_radius`,
`psiu`, `psiu_eq`, `psi1`, `psi2`, `psi3` with all derivatives and bounds, `kern`,
`kern_polar_pt`, `PolarData`, `radAmp`…`radAmp4` with their derivative chains,
`radial_integral_eq`, **`norm_radial_integral_le`** (the radial estimate
`‖∫_ρ‖ ≤ B₀ 2^{-2j}|ψ|^{-4}`), and the plate cutoffs listed above.  Also
`norm_integral_osc_vdc` (van der Corput's second-derivative test) and `norm_integral_osc_conj`,
which were built first and remain available.

### The interpolation of §3: design (settled, not yet formalized)

With Proposition 3.1 (Milestone 4) and the endpoint (Milestone 6) both available, §3 needs the
**analytic interpolation** of the paper.  Two cheaper substitutes were examined and *ruled out*:

* *Hölder in the output* (`‖SF‖_p ≤ ‖SF‖_2^θ‖SF‖_∞^{1-θ}`) loses exactly the gain the theorem is
  about: for `f = χ_{[0,N]×[0,1]} + χ_{[0,1]×[0,N]}` the resulting product of the two endpoint
  norms exceeds `‖f‖_{p₄}²` by `N^{(2γ-1)/p₄}`.  (Both single terms are sharp; it is the sum that
  breaks it, which is precisely what a genuine interpolated norm handles.)
* *Applying HLS first* (to turn the weighted `L²` mass into the mixed norm
  `L^{4/(3-2γ)}_{y₁}L²_{y₂}` and then interpolating unweighted mixed norms) fails at `γ = 1`,
  where the exponent `λ = 2γ-1 = 1` is the critical one for HLS on the line.  The paper's order
  — interpolate first, Hölder + HLS afterwards, where `λ = (2γ-1)p'/p < 1` strictly — is
  therefore essential.
* The repository's `Auto.stein_interpolation` cannot be used: it requires the endpoint bounds for
  *all* simple functions in a single `L^{p_i}(μ)` on each side, while here one endpoint input is
  a weighted `L²(ℝ⁴)` and the other the mixed `L¹_{(y₁,z₁)}L^∞_{(y₂,z₂)}`; a fixed-weight
  multiplier family gives the wrong exponent (`p = 2(3+2γ)/(2γ-1)` instead of `p₄`), and an
  `f`-dependent one violates the "for all `g`" hypothesis.

So the interpolation has to be run by hand on the strip, with the **Calderón factorization**
below (derived and checked; it is the only step that was not obvious).  Notation: `S = 𝒯j`,
`μ` = Lebesgue × counting on `ℝ²×ℰ`, `p = p₄ = (3+2γ)/2`, `1-θ = 2/p` (so the `L²`-endpoint carries
the weight `1-θ`, the `L^∞`-endpoint `θ`),
`Φ(y₁,z₁) = (∫∫|F(y,z)|^p d(y₂,z₂))^{1/p}`, `W = |y₁-z₁|^{(1-2γ)/p}` (so `W^p` is the weight of
Proposition 3.1 after `|y-z| ≥ |y₁-z₁|`), `u = WΦ`, `N = ‖u‖_{L^{p'}} = N_p(F)`.
Endpoints: `X₀ = L²(W^p)`, `X₁ = L¹_{(y₁,z₁)}L^∞_{(y₂,z₂)}`; outputs `L²(μ)`, `L^∞(μ)`.
Then, with `N = 1`,

    G₀ = |F|^{p/2} Φ^{1-p/2} Ψ₀,    Ψ₀ = (W u^{p'-1})^{-(p-2)/2},
    G₁ = Φ Ψ₁,                  Ψ₁ = W u^{p'-1},

satisfies `|F| = G₀^{1-θ} G₁^{θ}` (fibrewise: `|h| = h₀^{2/p}h₁^{1-2/p}` with
`h₀ = |h|^{p/2}‖h‖_p^{1-p/2}`, `h₁ = ‖h‖_p`; in the base `Ψ₀^{2/p}Ψ₁^{1-2/p} = 1`), together with
`‖G₀‖_{X₀}² = ∫∫ Ψ₀²Φ²W^p = ∫∫ u^{p'} = 1` and `‖G₁‖_{X₁} = ∫∫ Ψ₁Φ = ∫∫ u^{p'} = 1`
(all `W`-powers cancel exactly, using `(p'-1)(p-2) = (p-2)/(p-1)` and `2 - (p-2)/(p-1) = p'`).
The family is `F_ζ = (F/|F|)·G₀^{1-ζ}G₁^{ζ}`, so `F_θ = F`, `|F_{iτ}| = G₀`, `|F_{1+iτ}| = G₁`;
the test function on the output side gets the classical `|φ|^{r(ζ)}` family for the couple
`(L², L¹)`.  Three lines then gives
`|⟨SF, φ⟩| ≤ A^{1-θ}B^{θ}` for `‖φ‖_{p'} = 1`, i.e. `‖SF‖_{L^p(μ)} ≤ A^{1-θ}B^{θ}N_p(F)`.
After that, the paper's chain is elementary: `F = f⊗g`, Hölder in `y₁` with exponents `p/p'` and
`(p/p')'`, and the bilinear HLS of Milestone 5 with `λ = (2γ-1)p'/p < 1` and `r = p/p'`, which is
exactly the symmetric exponent `2/(2-λ)` for `p = p₄` — giving `N_{p₄}(f⊗g) ≲ ‖f‖_{p₄}‖g‖_{p₄}`.

### Status of §3 (as of the endpoint being finished)

Built and compiling in `RS.lean` (18 648 lines, `sorry`-free, standard axioms), in the forward
order of the proof:

* `Top2 j ε m t F x = ∫_{ℝ⁴} k(x-y)k(x-z)F(y,z)` — the operator `𝒯_j` of §3 defined by its kernel,
  for arbitrary `F` (not only tensors, which the interpolation needs);
  `mix2 F = ∫⁻_{(y₁,z₁)} sup_{(y₂,z₂)}‖F‖` — the mixed norm of the endpoint.
* `enorm_Top2_le_mix2` — the endpoint (3.14) for `𝒯_j`: `‖𝒯_jF(x,t)‖ ≤ C² mix2 F`,
  for every measurable `F`, with `C` the constant of the single-kernel estimate (K).
* `Top2_tens` — `𝒯_j(f⊗g) = T_tf·T_tg` (the bilinearization identity), via
  `TopS_eq_conv_left`.
* `Top2S`, `kern2S`, `Top2S_eq_convolution`, `Top2_eq_Top2S` — the kernel operator equals the
  `ℝ⁴` multiplier operator restricted to the diagonal, `𝒯_jF(x) = (𝓕⁻(m⊗m·𝓕F))(x,x)`.
* `wMass1`, `wMass_le_wMass1` — the weight `|y-z|^{-(2γ-1)}` of Proposition 3.1 may be replaced by
  `|y₁-z₁|^{-(2γ-1)}`, as the paper does before interpolating.

Also built (this completes **both endpoints of the interpolation for arbitrary Schwartz data on
`ℝ⁴`**):

* `Top2S`, `kern2S`, `Top2S_eq_convolution`, `Top2_eq_Top2S` — the kernel operator is the `ℝ⁴`
  multiplier operator restricted to the diagonal.
* `Hmul`, `Sop_eq_integral_Hmul`, `exists_decay_Pl2`, `integrable_inv_one_add_norm_cube`,
  `continuous_Sop`, `integrable_Sop` — `ξ ↦ S[F,bprod m](ξ,t)` is continuous and integrable
  (majorant `K(1+‖η‖)^{-3}` from the Schwartz decay of `mfull⊗mfull·𝓕F`, plus the shear identity
  `lintegral_pr_shift` for the integrability).
* `diagCLM`, `diagS`, `Top2S_diag_eq_fourierInv_Sop`, `fourier_diagS_Top2S` — the frequency-side
  identification `𝒯_jF(·,t) = 𝓕⁻(S[F,bprod m](·,t))`, proved by Fubini and the shear
  `(u,v) ↦ (u+v,v)` (`shiftME`, `measurePreserving_shiftME`), and then inverted with Mathlib's
  Fourier inversion theorem (which is what the continuity and integrability above are for).
* `lintegral_enorm_sq_Top2` — Plancherel: `‖𝒯_jF(·,t)‖_{L²} = ‖S[F,b](·,t)‖_{L²}`.
* **`prop31_Top2`** — Proposition 3.1 in physical space for arbitrary Schwartz `F` on `ℝ⁴`:
  `∑_{t∈ℰ}‖𝒯_jF(·,t)‖²_{L²} ≤ c(M+2)²B₀⁴Na2^{2j}‖F‖²_{L²(w_γ)}`.

What remains before the interpolation can be run is that its Calderón family members
(`G₀`, `G₁` above) are *not* Schwartz: they are bounded, compactly supported and measurable.  The
`L^∞` endpoint (`enorm_Top2_le_mix2`) already holds for every measurable `F`; the `L²` endpoint has
to be extended from Schwartz data to that class.  The route (checked, not yet formalized):

1. `|𝒯_jF(x,t)| ≤ ‖k_{j,t}‖²_{L²}‖F‖_{L²(ℝ⁴)}` by Cauchy–Schwarz, so `𝒯_j` is continuous from
   `L²(ℝ⁴)` to `L^∞` and `L²`-convergence gives uniform convergence of the images.
2. For `G` bounded, compactly supported and supported in `{|y₁-z₁| ≥ δ}`, Mathlib's
   `HasCompactSupport.exist_eLpNorm_sub_le` gives smooth compactly supported (hence Schwartz)
   `g_n → G` in `L²`; multiplying `g_n` by a fixed smooth cutoff that vanishes for
   `|y₁-z₁| ≤ δ/2` keeps the approximants in the region where `w_γ` is bounded, so they also
   converge in `L²(w_γ)`; Fatou then transfers the estimate from `g_n` to `G`.
3. A general bounded compactly supported `G` is handled by `G·1_{|y₁-z₁|>δ} → G` (dominated
   convergence in the kernel integral, then Fatou again), which is where the truncation of step 2
   comes from.  Note that this step is what makes the argument work at `γ = 1`, where `w_γ` is not
   locally integrable in `(y₁,z₁)`.

That plan is now carried out.  Built for it:

* `Ckern`, `norm_kern_le`, `integrable_Top2_integrand`, `norm_Top2_le_L1`
  (`‖𝒯_jh‖_∞ ≤ ‖mfull‖²_{L¹}‖h‖_{L¹}`), `Top2_sub`, `continuous_Top2`,
  `tendsto_Top2_of_tendsto_L1` — `𝒯_j` is bounded `L¹(ℝ⁴) → L^∞` and continuous, so `L¹`
  convergence of the data gives pointwise convergence of the images.
* `sepFst`, `cutDiag`, `cutBall`, `cutBoth` — smooth cutoffs on `ℝ⁴` (`Real.smoothTransition` of
  `(y₁-z₁)²` and of `‖q‖²`), with `cutBoth = 1` where `|y₁-z₁| ≥ δ`, `‖q‖ ≤ R`, vanishing where
  `|y₁-z₁| ≤ δ/2` or `‖q‖ ≥ 2R`, and compactly supported.
* `memLp_of_bdd_support`, `abs_sepFst_le`, `wMass_le_of_away` (the weight is bounded on functions
  supported away from the diagonal), `wMass_le_four_add` (a quasi-triangle inequality),
  `lintegral_enorm_le_sqrt` (Hölder on a ball), `lintegral_enorm_sq_le_of_eLpNorm`.
* **`prop31_Top2_away`** — the `L²` endpoint for bounded measurable data supported in
  `{|y₁-z₁| ≥ δ} ∩ {‖q‖ ≤ R}`, with the constant of Proposition 3.1 times `4`.  Proof: Mathlib's
  `MemLp.exist_eLpNorm_sub_le` gives smooth compactly supported approximants, `cutBoth` keeps them
  in the region where the weight is bounded, and Fatou (with the finite `t`-sum moved inside the
  integral) transfers the estimate.
* **`prop31_Top2_bdd`** — the same for *all* bounded compactly supported measurable data, by
  truncating to `{|y₁-z₁| ≥ 1/(n+1)}` (the diagonal `{y₁ = z₁}` is null, `volume_sepFst_eq_zero`),
  dominated convergence for the kernel integral and Fatou again.  This is the class in which the
  Calderón family's `G₁` lives, and the `L^∞` endpoint already holds for every measurable function.

The `L²` endpoint is now available on the whole class the Calderón family lives in:

* `exists_decay_Pl`, `integrable_inv_one_add_norm_pow5`, `lintegral_enorm_sq_mul_one_add_lt_top`,
  `enorm_sub_le_one_add_mul_one_add` (`‖y-z‖^s ≤ (1+‖x-y‖)(1+‖x-z‖)` for `0 ≤ s ≤ 1`),
  `CKx`, **`CKx_lt_top`** — the kernel of `𝒯_j` is square integrable against the polynomial weight
  `‖y-z‖^{2γ-1}`, uniformly in `x`.
* **`lintegral_kern_mul_le`** — the weighted Cauchy–Schwarz bound
  `∫⁻ ‖k(x-y)k(x-z)F‖ ≤ CK(x)^{1/2}(wMass γ F)^{1/2}` (the diagonal, where the weight is `∞`, is
  null), hence `integrable_Top2_integrand_of_wMass`: `𝒯_jF(x,t)` is defined by an absolutely
  convergent integral whenever `wMass γ F < ∞`.
* `measurable_Top2` (via `StronglyMeasurable.integral_prod_right'`, no continuity needed) and
  **`prop31_Top2_wmass`** — Proposition 3.1 in physical space for *every* measurable `F` with
  `wMass γ F < ∞`, by truncating `F·1_{‖F‖ ≤ n}·1_{‖q‖ ≤ n}`, dominated convergence and Fatou.

So both endpoints of the interpolation are in place: `prop31_Top2_wmass` (`L²`, any `F` of finite
weighted mass) and `enorm_Top2_le_mix2` (`L^∞`, any measurable `F`).

What remains is the Phragmén–Lindelöf step itself.  Mathlib's
`Complex.PhragmenLindelof.vertical_strip` is the tool (the repository's `SteinInterpolation` wraps
it in a private `three_lines_common_bound`, so a small public copy is needed here), together with
the reduction of the two-constant three-lines statement to the common-bound one by the entire factor
`M₀^{z-1}M₁^{-z}`.  The one real design question is **analyticity of
`Ψ(ζ) = ∑_t ∫ 𝒯_j(F_ζ)·φ_ζ`**.  Two routes were examined:

* *Differentiation under the integral* (`hasDerivAt_integral_of_dominated_loc_of_lip`, which does
  work for `𝕜 = ℂ`): the pointwise ζ-derivative of `F_ζ = ω G₀^{1-ζ}G₁^{ζ}` is
  `F_ζ·log(G₁/G₀)`, and `|F_ζ| ≤ G₀ + G₁` is dominated, but the `log` factor is not — one would
  need two-sided bounds on `u^{p'}/|F|`, which do not hold.
* *Rectangle-simple data with a step weight* (chosen): if `F` is a finite sum
  `∑ c_i 1_{A_i × B_i}` (base × fibre rectangles), bounded, compactly supported and supported away
  from the diagonal, and the weight `W` is replaced by a simple `W̃` with `W ≤ W̃ ≤ (1+η)W` on that
  region, then `Φ`, `Ψ₀`, `Ψ₁`, hence `G₀`, `G₁`, are simple, so `F_ζ` is a finite sum of
  indicators with coefficients `c^{1-ζ}d^{ζ}` — entire in `ζ` and bounded on the closed strip, so
  both the analyticity and the growth hypothesis of Phragmén–Lindelöf are immediate.  The `(1+η)`
  and the truncations are then removed by the same kind of limiting arguments as above.

**Built for the interpolation so far.**

* **`three_lines`** — Hadamard's three lines lemma in the bounded case,
  `‖Ψ(θ)‖ ≤ M₀^{1-θ}M₁^{θ}`, from Mathlib's `PhragmenLindelof.vertical_strip` applied to
  `Φ(z) = Ψ(z)e^{(z-1)log M₀}e^{-z log M₁}` (whose modulus is `‖Ψ‖M₀^{Re z-1}M₁^{-Re z}`, hence
  `≤ 1` on both edges and bounded on the strip, so the growth hypothesis holds with `c = 0 < π`).
* `pairT`, `outL2`, `outL1` — the pairing `⟨𝒯_jF, φ⟩` over `ℝ²×ℰ` and the two output-side norms,
  with the two endpoint bounds `enorm_pairT_le_sup` (`≤ B‖φ‖_{ℓ¹L¹}`) and `enorm_pairT_le_L2`
  (`≤ A‖φ‖_{ℓ²L²}`, via Hölder in `x` and the discrete Cauchy–Schwarz
  `ENNReal.inner_le_Lp_mul_Lq` over `ℰ`).
* `sepFst_pr_mk2`, **`wMass1_iter`** — the weighted mass in base–fibre coordinates,
  `∫⁻_{y₁}∫⁻_{z₁}∫⁻_{y₂}∫⁻_{z₂}`, which is the form in which the Calderón factorization is stated
  (the fibre profile `Φ` and the weight `W` are functions of the base variables).  With `mix2`
  already in that form, no explicit `ℝ⁴ ≅ (base)×(fibre)` equivalence is needed.

* The **Calderón factorization** is built, in base–fibre coordinates: `fibProf` (the fibre `L^p`
  profile `Φ`), `wtB` (`W = |y₁-z₁|^{(1-2γ)/p}`), `uB` (`u = WΦ`), `normNpp` (`N_p(F)^{p'}`),
  `psi1B` (`Ψ₁ = Wu^{p'-1}`), `psi0B` (`Ψ₀ = Ψ₁^{-(p-2)/2}`), `gZero`, `gOne`, with all
  measurability lemmas, and the three identities that make it work:
  * `calderon_alg1`, `calderon_alg2` — the ENNReal rpow algebra `ΦΨ₁ = u^{p'}` and
    `Ψ₀²Φ²W^p = u^{p'}` (the second needs `0 < W < ∞`, i.e. off the diagonal, and `Φ < ∞`);
  * **`lintegral_gOne`** — `∫⁻∫⁻ G₁ = N_p(F)^{p'}` (the `X₁` norm of the second factor);
  * **`lintegral_gZero_sq_weight`** — `∫⁻∫⁻∫⁻∫⁻ G₀²|y₁-z₁|^{-(2γ-1)} = N_p(F)^{p'}` (the `X₀`
    norm of the first factor), by integrating out the fibre (`fibProf_pow`) and then
    `calderon_alg2`;
  * **`calderon_factorization`** — `|F| = G₀^{2/p}G₁^{1-2/p}` pointwise wherever `0 < Φ < ∞` and
    `y₁ ≠ z₁`, with `calderon_factorization_zero` for the degenerate fibres.

* The **families** are defined: `rpowC` (complex powers of nonnegative reals, `0^w = 0`), `signC`
  (unimodular sign), with their norms, additivity, entirety in the exponent and measurability;
  `bs1`/`fb1`/`bs2`/`fb2` (base and fibre coordinates, `pr_bs_fb`), the finiteness lemmas
  `gOne_ne_top`, `gOne_ne_zero`, `gZero_ne_top`, `psi1B_ne_zero`, `psi1B_ne_top`, and
  **`Ffam`** (`F_ζ = sgn(F)G₀^{1-ζ}G₁^{ζ}`), **`phifam`** (`φ_ζ = sgn(φ)|φ|^{p'(1+ζ)/2}`).
  **`Ffam_at_theta`** — the family reproduces `F` at `ζ = θ = 1-2/p` (via `rpowC_toReal_eq` and
  `calderon_factorization`), which is what makes the three-lines conclusion a statement about `F`.

* The **edge data** is complete: `enorm_Ffam_le_gZero` / `enorm_Ffam_le_gOne` (the family's
  modulus at `Re ζ = 0, 1`, including the degenerate fibres and the diagonal, where
  `Ffam_eq_zero_of_degenerate` shows the family vanishes), `wMass1_Ffam_le`, `mix2_Ffam_le`,
  `enorm_phifam_le`, `outL2_phifam_le`, `outL1_phifam_le`, `phifam_at_theta`,
  `measurable_Ffam`, `measurable_phifam`, `differentiable_Ffam`, `differentiable_phifam`, and
  finally the two **edge bounds for the pairing**: **`enorm_pairT_edge0`**
  (`≤ (4KE·N_p(F)^{p'})^{1/2}(∑_t∫|φ|^{p'})^{1/2}`, from `prop31_Top2_wmass`) and
  **`enorm_pairT_edge1`** (`≤ C²N_p(F)^{p'}∑_t∫|φ|^{p'}`, from `enorm_Top2_le_mix2`).

The **interpolation is complete** (see milestone 7): the majorant bounds
(`lintegral_Pl2_iter_base`, `lintegral_sq_weight_iter`, `lintegral_kern_mul_le_gen`, `CKx1`,
`lintegral_kern_translate_le`, `lintegral_kern_gZero_le`, `lintegral_kern_gOne_le`, `CKx_le_sq`,
`enorm_Ffam_le_sum`, `enorm_Top2_Ffam_le`, `majB`, `integrable_majB`), the analytic step
(`continuousOn_Top2_Ffam`, `differentiableOn_Top2_Ffam`, `continuousOn_pairT_fam`,
`differentiableOn_pairT_fam`, with the swap lemmas `intervalIntegral_integral_swap_gen`), the three
lines application (`norm_pairT_interp`) and the duality step (`lintegral_pow_le_of_pairing_le`) all
compile, giving **`lintegral_pow_Top2_le`**.

### The instantiation of `MultData`/`PolarData` — infrastructure in place

The remaining task is to *construct* a multiplier satisfying the two hypothesis packages and to
connect it to the repository's dyadic bandpass maximal operator.  Built so far:

* **Rotations** (`rotF`, `rotLIE`, `rotCLE`): the rotation of the plane by an angle, as a linear
  isometry equivalence, with `norm_rotF`, `inner_rotF`, `rotF_pt` (angle addition),
  `measurePreserving_rotF`, `lintegral_comp_rotF` and **`fourier_comp_rotF`**
  (`𝓕(f∘R) = (𝓕f)∘R`).
* **Builders**: `multData_of_bounds` (a smooth sector-supported multiplier whose `iteratedFDeriv`
  of order `≤ 3` gains `2^{-j}` per derivative satisfies `MultData`, with the canonical second
  derivative field `m2can`), `polarData_of_bounds` (the canonical radial/angular iterated
  derivatives `mrcan`/`macan` satisfy `PolarData`), and the **rescaling** lemmas
  `norm_iteratedFDeriv_rescale`, `multData_of_rescaled` (a fixed-scale symbol composed with
  `2^{-j}•` automatically has the `2^{-nj}` gains).
* **Polar coordinates and the sector cutoff**: `exists_pt_of_norm_one`, `unitVec_pt_one_zero/one`,
  the bumps `angB`, `angC`, the sector cutoff `secCut v = angB(unitVec₀ v)·angC(unitVec₁ v)` and
  `mem_sector_of_secCut_ne_zero`: on the annulus, `secCut ≠ 0` forces `0 < v₁ < 2^{-10}v₂`, i.e.
  membership in the sector of `Θ_j`.
* **The angular partition of unity is complete.**  With `Nsec = 2^17` sectors and spacing
  `hsec = 2π/Nsec ≤ 2^{-14}`, the covering lemma `exists_secCut_rot_pos` shows that every direction
  in the annulus is caught by one of the rotated cutoffs (the window is located by
  `x ↦ π/2 - x` with `sin x ≈ x`, and the index is `⌊y/h + 1/2⌋` reduced mod `Nsec`); `Dsum` is the
  sum of the rotated cutoffs, invariant under a rotation by `hsec` (`Dsum_rotF_step`,
  `Dsum_rotF_nat`, by a shift of the summation index and `Nsec·hsec = 2π`); and
  `psiSec = secCut·annD/(Dsum + 1 - annD)` is smooth everywhere, supported in the sector
  (`sector_of_psiSec_ne_zero`), with
  **`sum_psiSec_rotF`: `∑_{ν<Nsec} psiSec(rotF(-νh)v) = 1` for `1/2 ≤ ‖v‖ ≤ 2`.**

**The plan, simplified.**  Because the multiplier of `A^j_t` is *radial*, all the sector pieces of
the decomposition are **rotations of a single symbol**: with `ψ_ν = ψ_0 ∘ rotF(-νh)` a partition of
unity subordinate to the `N` rotated sectors, the `ν`-th piece of `𝓕(A^j_tf)` is
`M(t,ω)ψ_0(rotF(-νh)ω)`, and `M(t, rotF(νh)v) = M(t,v)`, so
`(the ν-th piece) = (the 0-th piece, applied to f∘rotF(νh)) ∘ rotF(-νh)`.
Hence only **one** symbol `m_0(t,ω) = M(t,ω)ψ_0(ω)` has to be verified against `MultData` and
`PolarData`, and the maximal function of each piece has the same `L^q` norm as that of the first
piece applied to a rotate of `f` (rotations preserve both `L^p` norms).  This removes the need for
any transport of the hypothesis packages under rotations.

### Deferred hypothesis packaging

`MultData` and `PolarData` are *hypotheses* everywhere so far: they record exactly the properties
of the multiplier `m(t,·) = χ_j(·)a(t·)` that each estimate uses (smoothness, support in `Θ_j`,
and derivative bounds with the natural powers of `2^{-j}`, in the Cartesian frame for §4 and in
the polar frame for the §3 kernel estimate).  Constructing the instances from the paper's symbol
class `𝔖⁰` is a single self-contained step, deliberately postponed until the estimates that
consume them are finished, so that the required list of fields is known exactly and does not have
to be revised twice.

## Judgment calls
* **`PolarData.rz` was unsatisfiable and had to be weakened.**  As originally written, the radial
  data package required `mr k t φ r = 0` for every `r ≤ 0`, together with
  `mr 0 t φ r = m t (pt r φ)`.  Since every nonzero `ω` is `pt (-‖ω‖) (ψ+π)`, the two fields
  together forced `m ≡ 0`: the package could never have been instantiated.  The `rz` field now
  demands vanishing only at `r = 0` and for `r > 2^{j+1}`, which is exactly what the two use sites
  (`radAmp*` at the origin, and the far-field truncation) need, and which the canonical radial data
  of a sector-supported multiplier does satisfy.


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

5. **The `j` alternative of Proposition 3.1's `min`.**  The paper's Proposition 3.1 carries the
   factor `min(j^{1/2}(2γ-1)^{-1}, j)`; `prop31` proves the `j` alternative, i.e.
   `c(M+2)² ≤ c(j+2)²` in squared form.  This is what the application needs: the target
   downstream is a *geometric* rate `C ρ^j` with `ρ < 1`
   (`exists_q4_sector_dyadic_rate`), which is obtained in the interior of the exponent region,
   where the polynomial factor `(1+j)^{b₃}` that already appears in the paper's own Corollary 2.2
   is absorbed by `2^{-εj}` with `ε > 0`.  The sharper `j^{1/2}(2γ-1)^{-1}` alternative matters
   only on the boundary segment `Q₁Q₂` and at the endpoint `γ = 1/2`, neither of which is needed
   for Theorem 1.1 in the remaining case `d = 2`, `γ > 1/2`.  Cauchy–Schwarz over the `M+2`
   angular pieces is what produces this factor; obtaining `j^{1/2}` instead would require an
   almost-orthogonality argument between the angular pieces, which the paper's route also does
   not supply at this point.

## Incident and recovery (2026-08-27)

A patch script written through a shell heredoc contained surrogate escape sequences for a
non-BMP character (`𝕜`).  The script opened `RS.lean` for writing (truncating it) and then
raised `UnicodeEncodeError` before writing anything, leaving the file at 0 bytes and
destroying ~26.9k uncommitted lines.

Recovery: the session transcript records every patch command, so the file was rebuilt by
replaying the recorded edit history onto the last committed version (11,535 lines), then
repairing the residual damage by hand.  Three classes of loss had to be fixed manually:

* patch scripts that had been staged via `cat > /tmp/stNNN.py` (a form the first replay pass
  did not recognise) — the `IbpThrice` and `PolarIterated` sections and the `MultData.bdi`
  field;
* patches whose anchors had shifted, notably the fourth-order radial estimate (`ibp4`,
  `radAmp4`, `norm_radial_integral_le`) and the `PolarData.rz` correction;
* a handful of proof steps that had been repaired by later patches which no longer applied.

Final state: `RS.lean` is 26,940 lines, `lake build` is green (3755 jobs), no `sorry`, and
the top-level theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

**Process changes adopted.** Patch scripts are now written with the `Write` tool using
literal characters (never `\uXXXX` surrogate escapes), and every script writes to
`FILE.tmp` and then `os.replace`s it, so a failed write can never truncate the target.
A copy of the last green `RS.lean` is kept in the scratchpad after every successful build.

## Progress (2026-08-27 20:07 EDT) — the hypothesis packages of §3–§4 are instantiated

*Not a milestone under the rule below: this is instantiation infrastructure, not a completed
step of the paper.*

The four hypothesis packages that Theorem 2.1 consumes are now *constructed* for the planar
sector multiplier, with constants independent of the scale and of the dilation.

* **The fixed-scale symbol.**  `gSym φ part J t v = 2^{J/2} χ(t) (φ(v) − φ(2v)) ψ_0(v)
  A_part(t, 2^J‖v‖)` and the sector multiplier `msc φ part J t ω = gSym φ part J t (2^{−J}ω)`.
  `exists_gSym_bound` gives Fréchet-derivative bounds up to any fixed order `N`, uniform in
  `J ≥ 1` and in `t`; `gSym_support` gives support in `Θ_J`.
* **`exists_msc_data`**: `MultData J (msc …) … B` and `PolarData J (msc …) … (384 B)`.
  The polar package comes from a new general builder `polarData_of_rescaled`: the rescaling
  `v = 2^{−J}ω` supplies exactly one factor `2^{−J}` per radial derivative, and the angular
  derivatives are bounded because the support forces the radius to be `≤ 2`.  The radial and
  angular derivative bounds are reduced to the Fréchet bounds by two new lemmas: along a ray the
  iterated derivatives are directional derivatives (`norm_iteratedDeriv_line_le`), and along a
  circle the chain rule costs a bounded factor, because `∂_φ^i (pt ρ φ) = pt ρ (φ + iπ/2)` has
  norm `ρ ≤ 2` on the support (`iteratedDeriv_pt_angle`, `norm_iteratedDeriv_angle_le`).
* **The dilation derivative.**  The amplitude `A_part(a,ρ)` depends only on the *product* `aρ`,
  hence is *symmetric* in its two arguments (`ampR_symm`).  This converts the derivative in the
  dilation into the radial derivative, for which the repository already has the full symbol
  calculus, and gives the identity `∂_t A = (ρ/t) ∂_ρ A` (`ampRD_swap`, `goutDot_eq`).
  Consequently `∂_t gSym` obeys *the same* uniform bounds as `gSym` (`exists_gSymDot_bound`):
  the dangerous factor `2^J` comes only from differentiating the phase.
* **`exists_mtil_data`**: writing `2π ε‖ω‖ = 2π ε 2^J·nrm(2^{−J}ω)` on the support, the symbol
  `mtil ε m ṁ` of `∂_t(e^{2πiεt‖ω‖}m)` is again of the rescaled form (`mtil_msc_eq`), and both
  packages hold for it with the constants multiplied by `2^J` — exactly the loss that the net
  length `δ = 2^{−j}` of Theorem 2.1 pays for.
* Supporting infrastructure: the derivative-bound chain (`exists_iteratedFDeriv_bound_upto`,
  `exists_nrm_deriv_bound`, `exists_cutF_bound`, `exists_ampR_decay`,
  `norm_iteratedDeriv_gout_le`, `norm_iteratedFDeriv_cut_mul_comp_le`) was made generic in the
  order `N`, and the product bound generic in the radial profile, so that the same lemma serves
  the symbol, its dilation derivative and the phase term.
* `hasDerivAt_msc` and `continuous_mscDot` complete the list of hypotheses of
  `lintegral_pow_iSup_TopS_le_of_assouad`.

## Progress (2026-08-27 20:07 EDT) — the operator identity: sectors, rotations and the three waves

*Not a milestone under the rule below: the identity is an ingredient of Theorem 2.5, not a
completed step of the paper.*

The single-scale dyadic spherical average is now written exactly in terms of the sector operator
that Theorem 2.1 estimates.

* **`sector_sum_msc`**: for `1 ≤ t ≤ 2` and every frequency,
  `∑_{ν<N} msc φ part (j+1) t (R_{-νh} ξ) = 2^{(j+1)/2} · A_part(t,‖ξ‖) · ψ_j(ξ)`,
  where `ψ_j` is the repository's `absoluteDyadicBandpass`.  Two observations make this work:
  `absoluteDyadicBandpass φ … j ξ = bpCut φ (2^{-(j+1)}ξ)` exactly (`J = j+1` is forced by the
  repository's normalization), and the multiplier is radial, so the bandpass and the amplitude are
  invariant under the rotations while the sector cutoffs sum to one on the annulus.
* **`waveInt_eq_sector_sum`**: the `part`-wave piece of the average equals
  `2^{-(j+1)/2} ∑_{ν<N} (T_t f_ν) ∘ R_{-νh}` with `f_ν = f ∘ R_{νh}`, where `T_t = TopS` is the
  §3 operator.  The proof changes variables by a rotation inside the Fourier integral
  (`inner_rotF`, `fourier_comp_rotF`, `measurePreserving_rotF`), so no transport of the
  hypothesis packages under rotations is needed.
* **`sphericalAverage_bandpass_eq_wave_sum`**: the average of the bandpass projection is the sum of
  the three coordinate waves (outgoing, incoming, middle), by the repository's normal form
  `planarCoordinateSurfaceWaveSum_eq_three_radialTerms` and Fourier inversion.
* The phase bookkeeping matches: the outgoing wave is the case `ε = -1` and the incoming wave the
  case `ε = +1` of `mfull j ε m t ω = e^{2πiεt‖ω‖} m(t,ω)`.  The middle wave carries no phase and
  is a genuine error term, to be treated separately (it gains a *full* power `‖ξ‖^{-1}` instead of
  `‖ξ‖^{-1/2}`).

## Progress (2026-08-27 20:07 EDT) — the single-scale `Q₄` estimate for one coordinate wave

*Not a milestone under the rule below: one of the three waves at one scale, with the §3 constant
not yet estimated.*

`exists_waveInt_single_scale_bound` now delivers, for the outgoing and the incoming wave and for
every scale `j`, a *measurable majorant* `W` of `sup_{t∈E}|waveInt part j t f|` together with the
bound

    ‖W‖_{L^{2p}} ≤ N · 2^{-(j+1)/2} · KQ4 · ‖f‖_{L^p},   p = p₄ = (3+2γ)/2,

where `N = 2^17` is the number of sectors and `KQ4` is the explicit §3 constant

    KQ4 = C3(…, Na₀, 384B, B, j+1, …)^{1/2}
            + 2·2^{-(j+1)} · C3(…, Na₀, 384·B_t·2^{j+1}, B_t·2^{j+1}, j+1, …)^{1/2},
    Na₀ = 6 + 6·C_Assouad·2^{(j+1)η}.

The uniformity in `f` uses the new monotonicity lemma `C3_mono` (the §3 constant is monotone in
the counting constant `Na` and in the number of shells `Mc`), because Theorem 2.1 produces the
net data inside an existential.  The majorant form is what the reassembly needs: the supremum over
`E` of the wave piece is not obviously measurable, whereas the sector sum is.

### What remains

1. **Estimate `KQ4`.**  `C3` is a product of `ofReal`-factors raised to fixed positive powers, so
   it equals `ofReal` of an explicit real number; with `Mk ≈ (j+1)/2`, `L = Mk+2`, `Mc ≈ (j+1)/2`
   the two powers of `2^j` cancel against the prefactor `2^{-(j+1)/2}`, leaving
   `poly(j)·2^{(j+1)η/(2p)}`.  Hence for every `θ > 0` the single-scale constant is `≤ C_θ 2^{jθ}`.
2. **The middle wave.**  It carries no phase, gains a full power `‖ξ‖^{-1}`, and is handled by the
   trivial multiplier bound plus the frequency-localized `L^p → L^q` improvement.
3. **Reassembly into the repository's operator.**  `fractalDyadicBandpassMaximal 2 E ψ_j f` is
   `(surfaceMass 2)^{-1}` times the supremum of the three wave pieces, so the majorants add.
4. **The `L²` single-scale rate with geometric decay** for `γ < 1` (net + `∂_t`, i.e. the standard
   §2 estimate), which is the second input of the interpolation.
5. **Interpolation and geometry** (§2): the repository's interpolation machinery
   (`exists_q4_upper_activeDyadic_strict_dyadic_rate`, the off-diagonal Marcinkiewicz files) is
   *free of the `hd` restriction* and takes the rates as hypotheses, so it can be reused; what must
   be redone for `d = 2, γ > 1/2` is the triangle geometry whose fourth vertex is the new `Q₄(γ)`,
   including the Stein segment `β = 1`.
6. **Theorem 1.1** into `LeanSpherical/Theorems.lean`.
