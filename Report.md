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

## In progress — `LeanSpherical/Auto/Spherical/FractalDilations/RS.lean`

Built strictly forwards along the paper's logical path; everything in the file is `sorry`-free and
depends only on `[propext, Classical.choice, Quot.sound]`.

* §4.1 complete: the sector `Θ_j` (`Theta`), the `(j,m)`-adapted symbol class (`IsAdapted`), the
  operator `S[F,b]` (`Sop`), the planar slab volume bound (`volume_slab_le`), the bound
  `|Θ_j ∩ (ξ - Θ_j) ∩ {∠(ξ,·) ≤ 2^{-m+5}}| ≤ 2^{2j-m+12}` (`volume_SuppSet_le`), and Plancherel
  on `ℝ⁴` (`lintegral_enorm_sq_fourier_schwartz`).
* §4.2 complete: **Proposition 4.1** (`prop41`), the trivial estimate
  `‖S[F,b]‖_{L²(ℝ²×ℰ)} ≤ c B 2^{j-m/2} (#ℰ)^{1/2} ‖F‖_{L²(ℝ⁴)}`.
* Next: §4.3 Proposition 4.2 (almost orthogonality), then §4.4 Proposition 4.3 (off-diagonal
  decay, which consumes the Calderón--Vaillancourt milestone), then §4.6, §3, §2.

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
