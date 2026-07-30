/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.FractalDilations.TTStarCovering
import LeanSpherical.HarmonicAnalysis.SmoothDyadicPhysical
import LeanSpherical.HarmonicAnalysis.SphericalMaximalL2

/-!
# The finite-shell `TT*` calculation at `Q4`

The proof near `Q4` in Anderson--Hughes--Roos--Seeger groups pairs of sampled
radii according to the size of their gap.  At one such shell, its two analytic
inputs are

* a pairwise `L¹ → L∞` estimate, obtained from the oscillatory-kernel bound
  (3.11), and
* a uniform pairwise `L² → L²` estimate.

This file proves the finite-family consequences of those inputs.  It is
deliberately independent of a particular realization of the oscillatory
operators: the existing spherical-maximal development supplies single-radius
Fourier-multiplier bounds, while the genuinely new stationary-phase estimate
for the pairwise kernels belongs in a separate analytic layer.

The factor multiplying a shell can be supplied through
`q4TTStarScaledShell`; in the paper it is `2^{-j (d - 1)}`.
-/

namespace LeanSpherical.HarmonicAnalysis.FractalDilations

open MeasureTheory
open scoped BigOperators FourierTransform

noncomputable section

/-- The finite pairwise-radius shell operator.  The relation `R` selects the
second radius indices coupled to the output index `i`. -/
def q4TTStarShell
    {ι V W : Type*} [AddCommMonoid W]
    (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (P : ι → ι → V → W) (g : ι → V) (i : ι) : W :=
  ∑ j ∈ s.filter (R i), P i j (g j)

/-- A scalar-normalized finite pairwise-radius shell operator. -/
def q4TTStarScaledShell
    {ι V W : Type*} [AddCommMonoid W] [SMul ℝ W]
    (a : ℝ) (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (P : ι → ι → V → W) (g : ι → V) (i : ι) : W :=
  a • q4TTStarShell s R P g i

/-- The finite-shell `L¹ → L∞` estimate.  In the intended application `V`
is an `L¹` space, `W` is a space of bounded output fibres, and `A` is the
supremum norm of the pairwise convolution kernel. -/
theorem norm_q4TTStarShell_le_of_pairwise_bound
    {ι V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (P : ι → ι → V → W) (g : ι → V) {A : ℝ} (hA : 0 ≤ A)
    (hpair : ∀ i j, ‖P i j (g j)‖ ≤ A * ‖g j‖) (i : ι) :
    ‖q4TTStarShell s R P g i‖ ≤ A * ∑ j ∈ s, ‖g j‖ := by
  rw [q4TTStarShell]
  calc
    ‖∑ j ∈ s.filter (R i), P i j (g j)‖ ≤
        ∑ j ∈ s.filter (R i), ‖P i j (g j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ s.filter (R i), A * ‖g j‖ := by
      exact Finset.sum_le_sum fun j hj => hpair i j
    _ = A * ∑ j ∈ s.filter (R i), ‖g j‖ := by
      rw [Finset.mul_sum]
    _ ≤ A * ∑ j ∈ s, ‖g j‖ := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro j hj hjs
      exact norm_nonneg _

/-- The scaled form of the finite-shell `L¹ → L∞` estimate.  This is the
abstract form of (3.9), once a (3.11)-style kernel estimate has supplied the
pairwise constant `A`. -/
theorem norm_q4TTStarScaledShell_le_of_pairwise_bound
    {ι V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ W]
    (a : ℝ) (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (P : ι → ι → V → W) (g : ι → V) {A : ℝ} (hA : 0 ≤ A)
    (hpair : ∀ i j, ‖P i j (g j)‖ ≤ A * ‖g j‖) (i : ι) :
    ‖q4TTStarScaledShell a s R P g i‖ ≤
      |a| * A * ∑ j ∈ s, ‖g j‖ := by
  rw [q4TTStarScaledShell, norm_smul, Real.norm_eq_abs]
  calc
    |a| * ‖q4TTStarShell s R P g i‖ ≤
        |a| * (A * ∑ j ∈ s, ‖g j‖) :=
      mul_le_mul_of_nonneg_left
        (norm_q4TTStarShell_le_of_pairwise_bound s R P g hA hpair i)
        (abs_nonneg _)
    _ = |a| * A * ∑ j ∈ s, ‖g j‖ := by ring

/-- Apply one pairwise convolution kernel to one input fibre.  This is the
physical-space model for a summand of the shell operator. -/
def q4PairwiseKernelApply
    {ι X : Type*} [Sub X] [MeasurableSpace X]
    (μ : Measure X) (K : ι → ι → X → ℂ)
    (i j : ι) (f : X → ℂ) (x : X) : ℂ :=
  ∫ y, K i j (x - y) * f y ∂μ

/-- The finite shell formed from pairwise convolution kernels. -/
def q4KernelTTStarShell
    {ι X : Type*} [Sub X] [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (K : ι → ι → X → ℂ) (g : ι → X → ℂ) (i : ι) (x : X) : ℂ :=
  ∑ j ∈ s.filter (R i), q4PairwiseKernelApply μ K i j (g j) x

/-- A pointwise kernel bound gives the expected `L¹ → L∞` estimate for one
pairwise convolution.  In the application the displayed kernel bound is the
stationary-phase estimate (3.11). -/
theorem norm_q4PairwiseKernelApply_le_of_bound
    {ι X : Type*} [Sub X] [MeasurableSpace X]
    (μ : Measure X) (K : ι → ι → X → ℂ)
    {i j : ι} {f : X → ℂ} {x : X} {A : ℝ}
    (hf : Integrable f μ)
    (hmeas : AEStronglyMeasurable (fun y => K i j (x - y) * f y) μ)
    (hkernel : ∀ z, ‖K i j z‖ ≤ A) :
    ‖q4PairwiseKernelApply μ K i j f x‖ ≤ A * ∫ y, ‖f y‖ ∂μ := by
  have hmajor : Integrable (fun y => A * ‖f y‖) μ := hf.norm.const_mul A
  have hprod : Integrable (fun y => K i j (x - y) * f y) μ := by
    refine hmajor.mono' hmeas (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hkernel (x - y)) (norm_nonneg _)
  unfold q4PairwiseKernelApply
  calc
    ‖∫ y, K i j (x - y) * f y ∂μ‖ ≤
        ∫ y, ‖K i j (x - y) * f y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, A * ‖f y‖ ∂μ := by
      apply integral_mono hprod.norm hmajor
      intro y
      change ‖K i j (x - y) * f y‖ ≤ A * ‖f y‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hkernel (x - y)) (norm_nonneg _)
    _ = A * ∫ y, ‖f y‖ ∂μ := by rw [integral_const_mul]

/-- Summing the preceding pairwise kernel estimate over a shell proves the
physical-space `L¹ → L∞` endpoint used in (3.9).  The radius relation need
not be symmetric for this endpoint. -/
theorem norm_q4KernelTTStarShell_le_of_bound
    {ι X : Type*} [Sub X] [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (K : ι → ι → X → ℂ) (g : ι → X → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hg : ∀ j ∈ s, Integrable (g j) μ)
    (hmeas : ∀ i j x, AEStronglyMeasurable
      (fun y => K i j (x - y) * g j y) μ)
    (hkernel : ∀ i j z, ‖K i j z‖ ≤ A) (i : ι) (x : X) :
    ‖q4KernelTTStarShell μ s R K g i x‖ ≤
      A * ∑ j ∈ s, ∫ y, ‖g j y‖ ∂μ := by
  unfold q4KernelTTStarShell
  calc
    ‖∑ j ∈ s.filter (R i), q4PairwiseKernelApply μ K i j (g j) x‖ ≤
        ∑ j ∈ s.filter (R i), ‖q4PairwiseKernelApply μ K i j (g j) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ s.filter (R i), A * ∫ y, ‖g j y‖ ∂μ := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_q4PairwiseKernelApply_le_of_bound μ K
        (hg j (Finset.mem_filter.mp hj).1) (hmeas i j x) (hkernel i j)
    _ = A * ∑ j ∈ s.filter (R i), ∫ y, ‖g j y‖ ∂μ := by
      rw [Finset.mul_sum]
    _ ≤ A * ∑ j ∈ s, ∫ y, ‖g j y‖ ∂μ := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro j hj hjs
      exact integral_nonneg fun y => norm_nonneg _

/-- The frequency multiplier of one absolutely dyadic spherical piece.  This
is the literal multiplier available in the existing Fourier development; it
is recorded here so that the pairwise composition has a single exact name. -/
def q4DyadicSurfaceMultiplier
    {d : ℕ} (ψ : SchwartzMap (Euclidean d) ℂ) (r : ℝ)
    (ξ : Euclidean d) : ℂ :=
  surfaceFourier d (-r • ξ) * ψ ξ

/-- The corresponding literal Fourier-multiplier operator on Schwartz data. -/
def q4DyadicSurfacePiece
    {d : ℕ} (ψ f : SchwartzMap (Euclidean d) ℂ) (r : ℝ)
    (x : Euclidean d) : ℂ :=
  𝓕⁻ (fun ξ : Euclidean d =>
    q4DyadicSurfaceMultiplier ψ r ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x

/-- The exact frequency multiplier obtained by multiplying one dyadic
spherical piece with the conjugate multiplier at a second radius.  It is the
Fourier-side realization of the formal `A_{j,r} A_{j,r'}^*` composition.
The conversion of this formula into a physical kernel is the missing
stationary-phase layer. -/
def q4DyadicPairMultiplier
    {d : ℕ} (ψ : SchwartzMap (Euclidean d) ℂ) (r r' : ℝ)
    (ξ : Euclidean d) : ℂ :=
  q4DyadicSurfaceMultiplier ψ r ξ *
    starRingEnd ℂ (q4DyadicSurfaceMultiplier ψ r' ξ)

/-- The literal pairwise Fourier-multiplier operator. -/
def q4DyadicPairPiece
    {d : ℕ} (ψ f : SchwartzMap (Euclidean d) ℂ) (r r' : ℝ)
    (x : Euclidean d) : ℂ :=
  𝓕⁻ (fun ξ : Euclidean d =>
    q4DyadicPairMultiplier ψ r r' ξ * 𝓕 (f : Euclidean d → ℂ) ξ) x

/-- The formal convolution kernel of the pairwise dyadic multiplier. -/
def q4DyadicPairKernel
    {d : ℕ} (ψ : SchwartzMap (Euclidean d) ℂ) (r r' : ℝ)
    (x : Euclidean d) : ℂ :=
  𝓕⁻ (q4DyadicPairMultiplier ψ r r') x

/-- Norms of the pair multiplier factor into the two individual dyadic
surface multipliers.  This is the elementary frequency-side input to its
uniform `L²` estimate. -/
theorem norm_q4DyadicPairMultiplier
    {d : ℕ} (ψ : SchwartzMap (Euclidean d) ℂ) (r r' : ℝ)
    (ξ : Euclidean d) :
    ‖q4DyadicPairMultiplier ψ r r' ξ‖ =
    ‖q4DyadicSurfaceMultiplier ψ r ξ‖ *
        ‖q4DyadicSurfaceMultiplier ψ r' ξ‖ := by
  rw [q4DyadicPairMultiplier, norm_mul, starRingEnd_apply, norm_star]

/-- Pointwise bounds for the two individual multipliers imply the product
bound required by Plancherel for a pairwise `L²` estimate. -/
theorem norm_q4DyadicPairMultiplier_le_of_bounds
    {d : ℕ} (ψ : SchwartzMap (Euclidean d) ℂ) (r r' : ℝ)
    {B B' : ℝ} (hB : 0 ≤ B)
    (hr : ∀ ξ : Euclidean d, ‖q4DyadicSurfaceMultiplier ψ r ξ‖ ≤ B)
    (hr' : ∀ ξ : Euclidean d, ‖q4DyadicSurfaceMultiplier ψ r' ξ‖ ≤ B')
    (ξ : Euclidean d) :
    ‖q4DyadicPairMultiplier ψ r r' ξ‖ ≤ B * B' := by
  rw [norm_q4DyadicPairMultiplier]
  exact mul_le_mul (hr ξ) (hr' ξ) (norm_nonneg _) hB

/-- The existing sharp surface-transform decay gives the uniform frequency
bound for the literal pairwise spherical multiplier.  Thus the pairwise
`L²` *symbol* estimate is already available; what is not available is the
physical-space radius-gap decay of its convolution kernel. -/
theorem norm_q4DyadicPairMultiplier_succ_smooth_dyadic_bandpass_le_of_sharp
    {d : ℕ} (C0 : ℝ) (hC0 : 0 < C0)
    (hdecay : ∀ ξ : Euclidean (d + 1), 1 ≤ ‖ξ‖ →
      ‖surfaceFourier (d + 1) ξ‖ ≤ C0 / ‖ξ‖ ^ ((d : ℝ) / 2))
    {φ ψ : SchwartzMap (Euclidean (d + 1)) ℂ}
    (hφone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hφzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    (hφnorm : ∀ ξ, ‖φ ξ‖ ≤ 1) (j : ℕ)
    (hψ : ∀ ξ : Euclidean (d + 1),
      ψ ξ = φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) -
        φ (((2 : ℝ) ^ j)⁻¹ • ξ))
    {r r' : ℝ} (hr : r ∈ Set.Icc (1 : ℝ) 2)
    (hr' : r' ∈ Set.Icc (1 : ℝ) 2) (ξ : Euclidean (d + 1)) :
    ‖q4DyadicPairMultiplier ψ r r' ξ‖ ≤
      ((2 * C0) /
        (_root_.LeanSpherical.HarmonicAnalysis.dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 := by
  let B : ℝ := (2 * C0) /
    (_root_.LeanSpherical.HarmonicAnalysis.dyadicScale j) ^ ((d : ℝ) / 2)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (mul_nonneg (by norm_num) hC0.le)
      (Real.rpow_nonneg (_root_.LeanSpherical.HarmonicAnalysis.dyadicScale_pos j).le _)
  have hsingle (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
      (η : Euclidean (d + 1)) :
      ‖q4DyadicSurfaceMultiplier ψ t η‖ ≤ B := by
    unfold q4DyadicSurfaceMultiplier
    rw [hψ η]
    have hneg : surfaceFourier (d + 1) (-t • η) =
        surfaceFourier (d + 1) (t • η) := by
      rw [show (-t : ℝ) • η = -(t • η) by rw [neg_smul],
        surfaceFourier_neg]
    rw [hneg]
    simpa only [B] using
      norm_surfaceFourier_succ_smul_mul_smooth_dyadic_bandpass_le_of_sharp
          C0 hC0 hdecay hφone hφzero hφnorm j t ht η
  calc
    ‖q4DyadicPairMultiplier ψ r r' ξ‖ ≤ B * B :=
      norm_q4DyadicPairMultiplier_le_of_bounds ψ r r' hB
        (fun η => hsingle r hr η) (fun η => hsingle r' hr' η) ξ
    _ = ((2 * C0) /
        (_root_.LeanSpherical.HarmonicAnalysis.dyadicScale j) ^ ((d : ℝ) / 2)) ^ 2 := by
      dsimp [B]
      ring

/-- The finite-shell `L² → L²` calculation.  A symmetric shell of degree at
most `K` has norm at most `K` times the uniform norm `B` of its pairwise
operators.  This is precisely the Cauchy--Schwarz/counting step in (3.10). -/
theorem sum_sq_norm_q4TTStarShell_le_of_pairwise_bound
    {ι V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (hR : Std.Symm R) (K : ℕ)
    (hdegree : ∀ i ∈ s, (s.filter (R i)).card ≤ K)
    (P : ι → ι → V → W) (g : ι → V) {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ i j, ‖P i j (g j)‖ ≤ B * ‖g j‖) :
    (∑ i ∈ s, ‖q4TTStarShell s R P g i‖ ^ 2) ≤
      (B * (K : ℝ)) ^ 2 * ∑ i ∈ s, ‖g i‖ ^ 2 := by
  have hpoint (i : ι) (hi : i ∈ s) :
      ‖q4TTStarShell s R P g i‖ ^ 2 ≤
        (∑ j ∈ s.filter (R i), B * ‖g j‖) ^ 2 := by
    rw [q4TTStarShell]
    apply (sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg fun j hj => mul_nonneg hB (norm_nonneg _))).mpr
    calc
      ‖∑ j ∈ s.filter (R i), P i j (g j)‖ ≤
          ∑ j ∈ s.filter (R i), ‖P i j (g j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ s.filter (R i), B * ‖g j‖ := by
        exact Finset.sum_le_sum fun j hj => hpair i j
  calc
    (∑ i ∈ s, ‖q4TTStarShell s R P g i‖ ^ 2) ≤
        ∑ i ∈ s, (∑ j ∈ s.filter (R i), B * ‖g j‖) ^ 2 := by
      exact Finset.sum_le_sum fun i hi => hpoint i hi
    _ ≤ (K : ℝ) ^ 2 * ∑ i ∈ s, (B * ‖g i‖) ^ 2 :=
      sum_sq_neighbor_sum_le s R hR K hdegree (fun i => B * ‖g i‖)
    _ = (B * (K : ℝ)) ^ 2 * ∑ i ∈ s, ‖g i‖ ^ 2 := by
      rw [show (∑ i ∈ s, (B * ‖g i‖) ^ 2) =
          B ^ 2 * ∑ i ∈ s, ‖g i‖ ^ 2 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
      ring

/-- The scaled finite-shell `L² → L²` calculation.  Setting
`a = 2^{-j (d - 1)}` gives the normalization of the operators `S_{n,j}` in
the paper. -/
theorem sum_sq_norm_q4TTStarScaledShell_le_of_pairwise_bound
    {ι V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ W]
    (a : ℝ) (s : Finset ι) (R : ι → ι → Prop) [DecidableRel R]
    (hR : Std.Symm R) (K : ℕ)
    (hdegree : ∀ i ∈ s, (s.filter (R i)).card ≤ K)
    (P : ι → ι → V → W) (g : ι → V) {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ i j, ‖P i j (g j)‖ ≤ B * ‖g j‖) :
    (∑ i ∈ s, ‖q4TTStarScaledShell a s R P g i‖ ^ 2) ≤
      (|a| * B * (K : ℝ)) ^ 2 * ∑ i ∈ s, ‖g i‖ ^ 2 := by
  have hbase := sum_sq_norm_q4TTStarShell_le_of_pairwise_bound
    s R hR K hdegree P g hB hpair
  calc
    (∑ i ∈ s, ‖q4TTStarScaledShell a s R P g i‖ ^ 2) =
        |a| ^ 2 * ∑ i ∈ s, ‖q4TTStarShell s R P g i‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [q4TTStarScaledShell, norm_smul, Real.norm_eq_abs, mul_pow]
    _ ≤ |a| ^ 2 * ((B * (K : ℝ)) ^ 2 * ∑ i ∈ s, ‖g i‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
    _ = (|a| * B * (K : ℝ)) ^ 2 * ∑ i ∈ s, ‖g i‖ ^ 2 := by ring

/-- Radius-gap specialization of the `L²` shell calculation.  The local
covering theorem in `TTStarCovering` supplies its degree hypothesis; the
remaining pairwise hypothesis is the uniform `L²` bound for the composed
oscillatory operators. -/
theorem sum_sq_norm_q4RadiusGapShell_le_of_pairwise_bound
    {ι V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    (radii : ι → ℝ) (u L : ℝ) (s : Finset ι)
    [DecidableRel (fun i j => radiusGapShellNeighbors u L (radii i) (radii j))]
    (K : ℕ)
    (hdegree : ∀ i ∈ s,
      (s.filter (fun j => radiusGapShellNeighbors u L (radii i) (radii j))).card ≤ K)
    (P : ι → ι → V → W) (g : ι → V) {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ i j, ‖P i j (g j)‖ ≤ B * ‖g j‖) :
    (∑ i ∈ s, ‖q4TTStarShell s
      (fun i j => radiusGapShellNeighbors u L (radii i) (radii j)) P g i‖ ^ 2) ≤
      (B * (K : ℝ)) ^ 2 * ∑ i ∈ s, ‖g i‖ ^ 2 := by
  apply sum_sq_norm_q4TTStarShell_le_of_pairwise_bound
    s (fun i j => radiusGapShellNeighbors u L (radii i) (radii j))
  · constructor
    intro i j hij
    exact (radiusGapShellNeighbors_symm u L).symm _ _ hij
  · exact hdegree
  · exact hB
  · exact hpair

end

end LeanSpherical.HarmonicAnalysis.FractalDilations
