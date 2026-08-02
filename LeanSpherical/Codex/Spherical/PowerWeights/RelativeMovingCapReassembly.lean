import LeanSpherical.Codex.Spherical.PowerWeights.RelativeMovingCapEndpoint
import LeanSpherical.Codex.Spherical.PowerWeights.LocalizedUpper

/-!
# Finite-radius cap reassembly for relative moving dyadic pieces

This file sums the fixed-radius cap endpoint over the finite radius sets which
arise after discretizing the moving dilation parameter.  The main estimate is
kept in the literal Fourier-multiplier form used by the local weighted
argument.
-/

noncomputable section

open MeasureTheory FourierTransform Set Metric Filter Topology
open scoped BigOperators Convolution ENNReal FourierTransform

namespace LeanSpherical.HarmonicAnalysis

private theorem measurable_literal_moving_band_output
    (n j : Nat) (phi : SchwartzMap (Euclidean (n + 1)) ℂ) (f : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0)
    {r : ℝ} (hr : 0 < r) :
    Measurable (fun x : Euclidean (n + 1) =>
      ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean (n + 1) =>
        surfaceFourier (n + 1) (-r • ξ) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
              𝓕 (f : Euclidean (n + 1) → ℂ) ξ) x‖) := by
  obtain ⟨psi, hpsi, hpsi_compact, _⟩ :=
    exists_compactlySupported_schwartzMap_smooth_dyadic_bandpass phi hphi_one hphi_zero j
  obtain ⟨chi, hchi⟩ :=
    exists_schwartz_compactSupport_mul_surfaceFourier psi hpsi_compact 1
  have hchi' (ξ : Euclidean (n + 1)) :
      chi ξ = psi ξ * surfaceFourier (n + 1) (-ξ) := by
    simpa using hchi ξ
  have hmult :
      (fun ξ : Euclidean (n + 1) =>
        surfaceFourier (n + 1) (-r • ξ) *
          (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
            phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
              𝓕 (f : Euclidean (n + 1) → ℂ) ξ) =
      fun ξ : Euclidean (n + 1) =>
        chi (r • ξ) *
          𝓕 (f : Euclidean (n + 1) → ℂ) ξ := by
    funext ξ
    rw [hchi' (r • ξ), hpsi]
    rw [show (-r : ℝ) • ξ = -(r • ξ) by rw [neg_smul]]
    ring
  have hcont : Continuous (fun x : Euclidean (n + 1) =>
      𝓕⁻ (fun ξ : Euclidean (n + 1) =>
        chi (r • ξ) *
          𝓕 (f : Euclidean (n + 1) → ℂ) ξ) x) := by
    simpa [inv_inv] using
      (continuous_fourierInv_scaled_schwartz_multiplier chi f (inv_pos.mpr hr))
  rw [hmult]
  exact (ENNReal.continuous_ofReal.comp hcont.norm).measurable

/-- The explicit finite radial-tail coefficient from the local moving-band cap
estimate.  Keeping this one coefficient named makes the finite-radius sum
readable while preserving the exact cap factor needed later. -/
def relativeMovingBandCapTail (n j : Nat) (C r s : ℝ) : ENNReal :=
  (∑ m ∈ Finset.range (j - 2),
    ENNReal.ofReal (C * (2 : ℝ) ^ j) *
      (ENNReal.ofReal (((2 : ℝ)⁻¹) ^ (n + 1 + 3))) ^ m *
        volume (ball (0 : Euclidean n) s) *
          ENNReal.ofReal (6 * (r * (2 : ℝ) ^ (m + 1) / (2 : ℝ) ^ j))) +
    ENNReal.ofReal (C * (2 : ℝ) ^ j) *
      (ENNReal.ofReal (((2 : ℝ)⁻¹) ^ (n + 1 + 3))) ^ (j - 2) *
        volume (ball (0 : Euclidean (n + 1)) s)

/-- The cap-tail coefficient with its transverse `s ^ n` volume made
explicit.  The first term is the sharp local contribution; the second is the
summable far tail. -/
theorem relativeMovingBandCapTail_eq_scaled
    (n j : Nat) (C r : ℝ) {s : ℝ} (hs : 0 < s) :
    relativeMovingBandCapTail n j C r s =
      (∑ m ∈ Finset.range (j - 2),
        ENNReal.ofReal (C * (2 : ℝ) ^ j) *
          (ENNReal.ofReal (((2 : ℝ)⁻¹) ^ (n + 1 + 3))) ^ m *
            ((ENNReal.ofReal s) ^ n * volume (ball (0 : Euclidean n) 1)) *
              ENNReal.ofReal (6 * (r * (2 : ℝ) ^ (m + 1) / (2 : ℝ) ^ j))) +
        ENNReal.ofReal (C * (2 : ℝ) ^ j) *
          (ENNReal.ofReal (((2 : ℝ)⁻¹) ^ (n + 1 + 3))) ^ (j - 2) *
            ((ENNReal.ofReal s) ^ (n + 1) *
              volume (ball (0 : Euclidean (n + 1)) 1)) := by
  unfold relativeMovingBandCapTail
  rw [Measure.addHaar_ball_of_pos volume (0 : Euclidean n) hs,
    Measure.addHaar_ball_of_pos volume (0 : Euclidean (n + 1)) hs]
  simp only [finrank_euclideanSpace_fin]
  rw [ENNReal.ofReal_pow hs.le, ENNReal.ofReal_pow hs.le]

/-- A finite collection of moving radii inherits the cap-improved fixed-radius
endpoint term by term.  This is the literal reassembly used after a finite
radius discretization: no maximal-operator wrapper is introduced. -/
theorem exists_finite_radius_literal_moving_band_cap_lintegral_one_le
    (n : Nat) (phi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Nat) (f : SchwartzMap (Euclidean (n + 1)) ℂ)
      (R : Finset ℝ) {s : ℝ}, 3 ≤ j → 0 < s →
      (∀ r ∈ R, r ∈ Icc (1 : ℝ) 2) → (∀ r ∈ R, 4 * s ≤ r) →
      (∀ y : Euclidean (n + 1), ¬ s < ‖y‖ → f y = 0) →
      (∫⁻ x in ball (0 : Euclidean (n + 1)) s,
        ∑ r ∈ R, ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean (n + 1) =>
          surfaceFourier (n + 1) (-r • ξ) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
                𝓕 (f : Euclidean (n + 1) → ℂ) ξ) x‖) ≤
        (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
  obtain ⟨C, hC, hcap⟩ :=
    exists_fixed_radius_literal_moving_band_cap_lintegral_one_le n phi
  refine ⟨C, hC, ?_⟩
  intro j f R s hj hs hR hsmall hfsupp
  let H : ℝ → Euclidean (n + 1) → ENNReal := fun r x =>
    ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean (n + 1) =>
      surfaceFourier (n + 1) (-r • ξ) *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
          phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
            𝓕 (f : Euclidean (n + 1) → ℂ) ξ) x‖
  let M : ℝ → ENNReal := fun r => relativeMovingBandCapTail n j C r s
  have hHmeas (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) : Measurable (H r) := by
    dsimp only [H]
    exact measurable_literal_moving_band_output n j phi f hphi_one hphi_zero
      (lt_of_lt_of_le zero_lt_one hr.1)
  have hcapR (r : ℝ) (hrR : r ∈ R) :
      (∫⁻ x in ball (0 : Euclidean (n + 1)) s, H r x) ≤
        M r * ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
    dsimp only [H, M, relativeMovingBandCapTail]
    exact hcap j f hj (hR r hrR) hs (hsmall r hrR) hfsupp
  have hsum :
      (∫⁻ x in ball (0 : Euclidean (n + 1)) s, ∑ r ∈ R, H r x) ≤
        (∑ r ∈ R, M r) * ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
    calc
      (∫⁻ x in ball (0 : Euclidean (n + 1)) s, ∑ r ∈ R, H r x) =
          ∑ r ∈ R, ∫⁻ x in ball (0 : Euclidean (n + 1)) s, H r x := by
        exact lintegral_finsetSum R (fun r hrR => hHmeas r (hR r hrR))
      _ ≤ ∑ r ∈ R, M r * ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
        apply Finset.sum_le_sum
        intro r hrR
        exact hcapR r hrR
      _ = (∑ r ∈ R, M r) * ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
        rw [Finset.sum_mul]
  simpa only [H, M] using hsum

/-- Finite-radius local endpoint in the exact `LocalizedUpper` convention.
The restricted moving band over a finite radius set is dominated by its
literal finite sum, so the cap gain is available directly to the local
weighted cutoff argument. -/
theorem exists_restrictedRelativeBandpass_finset_cap_lintegral_one_le
    (n : Nat) (phi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Nat) (f : SchwartzMap (Euclidean (n + 1)) ℂ)
      (R : Finset ℝ) {s : ℝ}, 3 ≤ j → 0 < s →
      (∀ r ∈ R, r ∈ Icc (1 : ℝ) 2) → (∀ r ∈ R, 4 * s ≤ r) →
      (∀ y : Euclidean (n + 1), ¬ s < ‖y‖ → f y = 0) →
      (∫⁻ x in ball (0 : Euclidean (n + 1)) s,
        restrictedRelativeBandpassSphericalMaximal (n + 1) (R : Set ℝ) phi j f x) ≤
        (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
  obtain ⟨C, hC, hsum⟩ :=
    exists_finite_radius_literal_moving_band_cap_lintegral_one_le n phi hphi_one hphi_zero
  refine ⟨C, hC, ?_⟩
  intro j f R s hj hs hR hsmall hfsupp
  let H : ℝ → Euclidean (n + 1) → ENNReal := fun r x =>
    ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean (n + 1) =>
      surfaceFourier (n + 1) (-r • ξ) *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
          phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
            𝓕 (f : Euclidean (n + 1) → ℂ) ξ) x‖
  have hpoint (x : Euclidean (n + 1)) :
      restrictedRelativeBandpassSphericalMaximal (n + 1) (R : Set ℝ) phi j f x ≤
        ∑ r ∈ R, H r x := by
    unfold restrictedRelativeBandpassSphericalMaximal
    apply iSup_le
    intro r
    refine Finset.single_le_sum (s := R) (f := fun q => H q x) (fun _ _ => bot_le) ?_
    simpa only [Finset.mem_coe] using r.2.1
  calc
    (∫⁻ x in ball (0 : Euclidean (n + 1)) s,
        restrictedRelativeBandpassSphericalMaximal (n + 1) (R : Set ℝ) phi j f x) ≤
        ∫⁻ x in ball (0 : Euclidean (n + 1)) s, ∑ r ∈ R, H r x :=
      lintegral_mono hpoint
    _ ≤ (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
        ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
      simpa only [H] using hsum j f R hj hs hR hsmall hfsupp

/-- Dyadic core form of the `LocalizedUpper`-compatible finite-radius cap
endpoint.  The transverse factor in
`relativeMovingBandCapTail` is exactly the `2⁻ᵏⁿ` gain after applying
`relativeMovingBandCapTail_eq_scaled`. -/
theorem exists_restrictedRelativeBandpass_finset_dyadic_core_lintegral_one_le
    (n : Nat) (phi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Nat) (f : SchwartzMap (Euclidean (n + 1)) ℂ)
      (R : Finset ℝ) (k : Nat), 3 ≤ j → 2 ≤ k →
      (∀ r ∈ R, r ∈ Icc (1 : ℝ) 2) →
      (∀ y : Euclidean (n + 1), ¬ ((2 : ℝ) ^ k)⁻¹ < ‖y‖ → f y = 0) →
      (∫⁻ x in ball (0 : Euclidean (n + 1)) ((2 : ℝ) ^ k)⁻¹,
        restrictedRelativeBandpassSphericalMaximal (n + 1) (R : Set ℝ) phi j f x) ≤
        (∑ r ∈ R, relativeMovingBandCapTail n j C r ((2 : ℝ) ^ k)⁻¹) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_restrictedRelativeBandpass_finset_cap_lintegral_one_le n phi hphi_one hphi_zero
  refine ⟨C, hC, ?_⟩
  intro j f R k hj hk hR hfsupp
  have hpowpos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) _
  have hs : 0 < ((2 : ℝ) ^ k)⁻¹ := inv_pos.mpr hpowpos
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ k := by
        exact pow_le_pow_right₀ (by norm_num) hk
  exact hfinite j f R hj hs hR (fun r hrR => by
    calc
      4 * ((2 : ℝ) ^ k)⁻¹ = 4 / (2 : ℝ) ^ k := by rw [div_eq_mul_inv]
      _ ≤ 1 := (div_le_iff₀ hpowpos).2 (by simpa using hpow)
      _ ≤ r := (hR r hrR).1) hfsupp

/-- Dyadic small-ball form of the finite-radius cap reassembly.  Its near
coefficient is `volume (ball 0 ((2^k)⁻¹))` in transverse dimension `n`, i.e.
the `2⁻ᵏⁿ` cap gain needed for the core input in the spatial-shell argument. -/
theorem exists_finite_radius_literal_moving_band_dyadic_core_lintegral_one_le
    (n : Nat) (phi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Nat) (f : SchwartzMap (Euclidean (n + 1)) ℂ)
      (R : Finset ℝ) (k : Nat), 3 ≤ j → 2 ≤ k →
      (∀ r ∈ R, r ∈ Icc (1 : ℝ) 2) →
      (∀ y : Euclidean (n + 1), ¬ ((2 : ℝ) ^ k)⁻¹ < ‖y‖ → f y = 0) →
      (∫⁻ x in ball (0 : Euclidean (n + 1)) ((2 : ℝ) ^ k)⁻¹,
        ∑ r ∈ R, ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean (n + 1) =>
          surfaceFourier (n + 1) (-r • ξ) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
                𝓕 (f : Euclidean (n + 1) → ℂ) ξ) x‖) ≤
        (∑ r ∈ R, relativeMovingBandCapTail n j C r ((2 : ℝ) ^ k)⁻¹) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_finite_radius_literal_moving_band_cap_lintegral_one_le n phi hphi_one hphi_zero
  refine ⟨C, hC, ?_⟩
  intro j f R k hj hk hR hfsupp
  have hpowpos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) _
  have hs : 0 < ((2 : ℝ) ^ k)⁻¹ := inv_pos.mpr hpowpos
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ k := by
        exact pow_le_pow_right₀ (by norm_num) hk
  exact hfinite j f R hj hs hR (fun r hrR => by
    calc
      4 * ((2 : ℝ) ^ k)⁻¹ = 4 / (2 : ℝ) ^ k := by rw [div_eq_mul_inv]
      _ ≤ 1 := (div_le_iff₀ hpowpos).2 (by simpa using hpow)
      _ ≤ r := (hR r hrR).1) hfsupp

/-- The same finite-radius cap bound on one literal spatial annulus.  The
annulus is contained in the small ball, so this is the form used when the
core contribution is reassembled shell by shell. -/
theorem exists_finite_radius_literal_moving_band_annular_cap_lintegral_one_le
    (n : Nat) (phi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Nat) (f : SchwartzMap (Euclidean (n + 1)) ℂ)
      (R : Finset ℝ) {s : ℝ}, 3 ≤ j → 0 < s →
      (∀ r ∈ R, r ∈ Icc (1 : ℝ) 2) → (∀ r ∈ R, 4 * s ≤ r) →
      (∀ y : Euclidean (n + 1), ¬ s < ‖y‖ → f y = 0) →
      (∫⁻ x in ball (0 : Euclidean (n + 1)) s \
          closedBall (0 : Euclidean (n + 1)) (s / 2),
        ∑ r ∈ R, ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean (n + 1) =>
          surfaceFourier (n + 1) (-r • ξ) *
            (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
              phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
                𝓕 (f : Euclidean (n + 1) → ℂ) ξ) x‖) ≤
        (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_finite_radius_literal_moving_band_cap_lintegral_one_le n phi hphi_one hphi_zero
  refine ⟨C, hC, ?_⟩
  intro j f R s hj hs hR hsmall hfsupp
  let G : Euclidean (n + 1) → ENNReal := fun x =>
    ∑ r ∈ R, ENNReal.ofReal ‖𝓕⁻ (fun ξ : Euclidean (n + 1) =>
      surfaceFourier (n + 1) (-r • ξ) *
        (phi (((2 : ℝ) ^ (j + 1))⁻¹ • (r • ξ)) -
          phi (((2 : ℝ) ^ j)⁻¹ • (r • ξ))) *
            𝓕 (f : Euclidean (n + 1) → ℂ) ξ) x‖
  have hball :
      (∫⁻ x in ball (0 : Euclidean (n + 1)) s, G x) ≤
        (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
    simpa only [G] using hfinite j f R hj hs hR hsmall hfsupp
  let A : Set (Euclidean (n + 1)) :=
    ball (0 : Euclidean (n + 1)) s \
      closedBall (0 : Euclidean (n + 1)) (s / 2)
  have hA : MeasurableSet A := by
    exact measurableSet_ball.diff measurableSet_closedBall
  have hsubset : A ⊆ ball (0 : Euclidean (n + 1)) s := fun _ hx => hx.1
  have hannular :
      (∫⁻ x in A, G x) ≤
        (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
    calc
      (∫⁻ x in A, G x) = ∫⁻ x : Euclidean (n + 1), A.indicator G x :=
        (lintegral_indicator hA G).symm
      _ ≤ ∫⁻ x : Euclidean (n + 1),
          (ball (0 : Euclidean (n + 1)) s).indicator G x :=
        lintegral_mono (indicator_le_indicator_of_subset hsubset (fun _ => bot_le))
      _ = ∫⁻ x in ball (0 : Euclidean (n + 1)) s, G x :=
        lintegral_indicator measurableSet_ball G
      _ ≤ (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := hball
  simpa only [A, G] using hannular

/-- Spatial-annular restriction of the exact finite-radius moving-band
endpoint.  This is the direct local shell estimate: the output is the literal
`restrictedRelativeBandpassSphericalMaximal` used by `LocalizedUpper`. -/
theorem exists_restrictedRelativeBandpass_finset_annular_cap_lintegral_one_le
    (n : Nat) (phi : SchwartzMap (Euclidean (n + 1)) ℂ)
    (hphi_one : ∀ ξ, ‖ξ‖ ≤ 1 → phi ξ = 1)
    (hphi_zero : ∀ ξ, 2 ≤ ‖ξ‖ → phi ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Nat) (f : SchwartzMap (Euclidean (n + 1)) ℂ)
      (R : Finset ℝ) {s : ℝ}, 3 ≤ j → 0 < s →
      (∀ r ∈ R, r ∈ Icc (1 : ℝ) 2) → (∀ r ∈ R, 4 * s ≤ r) →
      (∀ y : Euclidean (n + 1), ¬ s < ‖y‖ → f y = 0) →
      (∫⁻ x in ball (0 : Euclidean (n + 1)) s \
          closedBall (0 : Euclidean (n + 1)) (s / 2),
        restrictedRelativeBandpassSphericalMaximal (n + 1) (R : Set ℝ) phi j f x) ≤
        (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
  obtain ⟨C, hC, hball⟩ :=
    exists_restrictedRelativeBandpass_finset_cap_lintegral_one_le n phi hphi_one hphi_zero
  refine ⟨C, hC, ?_⟩
  intro j f R s hj hs hR hsmall hfsupp
  let A : Set (Euclidean (n + 1)) :=
    ball (0 : Euclidean (n + 1)) s \
      closedBall (0 : Euclidean (n + 1)) (s / 2)
  let G : Euclidean (n + 1) → ENNReal := fun x =>
    restrictedRelativeBandpassSphericalMaximal (n + 1) (R : Set ℝ) phi j f x
  have hA : MeasurableSet A := by
    exact measurableSet_ball.diff measurableSet_closedBall
  have hsubset : A ⊆ ball (0 : Euclidean (n + 1)) s := fun _ hx => hx.1
  have hball' :
      (∫⁻ x in ball (0 : Euclidean (n + 1)) s, G x) ≤
        (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
    simpa only [G] using hball j f R hj hs hR hsmall hfsupp
  have hannular :
      (∫⁻ x in A, G x) ≤
        (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := by
    calc
      (∫⁻ x in A, G x) = ∫⁻ x : Euclidean (n + 1), A.indicator G x :=
        (lintegral_indicator hA G).symm
      _ ≤ ∫⁻ x : Euclidean (n + 1),
          (ball (0 : Euclidean (n + 1)) s).indicator G x :=
        lintegral_mono (indicator_le_indicator_of_subset hsubset (fun _ => bot_le))
      _ = ∫⁻ x in ball (0 : Euclidean (n + 1)) s, G x :=
        lintegral_indicator measurableSet_ball G
      _ ≤ (∑ r ∈ R, relativeMovingBandCapTail n j C r s) *
          ∫⁻ y : Euclidean (n + 1), ENNReal.ofReal ‖f y‖ := hball'
  simpa only [A, G] using hannular

end LeanSpherical.HarmonicAnalysis
