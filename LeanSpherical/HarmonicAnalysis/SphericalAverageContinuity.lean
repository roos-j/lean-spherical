/-
Copyright (c) 2026 LeanSpherical contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanSpherical contributors
-/

import LeanSpherical.HarmonicAnalysis.SurfaceFoundation
import LeanSpherical.HarmonicAnalysis.RadiusMaximalMeasurable

/-!
# Continuity of concrete spherical averages

For continuous inputs, spherical averaging is jointly continuous in the
radius and centre. Compactness of the sphere supplies the needed local
integrability for the parametric integral.
-/

namespace LeanSpherical.HarmonicAnalysis

open MeasureTheory Metric Set

noncomputable section

/-- A continuous input has a jointly continuous concrete spherical average. -/
theorem continuous_sphericalAverage {d : ℕ} (f : Euclidean d → ℂ)
    (hf : Continuous f) :
    Continuous (fun p : ℝ × Euclidean d => sphericalAverage d f p.1 p.2) := by
  unfold sphericalAverage
  have hjoint : Continuous (Function.uncurry
      (fun (p : ℝ × Euclidean d) (ω : sphere (0 : Euclidean d) 1) =>
        f (p.2 + p.1 • (ω : Euclidean d)))) := by
    exact hf.comp
      ((continuous_snd.comp continuous_fst).add
        ((continuous_fst.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd)))
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (μ := unitSurfaceMeasure d) hjoint isCompact_univ)

/-- For a continuous input, each radius restriction of the spherical average
is continuous. -/
theorem continuous_sphericalAverage_radial {d : ℕ} (f : Euclidean d → ℂ)
    (hf : Continuous f) (x : Euclidean d) :
    Continuous (fun r : ℝ => sphericalAverage d f r x) :=
  (continuous_sphericalAverage f hf).comp
    ((continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)))

/-- The compact-radius maximal norm of a continuous spherical average is
measurable. -/
theorem measurable_iSup_ennreal_norm_sphericalAverage
    {d : ℕ} (f : Euclidean d → ℂ) (hf : Continuous f) {a b : ℝ} :
    Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) :=
  measurable_iSup_ennreal_norm_of_continuous
    (d := d) (F := fun p => sphericalAverage d f p.1 p.2) (a := a) (b := b)
    (continuous_sphericalAverage f hf)

/-- The compact-radius maximal square function of a continuous spherical
average is measurable. -/
theorem measurable_iSup_ennreal_norm_sq_sphericalAverage
    {d : ℕ} (f : Euclidean d → ℂ) (hf : Continuous f) {a b : ℝ} :
    Measurable (fun x : Euclidean d =>
      ⨆ r : Icc a b, ENNReal.ofReal (‖sphericalAverage d f r.1 x‖ ^ 2)) :=
  measurable_iSup_ennreal_norm_sq_of_continuous
    (d := d) (F := fun p => sphericalAverage d f p.1 p.2) (a := a) (b := b)
    (continuous_sphericalAverage f hf)

/-- The literal compact-radius maximal norm is subadditive on continuous
inputs.  This is the pointwise decomposition step used with smooth
Schwartz-preserving amplitude truncations. -/
theorem iSup_ennreal_norm_sphericalAverage_add_le
    {d : ℕ} (f g : Euclidean d → ℂ) (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (x : Euclidean d) :
    (⨆ r : Icc a b,
      ENNReal.ofReal ‖sphericalAverage d (f + g) r.1 x‖) ≤
      (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) +
        ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖ := by
  apply iSup_le
  intro r
  have hint (h : Euclidean d → ℂ) (hh : Continuous h) : Integrable
      (fun ω : sphere (0 : Euclidean d) 1 => h (x + r.1 • (ω : Euclidean d)))
      (unitSurfaceMeasure d) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hh.comp
        ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => x).add
          ((continuous_const : Continuous fun _ : sphere (0 : Euclidean d) 1 => r.1).smul
            continuous_subtype_val))
    · exact HasCompactSupport.of_compactSpace _
  have havg : sphericalAverage d (f + g) r.1 x =
      sphericalAverage d f r.1 x + sphericalAverage d g r.1 x := by
    unfold sphericalAverage
    change ∫ ω : sphere (0 : Euclidean d) 1,
      (f (x + r.1 • (ω : Euclidean d)) + g (x + r.1 • (ω : Euclidean d)))
      ∂unitSurfaceMeasure d = _
    rw [MeasureTheory.integral_add (hint f hf) (hint g hg)]
  rw [havg]
  calc
    ENNReal.ofReal ‖sphericalAverage d f r.1 x + sphericalAverage d g r.1 x‖ ≤
        ENNReal.ofReal (‖sphericalAverage d f r.1 x‖ + ‖sphericalAverage d g r.1 x‖) :=
      ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖sphericalAverage d f r.1 x‖ +
          ENNReal.ofReal ‖sphericalAverage d g r.1 x‖ := by
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    _ ≤ (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) +
          ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖ := by
      gcongr
      · exact le_iSup (fun r : Icc a b =>
          ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) r
      · exact le_iSup (fun r : Icc a b =>
          ENNReal.ofReal ‖sphericalAverage d g r.1 x‖) r

/-- A continuous spherical average attains its compact-radius maximum, so
the corresponding extended-real supremum is finite. -/
theorem iSup_ennreal_norm_sphericalAverage_ne_top
    {d : ℕ} (f : Euclidean d → ℂ) (hf : Continuous f) {a b : ℝ}
    (hab : a ≤ b) (x : Euclidean d) :
    (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) ≠ ⊤ := by
  have hnorm : Continuous (fun r : ℝ => ‖sphericalAverage d f r x‖) :=
    (continuous_sphericalAverage_radial f hf x).norm
  obtain ⟨r₀, hr₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hab) hnorm.continuousOn
  have hsup :
      (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) =
        ENNReal.ofReal ‖sphericalAverage d f r₀ x‖ := by
    apply le_antisymm
    · apply iSup_le
      intro r
      exact ENNReal.ofReal_le_ofReal (hmax r.2)
    · exact le_iSup (fun r : Icc a b =>
        ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) ⟨r₀, hr₀⟩
  rw [hsup]
  exact ENNReal.ofReal_ne_top

/-- The ordinary real-valued compact-radius maximal norm is subadditive on
continuous inputs. -/
theorem toReal_iSup_ennreal_norm_sphericalAverage_add_le
    {d : ℕ} (f g : Euclidean d → ℂ) (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) (x : Euclidean d) :
    (⨆ r : Icc a b,
      ENNReal.ofReal ‖sphericalAverage d (f + g) r.1 x‖).toReal ≤
      (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖).toReal +
        (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖).toReal := by
  have hfg : Continuous (f + g) := hf.add hg
  have hleft := iSup_ennreal_norm_sphericalAverage_add_le f g hf hg (a := a) (b := b) x
  have hfgfin := iSup_ennreal_norm_sphericalAverage_ne_top (f + g) hfg hab x
  have hffin := iSup_ennreal_norm_sphericalAverage_ne_top f hf hab x
  have hgfin := iSup_ennreal_norm_sphericalAverage_ne_top g hg hab x
  have hsumfin :
      (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) +
          ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hffin, hgfin⟩
  calc
    (⨆ r : Icc a b,
      ENNReal.ofReal ‖sphericalAverage d (f + g) r.1 x‖).toReal ≤
        ((⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖) +
          ⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖).toReal :=
      (ENNReal.toReal_le_toReal hfgfin hsumfin).2 hleft
    _ = (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d f r.1 x‖).toReal +
          (⨆ r : Icc a b, ENNReal.ofReal ‖sphericalAverage d g r.1 x‖).toReal :=
      ENNReal.toReal_add hffin hgfin

/-- For a continuous input, the concrete spherical maximal function over all
positive radii is measurable.  The supremum is reduced by lower
semicontinuity to a countable dense subset of `Ioi 0`. -/
theorem measurable_sphericalMaximal {d : ℕ} (f : Euclidean d → ℂ)
    (hf : Continuous f) :
    Measurable (sphericalMaximal d f) := by
  let F : ℝ × Euclidean d → ℂ := fun p => sphericalAverage d f p.1 p.2
  have hF : Continuous F := by
    simpa only [F] using continuous_sphericalAverage f hf
  have hG : Measurable (⨆ r : Ioi (0 : ℝ), fun x : Euclidean d =>
      ENNReal.ofReal ‖F (r.1, x)‖) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro r
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_const.prodMk continuous_id)).norm)).measurable
    · intro x
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_subtype_val.prodMk continuous_const)).norm)).lowerSemicontinuous
  have hEq : sphericalMaximal d f =
      ⨆ r : Ioi (0 : ℝ), fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖ := by
    funext x
    exact (iSup_apply
      (f := fun r : Ioi (0 : ℝ) => fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖) (a := x)).symm
  rw [hEq]
  exact hG

/-- The mass-normalized positive-radius maximal function is measurable for
continuous inputs as well. -/
theorem measurable_normalizedSphericalMaximal {d : ℕ}
    (f : Euclidean d → ℂ) (hf : Continuous f) :
    Measurable (normalizedSphericalMaximal d f) := by
  let F : ℝ × Euclidean d → ℂ := fun p => normalizedSphericalAverage d f p.1 p.2
  have hF : Continuous F := by
    unfold F normalizedSphericalAverage
    exact continuous_const.mul (continuous_sphericalAverage f hf)
  have hG : Measurable (⨆ r : Ioi (0 : ℝ), fun x : Euclidean d =>
      ENNReal.ofReal ‖F (r.1, x)‖) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro r
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_const.prodMk continuous_id)).norm)).measurable
    · intro x
      exact (ENNReal.continuous_ofReal.comp
        ((hF.comp (continuous_subtype_val.prodMk continuous_const)).norm)).lowerSemicontinuous
  have hEq : normalizedSphericalMaximal d f =
      ⨆ r : Ioi (0 : ℝ), fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖ := by
    funext x
    exact (iSup_apply
      (f := fun r : Ioi (0 : ℝ) => fun x : Euclidean d =>
        ENNReal.ofReal ‖F (r.1, x)‖) (a := x)).symm
  rw [hEq]
  exact hG

end

end LeanSpherical.HarmonicAnalysis
