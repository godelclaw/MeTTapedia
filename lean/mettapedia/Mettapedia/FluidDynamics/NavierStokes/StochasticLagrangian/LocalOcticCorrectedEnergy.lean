import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalOcticMeanBalance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthEnergy

/-!
# The actual eighth-moment energy with an octic correlation correction

The complete correlation evolution is combined with the vorticity identity.
Only the mixed curvature is absorbed. The remaining signed expression contains
stretching, relative transport, and pure curvature; no bound on it is assumed
or proved here. All time statements are on the supplied local interval.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrectedEnergy

open MeasureTheory Set Mettapedia.Analysis
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity LocalLowDiffusionBudget LocalOcticDiffusion LocalOcticMeanBalance
open UnitTorusProductTransport
open LocalVorticityEighthMoment (meanEnergy weightedPalinstrophy radialDissipation stretching)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def energy (N : ℕ) (ε : ℝ) (u : FourierVelocity) : ℝ :=
  meanEnergy u / 8 + ε * LocalOcticCorrelation.correlation N u

/-- The unpaid signed source, after the mixed curvature has been separated. -/
def residual (N : ℕ) (nu ε : ℝ) (u : FourierVelocity) : ℝ :=
  stretching u + ε * (meanRate N 0 u - nu * pureContribution N u)

theorem energy_bounds (N : ℕ) (ε : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hε : |ε| ≤ 1 / 144) :
    meanEnergy u / 16 ≤ energy N ε u ∧ energy N ε u ≤ 3 * meanEnergy u / 16 := by
  have hE := LocalVorticityEighthMoment.meanEnergy_nonneg u
  have hb : |ε * LocalOcticCorrelation.correlation N u| ≤ meanEnergy u / 16 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 144) * (9 * meanEnergy u) :=
        mul_le_mul hε (LocalOcticCorrelation.abs_correlation_le N u hu) (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hl := neg_abs_le (ε * LocalOcticCorrelation.correlation N u)
  have hr := le_abs_self (ε * LocalOcticCorrelation.correlation N u)
  unfold energy
  constructor <;> linarith

theorem residual_eq_signedRate_add_mixed (N : ℕ) (nu ε : ℝ) (u : FourierVelocity) :
    residual N nu ε u = stretching u + ε * signedRate N nu u +
      nu * ε * LocalOcticCorrelation.mixedGradientContribution N u := by
  unfold residual signedRate
  ring

theorem abs_mixed_correction_le (N : ℕ) (nu ε : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hnu : 0 ≤ nu) (hε : |ε| ≤ 1 / 576) :
    |nu * ε * LocalOcticCorrelation.mixedGradientContribution N u| ≤
      nu / 2 * weightedPalinstrophy u := by
  have h := correction_mixed_absorption N u hu nu ε hnu hε
  rw [diffusionContribution_eq N u hu] at h
  have he : nu * ε * (-(pureContribution N u + LocalOcticCorrelation.mixedGradientContribution N u) +
      pureContribution N u) = -(nu * ε * LocalOcticCorrelation.mixedGradientContribution N u) := by ring
  rwa [he, abs_neg] at h

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

include hSum hu in
theorem continuousOn_mixedContribution (N : ℕ) :
    ContinuousOn (fun t ↦ LocalOcticCorrelation.mixedGradientContribution N (s.coefficients t)) (Icc 0 T) := by
  let f (t : ℝ) (x : T6) := mixedDensity (PeriodicRadialRiesz.tensor N) (s.coefficients t)
    (leftPoint x) (rightPoint x)
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))
  have hl : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2)) :=
    continuous_fst.prodMk (continuous_leftPoint.comp continuous_snd)
  have hr : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2)) :=
    continuous_fst.prodMk (continuous_rightPoint.comp continuous_snd)
  have hwl : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ fullVorticity (s.coefficients z.1) (leftPoint z.2)) :=
    hw.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2)) hl
  have hwr : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ fullVorticity (s.coefficients z.1) (rightPoint z.2)) :=
    hw.comp (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2)) hr
  have hgl (j : Fin 3) : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦
      LocalSpatialVorticityJets.fullCurlGradient (s.coefficients z.1) j (leftPoint z.2)) :=
    (LocalVorticityEighthMoment.continuous_fullCurlGradient_spaceTime s g hSum hu j).comp
      (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, leftPoint z.2)) hl
  have hgr (j : Fin 3) : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦
      LocalSpatialVorticityJets.fullCurlGradient (s.coefficients z.1) j (rightPoint z.2)) :=
    (LocalVorticityEighthMoment.continuous_fullCurlGradient_spaceTime s g hSum hu j).comp
      (f := fun z : Icc (0 : ℝ) T × T6 ↦ (z.1, rightPoint z.2)) hr
  have hK : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ PeriodicRadialRiesz.tensor N
      (leftPoint z.2 - rightPoint z.2)) := (PeriodicRadialRiesz.continuous_tensor N).comp
    ((continuous_leftPoint.comp continuous_snd).sub (continuous_rightPoint.comp continuous_snd))
  have hc : Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ f z.1 z.2) := by
    change Continuous (fun z : Icc (0 : ℝ) T × T6 ↦ ∑ j : Fin 3,
      OcticKernelCorrelation.mixedCurvature (PeriodicRadialRiesz.tensor N (leftPoint z.2 - rightPoint z.2))
        (fullVorticity (s.coefficients z.1) (leftPoint z.2))
        (fullVorticity (s.coefficients z.1) (rightPoint z.2))
        (LocalSpatialVorticityJets.fullCurlGradient (s.coefficients z.1) j (leftPoint z.2))
        (LocalSpatialVorticityJets.fullCurlGradient (s.coefficients z.1) j (rightPoint z.2)))
    apply continuous_finsetSum
    intro j _
    exact OcticKernelCorrelation.continuous_mixedCurvature hK hwl hwr (hgl j) (hgr j)
  have hi := continuous_parametric_integral_of_continuous (μ := (volume : Measure T6))
    (f := fun t : Icc (0 : ℝ) T ↦ f t) hc isCompact_univ
  simp only [Measure.restrict_univ] at hi
  have he (t : Icc (0 : ℝ) T) : (∫ x : T6, f t x) =
      LocalOcticCorrelation.mixedGradientContribution N (s.coefficients t) := by
    have ht := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2))
    have hd := continuous_mixedDensity _ (PeriodicRadialRiesz.continuous_tensor N) (s.coefficients t) ht
    rw [show (∫ x : T6, f t x) = ∫ x : T3, ∫ y : T3,
      mixedDensity (PeriodicRadialRiesz.tensor N) (s.coefficients t) x y from
        UnitTorusProductTransport.integral_pair _
          (hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_mixedDensity_eq N _ ht]
  simp_rw [he] at hi
  exact continuousOn_iff_continuous_restrict.mpr hi

variable (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
include hab hI hg hSum hu

theorem interior_energy_identity (N : ℕ) (ε : ℝ) :
    energy N ε (s.coefficients b) +
      (∫ t in a..b, nu * weightedPalinstrophy (s.coefficients t) +
        6 * nu * radialDissipation (s.coefficients t)) =
    energy N ε (s.coefficients a) +
      ∫ t in a..b, stretching (s.coefficients t) + ε * signedRate N nu (s.coefficients t) := by
  have he := LocalVorticityEighthMoment.interior_energy_identity s g hg hSum hu a b hab hI
  obtain ⟨hi, hc⟩ := integral_signedRate_eq s a b hab hI g hg hSum hu N
  have hs := ((LocalVorticityEighthMoment.continuousOn_stretching s g hSum hu).mono
    (hI.trans Ioo_subset_Icc_self)).intervalIntegrable_of_Icc (μ := volume) hab
  rw [intervalIntegral.integral_add hs (hi.const_mul ε), intervalIntegral.integral_const_mul, hc]
  unfold energy
  linarith only [he]

theorem intervalIntegrable_residual (N : ℕ) (ε : ℝ) :
    IntervalIntegrable (fun t ↦ residual N nu ε (s.coefficients t)) volume a b := by
  have hi := (integral_signedRate_eq s a b hab hI g hg hSum hu N).1
  have hS := ((LocalVorticityEighthMoment.continuousOn_stretching s g hSum hu).mono
    (hI.trans Ioo_subset_Icc_self)).intervalIntegrable_of_Icc (μ := volume) hab
  have hM := ((continuousOn_mixedContribution s g hSum hu N).mono
    (hI.trans Ioo_subset_Icc_self)).intervalIntegrable_of_Icc (μ := volume) hab
  simp_rw [residual_eq_signedRate_add_mixed]
  exact (hS.add (hi.const_mul ε)).add (hM.const_mul (nu * ε))

/-- The mixed term is paid once. The actual remaining source retains its sign. -/
theorem energy_add_half_dissipation_le (N : ℕ) (ε : ℝ) (hnu : 0 ≤ nu) (hε : |ε| ≤ 1 / 576) :
    energy N ε (s.coefficients b) + nu / 2 * (∫ t in a..b, weightedPalinstrophy (s.coefficients t)) ≤
      energy N ε (s.coefficients a) + ∫ t in a..b, residual N nu ε (s.coefficients t) := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) T := hI.trans Ioo_subset_Icc_self
  have hG := ((LocalVorticityEighthMoment.continuousOn_weightedPalinstrophy s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hR := ((LocalVorticityEighthMoment.continuousOn_radialDissipation s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hres := intervalIntegrable_residual s g hg hSum hu a b hab hI N ε
  have he := interior_energy_identity s g hg hSum hu a b hab hI N ε
  have hbound : (∫ t in a..b, stretching (s.coefficients t) + ε * signedRate N nu (s.coefficients t)) ≤
      (∫ t in a..b, residual N nu ε (s.coefficients t) + nu / 2 * weightedPalinstrophy (s.coefficients t)) := by
    apply intervalIntegral.integral_mono_on hab
      (by
        have hS := ((LocalVorticityEighthMoment.continuousOn_stretching s g hSum hu).mono hsub).intervalIntegrable_of_Icc
          (μ := volume) hab
        exact hS.add ((integral_signedRate_eq s a b hab hI g hg hSum hu N).1.const_mul ε))
      (hres.add (hG.const_mul (nu / 2)))
    intro t ht
    have hp := abs_mixed_correction_le N nu ε (s.coefficients t)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (hsub ht))) hnu hε
    rw [residual_eq_signedRate_add_mixed]
    linarith [neg_abs_le (nu * ε * LocalOcticCorrelation.mixedGradientContribution N (s.coefficients t))]
  rw [intervalIntegral.integral_add hres (hG.const_mul (nu / 2)), intervalIntegral.integral_const_mul] at hbound
  rw [intervalIntegral.integral_add (hG.const_mul nu) (hR.const_mul (6 * nu)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  have hr : 0 ≤ 6 * nu * (∫ t in a..b, radialDissipation (s.coefficients t)) :=
    mul_nonneg (mul_nonneg (by norm_num) hnu)
      (intervalIntegral.integral_nonneg_of_forall hab (fun _ ↦ LocalVorticityEighthMoment.radialDissipation_nonneg _))
  linarith only [he, hbound, hr]

end Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrectedEnergy
