import Mettapedia.Analysis.PeriodicRadialCorrelationEnergy
import Mettapedia.Analysis.PeriodicRadialCorrelationDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialPeriodicEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthEnergy

/-!
# An actual-vorticity correlation correction and its material rate

The correction is uniformly dominated by the eighth moment. Its two-endpoint
material derivative retains stretching, viscosity and relative kernel
transport. No favorable sign or global control of that derivative is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation

open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths PancakeLocalMaterialTrajectories
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalVorticitySeparation LocalAlignmentForcing
open LocalMeanAlignmentBalance (velocity)
open PancakeFourierTranslationCurve (coordinateShift)
open LocalRadialPeriodicEvolution (torusProjection_separation)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def correlation (N : ℕ) (u : FourierVelocity) : ℝ :=
  PeriodicRadialRiesz.octicCorrelation N (fullVorticity u)

theorem eighthMoment_eq_meanEnergy (u : FourierVelocity) :
    PeriodicRadialRiesz.eighthMoment (fullVorticity u) = LocalVorticityEighthMoment.meanEnergy u := by
  simp only [PeriodicRadialRiesz.eighthMoment, LocalVorticityEighthMoment.meanEnergy,
    LocalVorticityEighthMoment.energy_eq_norm_pow]

theorem abs_correlation_le (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    |correlation N u| ≤ 9 * LocalVorticityEighthMoment.meanEnergy u := by
  have h := PeriodicRadialRiesz.abs_octicCorrelation_le N _ (continuous_fullVorticity u hu)
  simpa only [correlation, eighthMoment_eq_meanEnergy, Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] using h

theorem corrected_energy_bounds (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (ε : ℝ) (hε : |ε| ≤ 1 / 18) :
    LocalVorticityEighthMoment.meanEnergy u / 2 ≤
        LocalVorticityEighthMoment.meanEnergy u + ε * correlation N u ∧
      LocalVorticityEighthMoment.meanEnergy u + ε * correlation N u ≤
        3 / 2 * LocalVorticityEighthMoment.meanEnergy u := by
  have he := LocalVorticityEighthMoment.meanEnergy_nonneg u
  have h := mul_le_mul_of_nonneg_left (abs_correlation_le N u hu) (abs_nonneg ε)
  have hbound : |ε * correlation N u| ≤ LocalVorticityEighthMoment.meanEnergy u / 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_right hε (by positivity : 0 ≤ 9 * LocalVorticityEighthMoment.meanEnergy u)]
  rw [abs_le] at hbound
  constructor <;> linarith [hbound.1, hbound.2]

def pairDensity (N : ℕ) (u : FourierVelocity) (x y : T3) : ℝ :=
  OcticKernelCorrelation.density (PeriodicRadialRiesz.tensor N (x - y))
    (fullVorticity u x) (fullVorticity u y)

theorem correlation_eq_pairIntegral (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    correlation N u = ∫ x : T3, ∫ y : T3, pairDensity N u x y :=
  PeriodicRadialRiesz.octicCorrelation_eq_pairIntegral N _ (continuous_fullVorticity u hu)

def periodicRate (N : ℕ) (u : FourierVelocity) (nu : ℝ) (x y : X3) : ℝ :=
  OcticKernelCorrelation.materialRate (PeriodicRadialRiesz.tensor N (torusPoint x - torusPoint y))
    (PeriodicRadialRiesz.liftedTensorDerivative N (separation x y)
      (velocity u (torusPoint x) - velocity u (torusPoint y)))
    (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y))
    (fullStrainOperator u (torusPoint x) (fullVorticity u (torusPoint x)) +
      nu • fullVorticityLaplacian u (torusPoint x))
    (fullStrainOperator u (torusPoint y) (fullVorticity u (torusPoint y)) +
      nu • fullVorticityLaplacian u (torusPoint y))

def fieldRate (N : ℕ) (u : FourierVelocity) (nu : ℝ) (x y : T3) : ℝ :=
  OcticKernelCorrelation.materialRate (PeriodicRadialRiesz.tensor N (x - y))
    (UnitTorusPeriodization.periodize (RadialRieszRegularization.tensorDerivative N) (x - y)
      (velocity u x - velocity u y))
    (fullVorticity u x) (fullVorticity u y)
    (fullStrainOperator u x (fullVorticity u x) + nu • fullVorticityLaplacian u x)
    (fullStrainOperator u y (fullVorticity u y) + nu • fullVorticityLaplacian u y)

theorem periodicRate_eq_fieldRate (N : ℕ) (u : FourierVelocity) (nu : ℝ) (x y : X3) :
    periodicRate N u nu x y = fieldRate N u nu (torusPoint x) (torusPoint y) := by
  simp only [periodicRate, fieldRate, PeriodicRadialRiesz.liftedTensorDerivative_eq_periodize,
    torusProjection_separation]

theorem hasDerivAt_pairDensity_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t) (N : ℕ) :
    HasDerivAt (fun τ ↦ pairDensity N (s.coefficients τ) (torusPoint (X τ)) (torusPoint (Y τ)))
      (periodicRate N (s.coefficients t) nu (X t) (Y t)) t := by
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hh : HasDerivAt (fun τ ↦ separation (X τ) (Y τ))
      (velocity (s.coefficients t) (torusPoint (X t)) -
        velocity (s.coefficients t) (torusPoint (Y t))) t :=
    L.hasFDerivAt.comp_hasDerivAt t (hX.sub hY)
  have hH := (PeriodicRadialRiesz.hasFDerivAt_tensor_lift N (separation (X t) (Y t))).comp_hasDerivAt t hh
  simp only [Function.comp_def, torusProjection_separation] at hH
  exact OcticKernelCorrelation.hasDerivAt_density hx hy hH

theorem periodicRate_split_viscosity (N : ℕ) (u : FourierVelocity) (nu : ℝ) (x y : X3) :
    periodicRate N u nu x y = periodicRate N u 0 x y + nu *
      OcticKernelCorrelation.endpointRate (PeriodicRadialRiesz.tensor N (torusPoint x - torusPoint y))
        (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y))
        (fullVorticityLaplacian u (torusPoint x)) (fullVorticityLaplacian u (torusPoint y)) := by
  simp only [periodicRate, OcticKernelCorrelation.materialRate_add_smul_endpoint, zero_smul, add_zero]

def mixedGradientContribution (N : ℕ) (u : FourierVelocity) : ℝ :=
  ∑ j : Fin 3, PeriodicRadialRiesz.mixedGradientSum N (fullVorticity u)
    (LocalSpatialVorticityJets.fullCurlGradient u j)

theorem abs_mixedGradientContribution_le (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    |mixedGradientContribution N u| ≤ 288 * LocalVorticityEighthMoment.weightedPalinstrophy u := by
  have hw := continuous_fullVorticity u hu
  have hg (j : Fin 3) := LocalSquaredGapGradient.continuous_fullCurlGradient u j
  have hi (j : Fin 3) : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 *
      ‖LocalSpatialVorticityJets.fullCurlGradient u j x‖ ^ 2) :=
    ((hw.norm.pow 6).mul ((hg j).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (∑ j : Fin 3, ∫ x : T3, ‖fullVorticity u x‖ ^ 6 *
      ‖LocalSpatialVorticityJets.fullCurlGradient u j x‖ ^ 2) =
      LocalVorticityEighthMoment.weightedPalinstrophy u := by
    rw [← integral_finsetSum _ (fun j _ ↦ hi j)]
    simp only [LocalVorticityEighthMoment.weightedPalinstrophy,
      GaussianRootWeightedIncrement.weightedPalinstrophyDensity, Finset.mul_sum]
  calc
    _ ≤ ∑ j : Fin 3, |PeriodicRadialRiesz.mixedGradientSum N (fullVorticity u)
        (LocalSpatialVorticityJets.fullCurlGradient u j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, 288 * ∫ x : T3, ‖fullVorticity u x‖ ^ 6 *
        ‖LocalSpatialVorticityJets.fullCurlGradient u j x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Nat.cast_ofNat, show (32 : ℝ) * 3 ^ 2 = 288 by norm_num] using
        PeriodicRadialRiesz.abs_mixedGradientSum_le N _ _ hw (hg j)
    _ = _ := by rw [← Finset.mul_sum, he]

theorem mixedGradientContribution_eq_pairIntegral (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    mixedGradientContribution N u = ∑ j : Fin 3, ∫ x : T3, ∫ y : T3,
      OcticKernelCorrelation.mixedCurvature (PeriodicRadialRiesz.tensor N (x - y))
        (fullVorticity u x) (fullVorticity u y)
        (LocalSpatialVorticityJets.fullCurlGradient u j x)
        (LocalSpatialVorticityJets.fullCurlGradient u j y) := by
  apply Finset.sum_congr rfl
  intro j _
  exact PeriodicRadialRiesz.mixedGradientSum_eq_pairIntegral N _ _ (continuous_fullVorticity u hu)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j)

/-- Both endpoints are translated together; the actual separation kernel is fixed. -/
theorem hasDerivAt_endpointRate_shift (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (x y : T3) :
    HasDerivAt (fun τ : ℝ ↦ OcticKernelCorrelation.endpointRate (PeriodicRadialRiesz.tensor N (x - y))
      (fullVorticity u (x + coordinateShift j τ))
      (fullVorticity u (y + coordinateShift j τ))
      (LocalSpatialVorticityJets.fullCurlGradient u j (x + coordinateShift j τ))
      (LocalSpatialVorticityJets.fullCurlGradient u j (y + coordinateShift j τ)))
      (OcticKernelCorrelation.endpointRate (PeriodicRadialRiesz.tensor N (x - y))
        (fullVorticity u x) (fullVorticity u y)
        (LocalJointDiffusionBudget.fullCurlSecond u j x) (LocalJointDiffusionBudget.fullCurlSecond u j y) +
      OcticKernelCorrelation.pureCurvature (PeriodicRadialRiesz.tensor N (x - y))
        (fullVorticity u x) (fullVorticity u y)
        (LocalSpatialVorticityJets.fullCurlGradient u j x) (LocalSpatialVorticityJets.fullCurlGradient u j y) +
      OcticKernelCorrelation.mixedCurvature (PeriodicRadialRiesz.tensor N (x - y))
        (fullVorticity u x) (fullVorticity u y)
        (LocalSpatialVorticityJets.fullCurlGradient u j x) (LocalSpatialVorticityJets.fullCurlGradient u j y)) 0 := by
  have h := OcticKernelCorrelation.hasDerivAt_endpointRate (PeriodicRadialRiesz.tensor N (x - y))
    (LocalSpatialVorticityJets.hasDerivAt_fullVorticity_shift u hu j x 0)
    (LocalSpatialVorticityJets.hasDerivAt_fullVorticity_shift u hu j y 0)
    (LocalSpatialVorticityJets.hasDerivAt_fullCurlGradient_shift u hu j x 0)
    (LocalSpatialVorticityJets.hasDerivAt_fullCurlGradient_shift u hu j y 0)
  simpa only [PancakeHaarTransportRate.coordinateShift_zero, add_zero] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalOcticCorrelation
