import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMixedGradientBudget

/-!
# Advection energy and the actual velocity supremum

Squared advection is bounded by the actual velocity supremum squared times
enstrophy. The supremum is constructed from the continuous full velocity;
it is not an assumed constant or an initial-data bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAdvectionEnstrophy

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeBlockReality PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakeLocalStrainReality PancakeLocalGradientEquation
open PancakeInfiniteSpatialPressure PancakePhysicalConvectionCoefficients
open LocalLowDiffusionBudget LocalVorticityEighthMoment
open LocalMeanAlignmentBalance (velocity continuous_velocity)
open CurlVorticitySource HelicityAngularSource HelicityAngularBudget
open LocalWeightedDivCurl LocalMixedGradientBudget
open InfiniteConvectionEnergy PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def velocitySupNorm (u : FourierVelocity) : ℝ :=
  ‖(⟨velocity u, continuous_velocity u⟩ : C(T3, R3))‖

theorem norm_velocity_le (u : FourierVelocity) (x : T3) :
    ‖velocity u x‖ ≤ velocitySupNorm u :=
  (⟨velocity u, continuous_velocity u⟩ : C(T3, R3)).norm_coe_le_norm x

theorem advection_apply (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) (m : Fin 3) :
    advection u x m = ⟪realComponentGradient u m x, velocity u x⟫ := by
  have hu1 := summable_firstMoment_of_second u hu
  have hreal (j : Fin 3) : (coordinateDerivative (fullFourierField id u) j x m).im = 0 := by
    have h := congrArg Complex.im (spatialVelocityGradient_reality u hu1 hr x m j)
    simp only [Complex.conj_im] at h
    change -(coordinateDerivative (fullFourierField id u) j x m).im =
      (coordinateDerivative (fullFourierField id u) j x m).im at h
    linarith
  have he : (fullFourierField id (advectionCoeff u) : T3 → VelocityCoefficient) =
      spatialAdvection (fullFourierField id u) := fullFourierField_advection u hu hd
  simp [advection, he, spatialAdvection, velocity, realComponentGradient, componentGradient,
    complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, Complex.mul_re, hreal]

theorem norm_advection_sq_le (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    ‖advection u x‖ ^ 2 ≤ ‖velocity u x‖ ^ 2 * gradientSquare u x := by
  rw [EuclideanSpace.real_norm_sq_eq, gradientSquare, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  rw [advection_apply u hu hd hr]
  simpa only [pow_two, real_inner_self_eq_norm_sq, mul_comm] using
    real_inner_mul_inner_self_le (realComponentGradient u m x) (velocity u x)

theorem advectionSquareIntegral_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    advectionSquareIntegral u ≤ velocitySupNorm u ^ 2 *
      ∫ x : T3, ‖fullVorticity u x‖ ^ 2 := by
  have hu2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu
  have hu1 := summable_firstMoment_of_second u hu2
  have hA : Integrable (fun x : T3 ↦ ‖advection u x‖ ^ 2) :=
    ((continuous_advection u).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (fun x : T3 ↦ velocitySupNorm u ^ 2 * gradientSquare u x) :=
    ((continuous_gradientSquare u hu1).const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    advectionSquareIntegral u ≤ ∫ x : T3, velocitySupNorm u ^ 2 * gradientSquare u x := by
      apply integral_mono hA hG
      intro x
      exact (norm_advection_sq_le u hu2 hd hr x).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_velocity_le u x) 2)
          (by unfold gradientSquare; positivity))
    _ = _ := by rw [integral_const_mul, integral_gradientSquare_eq u hu hd hr]

theorem advectionSquareIntegral_le_kineticEnstrophy (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    advectionSquareIntegral u ≤ velocitySupNorm u ^ 2 * kineticEnergy (fourierCurl u) :=
  (advectionSquareIntegral_le u hu hd hr).trans (mul_le_mul_of_nonneg_left
    (integral_norm_fullVorticity_sq_le u (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu))
    (sq_nonneg _))

theorem sixthMoment_le_one_add_meanEnergy (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : sixthMoment u ≤ 1 + meanEnergy u := by
  have hw := continuous_fullVorticity u hu
  have h6 : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6) :=
    (hw.norm.pow 6).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h8 : Integrable (fun x : T3 ↦ (‖fullVorticity u x‖ ^ 2) ^ 4) :=
    ((hw.norm.pow 2).pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : Integrable (fun _ : T3 ↦ (1 : ℝ)) := integrable_const 1
  have hi : Integrable (fun x : T3 ↦ 1 + (‖fullVorticity u x‖ ^ 2) ^ 4) := h1.add h8
  have h := integral_mono h6 hi (fun x ↦ show
      ‖fullVorticity u x‖ ^ 6 ≤ 1 + (‖fullVorticity u x‖ ^ 2) ^ 4 from by
    rw [← pow_mul]
    by_cases hx : ‖fullVorticity u x‖ ≤ 1
    · have hp := pow_le_pow_left₀ (norm_nonneg _) hx 6
      norm_num at hp
      exact hp.trans (le_add_of_nonneg_right (by positivity))
    · have hp := pow_le_pow_right₀ (le_of_not_ge hx) (show 6 ≤ 2 * 4 by omega)
      exact hp.trans (le_add_of_nonneg_left (by norm_num)))
  rw [integral_add h1 h8] at h
  simpa only [sixthMoment, meanEnergy, energy, integral_const, probReal_univ, one_smul] using h

/-- An explicit lower-order remainder after radial/angular recombination.
The velocity supremum still needs a dynamical or elliptic estimate. -/
theorem weightedSource_le_velocity_enstrophy (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (η : ℝ) (hη : 0 < η) :
    weightedSource u ≤ η * weightedPalinstrophy u + (1 + meanEnergy u) / η +
      4 * velocitySupNorm u ^ 2 * kineticEnergy (fourierCurl u) / η ^ 3 := by
  have h6 := div_le_div_of_nonneg_right
    (sixthMoment_le_one_add_meanEnergy u (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu)) hη.le
  have hA := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (advectionSquareIntegral_le_kineticEnstrophy u hu hd hr) (by norm_num : (0 : ℝ) ≤ 4))
    (le_of_lt (pow_pos hη 3))
  have h := add_le_add (add_le_add (le_refl (η * weightedPalinstrophy u)) h6) hA
  exact (weightedSource_le_dissipation_advection u hu hd hr η hη).trans (by
    simpa only [mul_assoc] using h)

end Mettapedia.FluidDynamics.NavierStokes.LocalAdvectionEnstrophy
