import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteFourierTime

/-!
# The actual Laplacian of the infinite velocity field

Second absolute moments justify both coordinate derivatives. Summing the
three ordinary second derivatives recovers the physical viscous symbol,
including its sign and the unit-torus factor.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteSpatialLaplacian

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakeCurlOutputTail PancakeIndexedFourierMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeInfiniteFourierTime
open PancakeFourierTranslationCurve PancakeIncomingLowSourceEnergy

local notation "T3" => UnitAddTorus (Fin 3)

theorem fullFourierField_add (u v : FourierVelocity)
    (hu : Summable (fun q ↦ ‖u q‖)) (hv : Summable (fun q ↦ ‖v q‖)) :
    fullFourierField id (fun q ↦ u q + v q) = fullFourierField id u + fullFourierField id v := by
  have he (q : Wavevector) : modeField q (u q + v q) = modeField q (u q) + modeField q (v q) :=
    (modeFieldCLM q).map_add _ _
  simp only [fullFourierField, id_eq, he]
  exact (summable_modeField id u hu).tsum_add (summable_modeField id v hv)

theorem fullFourierField_finsetSum {ι : Type*} (F : Finset ι) (u : ι → FourierVelocity)
    (hu : ∀ j ∈ F, Summable (fun q ↦ ‖u j q‖)) :
    fullFourierField id (fun q ↦ ∑ j ∈ F, u j q) = ∑ j ∈ F, fullFourierField id (u j) := by
  have he (q : Wavevector) :
      modeField q (∑ j ∈ F, u j q) = ∑ j ∈ F, modeField q (u j q) :=
    map_sum (modeFieldCLM q) _ _
  simp only [fullFourierField, id_eq, he]
  exact Summable.tsum_finsetSum (fun j hj ↦ summable_modeField id (u j) (hu j hj))

theorem fullFourierField_smul (c : ℂ) (u : FourierVelocity) :
    fullFourierField id (fun q ↦ c • u q) = c • fullFourierField id u := by
  simp only [fullFourierField, modeField_smul]
  exact tsum_const_smul'' c

theorem firstMoment_derivative_le_second (u : FourierVelocity) (j : Fin 3) (q : Wavevector) :
    fourierMoment 1 (indexedDerivativeCoeff id j u) q ≤ (2 * Real.pi) * fourierMoment 2 u q := by
  change (1 + ‖frequencyVec q‖)^1 *
    ‖(unitTorusDerivativePhase * (q j : ℂ)) • coefficientVec (u q)‖ ≤ _
  rw [pow_one, norm_smul, norm_mul, norm_derivativePhase]
  calc
    _ ≤ (1 + ‖frequencyVec q‖) *
        ((2 * Real.pi) * (1 + ‖frequencyVec q‖) * ‖coefficientVec (u q)‖) := by
      gcongr
      exact (norm_frequency_coordinate_le q j).trans (le_add_of_nonneg_left zero_le_one)
    _ = _ := by unfold fourierMoment; ring

theorem summable_firstMoment_derivative (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j : Fin 3) :
    Summable (fourierMoment 1 (indexedDerivativeCoeff id j u)) :=
  (hu.mul_left (2 * Real.pi)).of_nonneg_of_le (fourierMoment_nonneg _ _)
    (firstMoment_derivative_le_second u j)

theorem summable_norm_secondDerivative (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j l : Fin 3) :
    Summable (fun q ↦ ‖indexedDerivativeCoeff id l (indexedDerivativeCoeff id j u) q‖) :=
  summable_norm_derivativeCoefficients id _ (by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_derivative u hu j) l

theorem coordinateDerivative2_fullFourierField (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j l : Fin 3) (x : T3) :
    coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) j y) l x =
      fullFourierField id (indexedDerivativeCoeff id l (indexedDerivativeCoeff id j u)) x := by
  have hu1 : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second u hu
  simp only [coordinateDerivative_fullFourierField id u hu1]
  apply coordinateDerivative_fullFourierField
  simpa only [indexedFirstMoment_id] using summable_firstMoment_derivative u hu j

def spatialLaplacian (f : T3 → VelocityCoefficient) (x : T3) : VelocityCoefficient :=
  ∑ j : Fin 3, coordinateDerivative (fun y ↦ coordinateDerivative f j y) j x

def laplacianCoeff (u : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  (unitTorusDerivativePhase^2 * modeSquare q) • u q

theorem sum_secondDerivativeCoeff (u : FourierVelocity) (q : Wavevector) :
    (∑ j : Fin 3, indexedDerivativeCoeff id j (indexedDerivativeCoeff id j u) q) =
      laplacianCoeff u q := by
  ext i
  simp only [Finset.sum_apply, indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul,
    id_eq, laplacianCoeff, modeSquare, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem spatialLaplacian_fullFourierField (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    spatialLaplacian (fullFourierField id u) = fullFourierField id (laplacianCoeff u) := by
  have he := fullFourierField_finsetSum Finset.univ
    (fun j ↦ indexedDerivativeCoeff id j (indexedDerivativeCoeff id j u))
    (fun j _ ↦ summable_norm_secondDerivative u hu j j)
  have hc : (fun q ↦ ∑ j : Fin 3, indexedDerivativeCoeff id j (indexedDerivativeCoeff id j u) q) =
      laplacianCoeff u := funext (sum_secondDerivativeCoeff u)
  rw [hc] at he
  funext x
  simp only [spatialLaplacian, coordinateDerivative2_fullFourierField u hu]
  exact (congrArg (fun f : C(T3, VelocityCoefficient) ↦ f x) he).symm

theorem fullFourierField_viscous (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) :
    fullFourierField id (unitTorusViscousVorticityCoeff nu u) x =
      (nu : ℂ) • spatialLaplacian (fullFourierField id u) x := by
  have hc : unitTorusViscousVorticityCoeff nu u = fun q ↦ (nu : ℂ) • laplacianCoeff u q := by
    ext q i
    simp only [unitTorusViscousVorticityCoeff, laplacianCoeff, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hc, fullFourierField_smul, spatialLaplacian_fullFourierField u hu]
  rfl

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteSpatialLaplacian
