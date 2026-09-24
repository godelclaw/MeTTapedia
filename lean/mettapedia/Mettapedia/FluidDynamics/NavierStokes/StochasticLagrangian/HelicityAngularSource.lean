import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialAdvectionDivergence
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicitySourceEvolution

/-!
# Angular structure of the material helicity source

Combining the cross-derivative terms with the actual pressure Poisson identity
gives `Q = -2 sum_m grad u_m cross partial_m omega`. Pairing with vorticity
therefore removes derivatives parallel to vorticity. No direction field is
divided by its magnitude, so the identity also applies at vorticity zeros.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.HelicityAngularSource

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeSpatialGradientDifferentiation PancakePeriodicComplexStretch
open PancakeInfiniteSpatialPressure PancakeLocalProjectedEquation
open SpatialCurlCurl CurlVorticitySource SpatialAdvectionDivergence
open PancakeDyadicDirectionEvolution PancakeInfiniteRealCurl PancakeLocalStrainReality
open PancakeBlockReality PancakeGalerkinKineticEnergy PancakeLocalGradientEquation
open LocalWeightedCurlCancellation LocalLowDiffusionBudget LocalSpatialVorticityJets
open Mettapedia.Analysis.EuclideanCrossProduct

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The gradient of one velocity component (a row, not a column). -/
def componentGradient (u : FourierVelocity) (m : Fin 3) (x : T3) : VelocityCoefficient :=
  fun j ↦ coordinateDerivative (fullFourierField id u) j x m

theorem spatialSource_eq_cross (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    spatialSource u x = -(2 • (∑ m : Fin 3,
      coefficientCross (componentGradient u m x)
        (coordinateDerivative (spatialCurl (fullFourierField id u)) m x))) := by
  have hu1 := summable_firstMoment_of_second u hu
  have hdf (j : Fin 3) : (fullFourierField id (indexedDerivativeCoeff id j u) : T3 → VelocityCoefficient) =
      (fun y ↦ coordinateDerivative (fullFourierField id u) j y) :=
    (coordinateDerivative_fullFourierField_eq u hu1 j).symm
  have h01 := coordinateDerivative2_commute u hu 0 1 x
  have h02 := coordinateDerivative2_commute u hu 0 2 x
  have h12 := coordinateDerivative2_commute u hu 1 2 x
  unfold spatialSource
  rw [gradient_pressureLaplacian u hu hd]
  ext i
  fin_cases i <;>
    simp [spatialTransport, hdf, componentGradient, coefficientCross, Fin.sum_univ_three,
      gradient_divergence_advection u hu hd, coordinateDerivative_spatialCurl u hu,
      h01, h02, h12] <;> ring

def realComponentGradient (u : FourierVelocity) (m : Fin 3) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (componentGradient u m x)

theorem source_eq_cross (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    LocalHelicitySourceEvolution.source u x =
      -(2 • (∑ m : Fin 3, cross (realComponentGradient u m x) (fullCurlGradient u m x))) := by
  have hu1 := summable_firstMoment_of_second u hu
  have hc : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_curl 1 u hu
  have hreal (m j : Fin 3) : (componentGradient u m x j).im = 0 := by
    have h := congrArg Complex.im (spatialVelocityGradient_reality u hu1 hr x m j)
    simp only [Complex.conj_im] at h
    change -(componentGradient u m x j).im = (componentGradient u m x j).im at h
    linarith
  unfold LocalHelicitySourceEvolution.source
  rw [spatialSource_eq_cross u hu hd, map_neg, map_nsmul, map_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro m _
  rw [realPart_cross _ _ (hreal m), spatialCurl_velocity u hu1,
    coordinateDerivative_fullFourierField id _ hc]
  rfl

/-- Only angular vorticity variation contributes to the inviscid helicity
source; parallel amplitude variation cancels before any norm estimate. -/
theorem inner_vorticity_source (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    ⟪fullVorticity u x, LocalHelicitySourceEvolution.source u x⟫ =
      2 * ∑ m : Fin 3, ⟪realComponentGradient u m x,
        cross (fullVorticity u x) (fullCurlGradient u m x)⟫ := by
  rw [source_eq_cross u hu hd hr]
  have he (m : Fin 3) :
      ⟪fullVorticity u x, cross (realComponentGradient u m x) (fullCurlGradient u m x)⟫ =
        -⟪realComponentGradient u m x, cross (fullVorticity u x) (fullCurlGradient u m x)⟫ := by
    rw [inner_cross_cycle, cross_swap (fullCurlGradient u m x), inner_neg_right]
    ring
  simp only [inner_neg_right, two_smul, inner_add_right, inner_sum, he,
    Finset.sum_neg_distrib]
  ring

theorem inner_vorticity_source_sub_parallel (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) (c : Fin 3 → ℝ) :
    ⟪fullVorticity u x, LocalHelicitySourceEvolution.source u x⟫ =
      2 * ∑ m : Fin 3, ⟪realComponentGradient u m x,
        cross (fullVorticity u x) (fullCurlGradient u m x - c m • fullVorticity u x)⟫ := by
  simpa only [cross_sub_right, cross_smul_right, cross_self, smul_zero, sub_zero] using
    inner_vorticity_source u hu hd hr x

theorem inner_vorticity_source_eq_zero_of_parallel (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) (c : Fin 3 → ℝ)
    (hparallel : ∀ m, fullCurlGradient u m x = c m • fullVorticity u x) :
    ⟪fullVorticity u x, LocalHelicitySourceEvolution.source u x⟫ = 0 := by
  rw [inner_vorticity_source u hu hd hr]
  simp only [hparallel, cross_smul_right, cross_self, smul_zero, inner_zero_right,
    Finset.sum_const_zero, mul_zero]

theorem abs_inner_vorticity_source_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    |⟪fullVorticity u x, LocalHelicitySourceEvolution.source u x⟫| ≤
      2 * ∑ m : Fin 3, ‖realComponentGradient u m x‖ *
        ‖cross (fullVorticity u x) (fullCurlGradient u m x)‖ := by
  rw [inner_vorticity_source u hu hd hr, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun m _ ↦ abs_real_inner_le_norm _ _))

/-- Young's inequality is applied only after the angular cancellation.
The surviving velocity-gradient coefficient is explicitly retained. -/
theorem abs_inner_vorticity_source_le_young (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) (η : ℝ) (hη : 0 < η) :
    |⟪fullVorticity u x, LocalHelicitySourceEvolution.source u x⟫| ≤
      η * (∑ m : Fin 3, ‖cross (fullVorticity u x) (fullCurlGradient u m x)‖ ^ 2) +
        (∑ m : Fin 3, ‖realComponentGradient u m x‖ ^ 2) / η := by
  have hy (a b : ℝ) : 2 * a * b ≤ η * b ^ 2 + a ^ 2 / η := by
    apply (mul_le_mul_iff_right₀ hη).mp
    rw [mul_add, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hη)]
    nlinarith only [sq_nonneg (η * b - a)]
  apply (abs_inner_vorticity_source_le u hu hd hr x).trans
  calc
    _ = ∑ m : Fin 3, 2 * ‖realComponentGradient u m x‖ *
        ‖cross (fullVorticity u x) (fullCurlGradient u m x)‖ := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    _ ≤ ∑ m : Fin 3, (η * ‖cross (fullVorticity u x) (fullCurlGradient u m x)‖ ^ 2 +
        ‖realComponentGradient u m x‖ ^ 2 / η) := Finset.sum_le_sum (fun m _ ↦ hy _ _)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]

theorem weighted_angular_square (u : FourierVelocity) (x : T3) :
    ‖fullVorticity u x‖ ^ 4 *
        (∑ m : Fin 3, ‖cross (fullVorticity u x) (fullCurlGradient u m x)‖ ^ 2) =
      ‖fullVorticity u x‖ ^ 6 * (∑ m : Fin 3, ‖fullCurlGradient u m x‖ ^ 2) -
        ‖fullVorticity u x‖ ^ 4 * (∑ m : Fin 3, ⟪fullVorticity u x, fullCurlGradient u m x⟫ ^ 2) := by
  simp only [norm_cross_sq, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The fourth-power-weighted angular cost uses only the angular part of
octic dissipation. The remaining mixed velocity-gradient cost is not a
global budget and is not assumed bounded here. -/
theorem weighted_abs_source_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) (η : ℝ) (hη : 0 < η) :
    ‖fullVorticity u x‖ ^ 4 * |⟪fullVorticity u x, LocalHelicitySourceEvolution.source u x⟫| ≤
      η * (‖fullVorticity u x‖ ^ 6 * (∑ m : Fin 3, ‖fullCurlGradient u m x‖ ^ 2) -
        ‖fullVorticity u x‖ ^ 4 * (∑ m : Fin 3, ⟪fullVorticity u x, fullCurlGradient u m x⟫ ^ 2)) +
      ‖fullVorticity u x‖ ^ 4 / η * (∑ m : Fin 3, ‖realComponentGradient u m x‖ ^ 2) := by
  apply (mul_le_mul_of_nonneg_left (abs_inner_vorticity_source_le_young u hu hd hr x η hη)
    (by positivity : 0 ≤ ‖fullVorticity u x‖ ^ 4)).trans_eq
  rw [← weighted_angular_square]
  ring

end Mettapedia.FluidDynamics.NavierStokes.HelicityAngularSource
