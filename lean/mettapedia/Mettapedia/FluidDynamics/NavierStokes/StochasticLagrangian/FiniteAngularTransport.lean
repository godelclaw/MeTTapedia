import Mettapedia.Analysis.AngularCurlTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularSourceWork
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialVorticityInviscidRate

/-!
# Actual Fourier transport stress of angular curl energy

The advecting velocity, its divergence-free derivative matrix, and all
transported vorticity jets are reconstructed from Fourier coefficients.
Scalar transport cancels; the signed first-jet deformation stress remains.
This identity does not assign it a favorable sign or a global time budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteAngularTransport

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeHaarTransportRate
open PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments
open PancakeWeakIncompressibleTransport PancakePeriodicWeakDerivative
open PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution PancakeFourierMaterialPaths
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityEighthMoment
open FourierFiniteSupport FiniteVorticityMixedJets LocalProjectionTransport
open FiniteAngularSourceWork InfiniteFourierTransport
open InfiniteFourierDiffusion PancakeLocalGradientEquation
open PancakeInfiniteSpatialCurl

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- First index: differentiation direction; second index: velocity component. -/
def velocityDerivative (u : FourierVelocity) (j k : Fin 3) (x : T3) : ℝ :=
  mappedField complexRealPartEuclideanCLM (indexedDerivativeCoeff id j u) x k

theorem continuous_velocityDerivative (u : FourierVelocity) (j k : Fin 3) :
    Continuous (velocityDerivative u j k) :=
  (PiLp.continuous_apply 2 _ k).comp (continuous_mappedField _)

theorem hasDerivAt_velocityComponent (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j k : Fin 3) (x : T3) (t : ℝ) :
    HasDerivAt (fun τ ↦ velocityComponent u k (x + coordinateShift j τ))
      (velocityDerivative u j k (x + coordinateShift j t)) t := by
  have h := (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_mappedField_shift P u hs j x t)
  change HasDerivAt (fun τ ↦ mappedField complexRealPartEuclideanCLM u (x + coordinateShift j τ) k)
    (velocityDerivative u j k (x + coordinateShift j t)) t at h
  simpa only [mappedField, complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
    velocityComponent] using h

theorem velocityDerivative_eq (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (j k : Fin 3) (x : T3) :
    velocityDerivative u j k x = (coordinateDerivative (fullFourierField id u) j x k).re := by
  have h := (hasDerivAt_velocityComponent P u hs j k x 0).deriv
  change shiftRate (velocityComponent u k) (coordinateShift j) x = _ at h
  simpa only [coordinateShift_zero, add_zero,
    shiftRate_velocityComponent u (summable_fourierMoment P u hs 1)] using h.symm

theorem sum_velocityDerivative_diagonal (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    (∑ j : Fin 3, velocityDerivative u j j x) = 0 := by
  have h := coordinateDivergence_velocity_zero u (summable_fourierMoment P u hs 2) hd x
  simpa only [coordinateDivergence, velocityDerivative_eq P u hs,
    shiftRate_velocityComponent u (summable_fourierMoment P u hs 1)] using h

def deformationDensity (u v : FourierVelocity) (x : T3) : ℝ :=
  AngularCurlDecomposition.deformationWork (fullVorticity v x) (fun j ↦ fullCurlGradient v j x)
    (fun j k ↦ velocityDerivative u j k x)

def deformationIntegral (u v : FourierVelocity) : ℝ := ∫ x : T3, deformationDensity u v x

theorem integral_angularGradient_transport (P Q : Finset Wavevector) (u v : FourierVelocity)
    (hu : ∀ q, q ∉ P → u q = 0) (hv : ∀ q, q ∉ Q → v q = 0)
    (hd : ∀ q, modeDot q (u q) = 0) :
    (∫ x : T3, ⟪angularGradient v x, transportVorticity u v x⟫) = deformationIntegral u v := by
  exact AngularCurlDecomposition.integral_variationalGradient_transport
    (fullVorticity v) (fullCurlGradient v) (fun j k ↦ mixed v k j)
    (velocityComponent u) (velocityDerivative u) coordinateShift
    (continuous_fullVorticity v (summable_fourierMoment Q v hv 1))
    (LocalSquaredGapGradient.continuous_fullCurlGradient v) (fun _ _ ↦ continuous_mappedField _)
    (continuous_velocityComponent u) (continuous_velocityDerivative u)
    continuous_coordinateShift coordinateShift_zero
    (hasDerivAt_fullVorticity_shift v (summable_fourierMoment Q v hv 3))
    (fun j k ↦ hasDerivAt_gradient_shift Q v hv k j) (hasDerivAt_velocityComponent P u hu)
    (fun j k x ↦ congrFun (mixed_commute v k j) x) (sum_velocityDerivative_diagonal P u hu hd)

theorem integral_octic_transport_zero (P Q : Finset Wavevector) (u v : FourierVelocity)
    (hu : ∀ q, q ∉ P → u q = 0) (hv : ∀ q, q ∉ Q → v q = 0)
    (hd : ∀ q, modeDot q (u q) = 0) :
    (∫ x : T3, ‖fullVorticity v x‖ ^ 6 * ⟪fullVorticity v x, transportVorticity u v x⟫) = 0 := by
  let df (j : Fin 3) (x : T3) := ‖fullVorticity v x‖ ^ 6 * ⟪fullVorticity v x, fullCurlGradient v j x⟫
  have ha := continuous_fullVorticity v (summable_fourierMoment Q v hv 1)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient v
  have hdf (j : Fin 3) (x : T3) (h : ℝ) :
      HasDerivAt (fun t ↦ energy v (x + coordinateShift j t) / 8) (df j (x + coordinateShift j h)) h := by
    have hh := ((hasDerivAt_fullVorticity_shift v (summable_fourierMoment Q v hv 3) j x h).norm_sq.fun_pow 4).div_const 8
    apply hh.congr_deriv
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, ← pow_mul, Nat.reduceMul]
    dsimp [df]
    ring
  have hz := UnitTorusContinuousRate.integral_sum_mul_rate_eq_zero (fun x ↦ energy v x / 8) df
    (velocityComponent u) (fun j ↦ velocityDerivative u j j) coordinateShift
    (((ha.norm.pow 2).pow 4).div_const 8)
    (fun j ↦ (ha.norm.pow 6).mul (ha.inner (hD j)))
    (continuous_velocityComponent u) (fun j ↦ continuous_velocityDerivative u j j)
    continuous_coordinateShift coordinateShift_zero hdf (fun j ↦ hasDerivAt_velocityComponent P u hu j j)
    (sum_velocityDerivative_diagonal P u hu hd)
  have he (x : T3) : ‖fullVorticity v x‖ ^ 6 * ⟪fullVorticity v x, transportVorticity u v x⟫ =
      ∑ j : Fin 3, velocityComponent u j x * df j x := by
    simp only [transportVorticity, df, inner_add_right, real_inner_smul_right, Fin.sum_univ_three]
    ring
  simpa only [he] using hz

/-- The scalar flux vanishes, but the correction contributes a signed
deformation stress with the indicated sign. -/
theorem integral_correctedGradient_transport (κ : ℝ) (P Q : Finset Wavevector) (u v : FourierVelocity)
    (hu : ∀ q, q ∉ P → u q = 0) (hv : ∀ q, q ∉ Q → v q = 0)
    (hd : ∀ q, modeDot q (u q) = 0) :
    (∫ x : T3, ⟪correctedGradient κ v x, transportVorticity u v x⟫) =
      -(3 / κ) * deformationIntegral u v := by
  have ha := continuous_fullVorticity v (summable_fourierMoment Q v hv 1)
  have ht : Continuous (transportVorticity u v) := continuous_finsetSum _ (fun j _ ↦
    (continuous_velocityComponent u j).smul (LocalSquaredGapGradient.continuous_fullCurlGradient v j))
  have hiA : Integrable (fun x : T3 ↦ ‖fullVorticity v x‖ ^ 6 *
      ⟪fullVorticity v x, transportVorticity u v x⟫) :=
    ((ha.norm.pow 6).mul (ha.inner ht)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hiJ : Integrable (fun x : T3 ↦ ⟪angularGradient v x, transportVorticity u v x⟫) :=
    ((continuous_angularGradient Q v hv).inner ht).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  simp only [correctedGradient, inner_sub_left, real_inner_smul_left]
  rw [integral_sub hiA (hiJ.const_mul _), integral_const_mul,
    integral_octic_transport_zero P Q u v hu hv hd, integral_angularGradient_transport P Q u v hu hv hd]
  ring

end Mettapedia.FluidDynamics.NavierStokes.FiniteAngularTransport
