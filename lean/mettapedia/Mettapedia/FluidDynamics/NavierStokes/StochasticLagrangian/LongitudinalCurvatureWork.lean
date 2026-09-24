import Mettapedia.Analysis.UnitTorusTransportPairing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalVorticityDiffusion

/-!
# Signed longitudinal curvature work without a velocity-Hessian norm

The two inviscid terms are kept together before integration by parts.
For `q = (ω·∇)ω`, their pairing with `q` is exactly
`-∫ ⟨(ω·∇)q, (ω·∇)u⟩`. This removes the explicit velocity Hessian
from the pairing; it does not bound the surviving weighted stretching.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalCurvatureWork

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis LongitudinalJetEvolution
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeInfiniteSpatialLaplacian
open PancakeFourierTranslationCurve PancakeHaarTransportRate PancakeGalerkinKineticEnergy
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeInfiniteRealCurl
open FullLambVector FullVorticityGradientTransport LocalLongitudinalVorticity
open LongitudinalVorticityDiffusion LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalWeightedCurlCancellation LocalVorticitySeparation LocalAlignmentForcing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def vorticityStretch (u : FourierVelocity) (x : T3) : R3 :=
  longitudinal (fullVorticity u x) (fun j ↦ velocityJet u j x)

theorem vorticityStretch_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    vorticityStretch u x = fullStrainOperator u x (fullVorticity u x) := by
  rw [vorticityStretch, longitudinal, directional_velocityJet u hu, gradient_vorticity]

theorem continuous_longitudinalVorticity (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (longitudinalVorticity u) :=
  continuous_longitudinal (continuous_fullVorticity u hu)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)

theorem continuous_vorticityStretch (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (vorticityStretch u) :=
  continuous_longitudinal (continuous_fullVorticity u hu) (continuous_velocityJet u)

theorem continuous_longitudinalGradient (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (k : Fin 3) : Continuous (longitudinalGradient u k) :=
  continuous_rate (continuous_fullVorticity u hu)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u k)
    (fun j ↦ continuous_velocityJet (indexedDerivativeCoeff id j (fourierCurl u)) k)

theorem continuous_stretchingDerivative (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) : Continuous (stretchingDerivative u j) :=
  continuous_rate (continuous_fullVorticity u hu) (continuous_velocityJet u)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
    (fun k ↦ continuous_velocityJet (indexedDerivativeCoeff id k u) j)

theorem hasDerivAt_vorticityStretch_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ vorticityStretch u (x + coordinateShift j t))
      (stretchingDerivative u j (x + coordinateShift j h)) h :=
  hasDerivAt_longitudinal (hasDerivAt_fullVorticity_shift_second u hu j x h)
    (fun k ↦ hasDerivAt_velocityJet_shift u hu k j x h)

theorem inviscidRate_eq_transport_stretching (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    inviscidRate u x = ∑ j, fullVorticity u x j • stretchingDerivative u j x := by
  unfold inviscidRate
  rw [← directional_velocityJet u hu]
  simp only [longitudinalVorticity, longitudinal, curvatureSource, velocityCurvature,
    stretchingDerivative, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  module

/-- Exact signed pairing of both inviscid sources; the Hessian is not
estimated separately. The remaining product still needs a dynamic bound. -/
theorem integral_longitudinal_inviscidRate (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, ⟪longitudinalVorticity u x, inviscidRate u x⟫) =
      -(∫ x : T3, ⟪∑ j, fullVorticity u x j • longitudinalGradient u j x,
        fullStrainOperator u x (fullVorticity u x)⟫) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hz := UnitTorusTransportPairing.integral_inner_transport
    (longitudinalVorticity u) (vorticityStretch u)
    (longitudinalGradient u) (stretchingDerivative u)
    (fun j x ↦ fullVorticity u x j) (fun j x ↦ fullCurlGradient u j x j) coordinateShift
    (continuous_longitudinalVorticity u hu1) (continuous_vorticityStretch u hu1)
    (continuous_longitudinalGradient u hu1) (continuous_stretchingDerivative u hu1)
    (fun j ↦ (EuclideanSpace.proj j).continuous.comp (continuous_fullVorticity u hu1))
    (fun j ↦ (EuclideanSpace.proj j).continuous.comp
      (LocalSquaredGapGradient.continuous_fullCurlGradient u j))
    continuous_coordinateShift coordinateShift_zero
    (hasDerivAt_longitudinal_shift u hu) (hasDerivAt_vorticityStretch_shift u hu2)
    (fun j x h ↦ by
      simpa [EuclideanSpace.inner_single_left] using
        (hasDerivAt_const h (EuclideanSpace.single j (1 : ℝ))).inner ℝ
          (hasDerivAt_fullVorticity_shift_second u hu2 j x h))
    (sum_fullCurlGradient_diagonal_eq_zero u hu)
  simpa only [← inviscidRate_eq_transport_stretching u hu1, vorticityStretch_eq u hu1] using hz

theorem sum_mixedGradient_curl_diagonal (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (k : Fin 3) (x : T3) :
    (∑ j : Fin 3, mixedGradient (fourierCurl u) k j x j) = 0 := by
  have hj (j : Fin 3) :
      HasDerivAt (fun t ↦ fullCurlGradient u j (x + coordinateShift k t) j)
        (mixedGradient (fourierCurl u) j k (x + coordinateShift k 0) j) 0 := by
    simpa [EuclideanSpace.inner_single_left] using
      (hasDerivAt_const 0 (EuclideanSpace.single j (1 : ℝ))).inner ℝ
        (hasDerivAt_fullCurlGradient_shift_mixed u hu j k x 0)
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hj j)
  change HasDerivAt (fun t ↦ ∑ j : Fin 3, fullCurlGradient u j (x + coordinateShift k t) j) _ 0 at hh
  simp_rw [sum_fullCurlGradient_diagonal_eq_zero u hu] at hh
  have he := hh.unique (hasDerivAt_const 0 (0 : ℝ))
  simpa only [coordinateShift_zero, add_zero, mixedGradient_commute (fourierCurl u) _ k] using he

theorem integral_longitudinal_gradientTransport (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (k : Fin 3) :
    (∫ x : T3, ⟪longitudinalVorticity u x,
      ∑ j, fullCurlGradient u k x j • mixedGradient (fourierCurl u) k j x⟫) =
      -(∫ x : T3, ⟪∑ j, fullCurlGradient u k x j • longitudinalGradient u j x,
        fullCurlGradient u k x⟫) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  exact UnitTorusTransportPairing.integral_inner_transport
    (longitudinalVorticity u) (fullCurlGradient u k)
    (longitudinalGradient u) (fun j x ↦ mixedGradient (fourierCurl u) k j x)
    (fun j x ↦ fullCurlGradient u k x j) (fun j x ↦ mixedGradient (fourierCurl u) k j x j)
    coordinateShift (continuous_longitudinalVorticity u hu1)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u k)
    (continuous_longitudinalGradient u hu1)
    (fun j ↦ continuous_velocityJet (indexedDerivativeCoeff id k (fourierCurl u)) j)
    (fun j ↦ (EuclideanSpace.proj j).continuous.comp
      (LocalSquaredGapGradient.continuous_fullCurlGradient u k))
    (fun j ↦ (EuclideanSpace.proj j).continuous.comp
      (continuous_velocityJet (indexedDerivativeCoeff id k (fourierCurl u)) j))
    continuous_coordinateShift coordinateShift_zero (hasDerivAt_longitudinal_shift u hu)
    (fun j ↦ hasDerivAt_fullCurlGradient_shift_mixed u hu k j)
    (fun j x h ↦ by
      simpa [EuclideanSpace.inner_single_left] using
        (hasDerivAt_const h (EuclideanSpace.single j (1 : ℝ))).inner ℝ
          (hasDerivAt_fullCurlGradient_shift_mixed u hu k j x h))
    (sum_mixedGradient_curl_diagonal u hu k)

/-- The mixed viscous work also transfers its highest derivative onto
the longitudinal test. The remaining quadratic gradient flux is retained. -/
theorem integral_longitudinal_viscousCross (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, ⟪longitudinalVorticity u x, viscousCross u x⟫) =
      -(∑ k : Fin 3, ∫ x : T3,
        ⟪∑ j, fullCurlGradient u k x j • longitudinalGradient u j x,
          fullCurlGradient u k x⟫) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hi (k : Fin 3) : Integrable (fun x : T3 ↦ ⟪longitudinalVorticity u x,
      ∑ j, fullCurlGradient u k x j • mixedGradient (fourierCurl u) k j x⟫) := by
    have hc : Continuous (fun x ↦ ∑ j, fullCurlGradient u k x j •
        mixedGradient (fourierCurl u) k j x) :=
      continuous_finsetSum _ (fun j _ ↦
        ((EuclideanSpace.proj j).continuous.comp
          (LocalSquaredGapGradient.continuous_fullCurlGradient u k)).smul
            (continuous_velocityJet (indexedDerivativeCoeff id k (fourierCurl u)) j))
    exact ((continuous_longitudinalVorticity u hu1).inner hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : T3) : ⟪longitudinalVorticity u x, viscousCross u x⟫ =
      ∑ k, ⟪longitudinalVorticity u x,
        ∑ j, fullCurlGradient u k x j • mixedGradient (fourierCurl u) k j x⟫ := by
    simp only [viscousCross, diffusionCross, inner_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [mixedGradient_commute (fourierCurl u) _ k]
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ ↦ hi k)]
  simp only [integral_longitudinal_gradientTransport u hu, Finset.sum_neg_distrib]

theorem continuous_longitudinalSecond (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (k : Fin 3) : Continuous (longitudinalSecond u k) := by
  have hr := continuous_rate (continuous_fullVorticity u hu)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)
    (continuous_velocityJet (indexedDerivativeCoeff id k (fourierCurl u)) k)
    (fun j ↦ continuous_velocityJet
      (indexedDerivativeCoeff id k (indexedDerivativeCoeff id j (fourierCurl u))) k)
  have hc := continuous_longitudinal (LocalSquaredGapGradient.continuous_fullCurlGradient u k)
    (fun j ↦ continuous_velocityJet (indexedDerivativeCoeff id j (fourierCurl u)) k)
  exact hr.add (continuous_const.smul hc)

theorem integral_longitudinal_laplacian (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) :
    (∫ x : T3, ⟪longitudinalVorticity u x, longitudinalLaplacian u x⟫) =
      -(∑ k : Fin 3, ∫ x : T3, ‖longitudinalGradient u k x‖ ^ 2) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 4) hu
  have hu3 := summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu
  have hk (k : Fin 3) : (∫ x : T3, ⟪longitudinalVorticity u x, longitudinalSecond u k x⟫) =
      -(∫ x : T3, ‖longitudinalGradient u k x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using UnitTorusTransportPairing.integral_inner_rate
      (longitudinalVorticity u) (longitudinalGradient u k)
      (longitudinalGradient u k) (longitudinalSecond u k) (coordinateShift k)
      (continuous_longitudinalVorticity u hu1) (continuous_longitudinalGradient u hu1 k)
      (continuous_longitudinalGradient u hu1 k) (continuous_longitudinalSecond u hu1 k)
      (continuous_coordinateShift k) (coordinateShift_zero k)
      (hasDerivAt_longitudinal_shift u hu3 k) (hasDerivAt_longitudinalGradient_shift u hu k)
  have hi (k : Fin 3) : Integrable (fun x : T3 ↦
      ⟪longitudinalVorticity u x, longitudinalSecond u k x⟫) :=
    ((continuous_longitudinalVorticity u hu1).inner
      (continuous_longitudinalSecond u hu1 k)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  simp only [longitudinalLaplacian, deriv_deriv_longitudinal_shift u hu, inner_sum]
  rw [integral_finsetSum _ (fun k _ ↦ hi k)]
  simp only [hk, Finset.sum_neg_distrib]

theorem continuous_inviscidRate (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (inviscidRate u) := by
  have h := continuous_longitudinal (continuous_fullVorticity u hu)
    (continuous_stretchingDerivative u hu)
  simpa only [longitudinal, ← inviscidRate_eq_transport_stretching u hu] using h

theorem continuous_viscousCross (u : FourierVelocity) : Continuous (viscousCross u) := by
  unfold viscousCross diffusionCross
  exact continuous_finsetSum Finset.univ (fun k _ ↦ continuous_finsetSum Finset.univ (fun j _ ↦
    ((EuclideanSpace.proj j).continuous.comp
      (LocalSquaredGapGradient.continuous_fullCurlGradient u k)).smul
        (continuous_velocityJet (indexedDerivativeCoeff id j (fourierCurl u)) k)))

theorem continuous_longitudinalLaplacian (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) : Continuous (longitudinalLaplacian u) := by
  have he : longitudinalLaplacian u = fun x ↦ ∑ k, longitudinalSecond u k x := by
    funext x
    simp only [longitudinalLaplacian, deriv_deriv_longitudinal_shift u hu]
  rw [he]
  exact continuous_finsetSum _ (fun k _ ↦ continuous_longitudinalSecond u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 4) hu) k)

/-- Spatial work of the actual material rate, with ordinary diffusion
and both remaining fluxes explicit. No time-integrated bound is assumed. -/
theorem integral_materialRate_balance (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    (∫ x : T3, ⟪longitudinalVorticity u x,
      materialRate ν u (fun j ↦ realFullField u x j) x⟫) +
        ν * (∑ k : Fin 3, ∫ x : T3, ‖longitudinalGradient u k x‖ ^ 2) =
      -(∫ x : T3, ⟪∑ j, fullVorticity u x j • longitudinalGradient u j x,
          fullStrainOperator u x (fullVorticity u x)⟫) +
        (2 * ν) * (∑ k : Fin 3, ∫ x : T3,
          ⟪∑ j, fullCurlGradient u k x j • longitudinalGradient u j x,
            fullCurlGradient u k x⟫) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 4) hu
  have hu3 := summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu
  have hq := continuous_longitudinalVorticity u hu1
  have hiL : Integrable (fun x : T3 ↦
      ⟪longitudinalVorticity u x, longitudinalLaplacian u x⟫) :=
    (hq.inner (continuous_longitudinalLaplacian u hu)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiI : Integrable (fun x : T3 ↦ ⟪longitudinalVorticity u x, inviscidRate u x⟫) :=
    (hq.inner (continuous_inviscidRate u hu1)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiC : Integrable (fun x : T3 ↦ ⟪longitudinalVorticity u x, viscousCross u x⟫) :=
    (hq.inner (continuous_viscousCross u)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : T3) : materialRate ν u (fun j ↦ realFullField u x j) x =
      ν • longitudinalLaplacian u x + inviscidRate u x - (2 * ν) • viscousCross u x := by
    rw [materialRate_eq ν u hu hd hr, longitudinalLaplacian_eq u hu]
    module
  simp_rw [he, inner_sub_right, inner_add_right, real_inner_smul_right]
  have hsplit := integral_sub ((hiL.const_mul ν).add hiI) (hiC.const_mul (2 * ν))
  simp only [Pi.add_apply] at hsplit
  rw [hsplit,
    integral_add (hiL.const_mul ν) hiI, integral_const_mul, integral_const_mul,
    integral_longitudinal_laplacian u hu, integral_longitudinal_inviscidRate u hu3,
    integral_longitudinal_viscousCross u hu3]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalCurvatureWork
