import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteRealCurl
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFullNonlinearConsistency

/-!
# The constructed full interaction is the physical curl nonlinearity

For conjugate-symmetric coefficients with summable second absolute
moment, the full interaction series equals curl(U cross curl(U)), with
both curls defined by actual derivatives of the real field U. The
previous joint truncation bound therefore compares with this physical
expression. No evolution or global moment bound is assumed proved here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFullAnalyticNonlinearity

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeInfiniteSpatialCurl
open PancakeInfiniteFourierProduct PancakeInfiniteRealCurl PancakeCurlOutputTail
open PancakeInfinitePairReconstruction PancakeFullNonlinearConsistency PancakeGalerkinKineticEnergy
open PancakeDyadicDirectionEvolution PancakeBlockReality PancakeInteractionTruncationTail
open PancakeZeroSafeInteractionTail PancakeDiscardedNonlinearLimit

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def physicalFullNonlinearity (u : FourierVelocity) : T3 → R3 :=
  realSpatialCurl (fun x ↦ realCross (realFullField u x) (realSpatialCurl (realFullField u) x))

theorem realPart_fullPairField (F : Wavevector × Wavevector → VelocityCoefficient)
    (hF : Summable (fun p ↦ ‖F p‖)) (x : T3) :
    complexRealPartEuclideanCLM (fullFourierField pairFrequency F x) = infinitePairField F x := by
  rw [fullFourierField_apply pairFrequency F hF]
  exact complexRealPartEuclideanCLM.map_tsum (summable_pointwise_modes pairFrequency F hF x)

theorem fullCurlNonlinearity_eq_complexCurl (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) :
    fullCurlNonlinearity u x = complexRealPartEuclideanCLM
      (spatialCurl (fun y ↦ coefficientCross (fullFourierField id u y)
        (spatialCurl (fullFourierField id u) y)) x) := by
  have hu1 := summable_firstMoment_of_second u hu
  have hw1 := summable_firstMoment_curl u hu
  rw [spatialCurl_velocity u hu1, spatialCurl_cross_fullFourierField u (fourierCurl u) hu1 hw1]
  exact (realPart_fullPairField (curlPair u (fourierCurl u))
    (summable_norm_curlCoefficients pairFrequency (crossPair u (fourierCurl u))
      (summable_firstMoment_crossPair u (fourierCurl u) hu1 hw1)) x).symm

theorem physicalFullNonlinearity_eq_fullCurlNonlinearity (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) :
    physicalFullNonlinearity u = fullCurlNonlinearity u := by
  have hu1 := summable_firstMoment_of_second u hu
  have hw1 := summable_firstMoment_curl u hu
  have hp := summable_firstMoment_crossPair u (fourierCurl u) hu1 hw1
  have he : (fun x ↦ realCross (realFullField u x) (realFullField (fourierCurl u) x)) =
      fun x ↦ complexRealPartEuclideanCLM
        (fullFourierField pairFrequency (crossPair u (fourierCurl u)) x) :=
    funext (realCross_fullField u (fourierCurl u) hu1 hw1 hr)
  unfold physicalFullNonlinearity
  rw [realSpatialCurl_realFullField u hu1, he,
    realSpatialCurl_realPart _ (differentiableAt_fullFourierField_shift _ _ hp),
    spatialCurl_fullFourierField _ _ hp]
  funext x
  exact realPart_fullPairField _ (summable_norm_curlCoefficients _ _ hp) x

theorem norm_physicalNonlinearity_sub_retained_le_tail (g : Wavevector → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hSum : Summable g) (M : Finset Wavevector) (u : FourierVelocity)
    (hzero : u 0 = 0) (hu : ∀ k ∈ M, modeDot k (u k) = 0)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hbound : ∀ k, fourierMoment 2 u k ≤ g k) (x : T3) :
    ‖physicalFullNonlinearity u x - retainedCurlNonlinearity M u x‖ ≤
      interactionTail (nonzeroMajorant (velocityCurlMajorant g)) M := by
  have hm : Summable (fourierMoment 2 u) :=
    Summable.of_nonneg_of_le (fourierMoment_nonneg _ _) hbound hSum
  rw [physicalFullNonlinearity_eq_fullCurlNonlinearity u hm hr]
  exact norm_fullNonlinearError_le_tail g hg hSum M u hzero hu hbound x

end Mettapedia.FluidDynamics.NavierStokes.PancakeFullAnalyticNonlinearity
