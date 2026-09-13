import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialTransportLaplacian
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePressurePoisson

/-!
# Double curl with the ordinary gradient-divergence term retained

The identity applies to arbitrary sufficiently summable Fourier fields,
including the nonlinear advection field, which is not divergence-free.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpatialCurlCurl

open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeInfiniteSpatialLaplacian PancakeSpatialGradientDifferentiation
open PancakeFourierTranslationCurve PancakeInfiniteSpatialPressure PancakeLocalProjectedEquation
open PancakeGalerkinKineticEnergy LocalWeightedCurlCancellation

local notation "T3" => UnitAddTorus (Fin 3)

theorem coordinateDerivative_spatialCurl (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j : Fin 3) (x : T3) :
    coordinateDerivative (spatialCurl (fullFourierField id u)) j x =
      ![coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 1 y) j x 2 -
          coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 2 y) j x 1,
        coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 2 y) j x 0 -
          coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 0 y) j x 2,
        coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 0 y) j x 1 -
          coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 1 y) j x 0] := by
  have h (k : Fin 3) := hasDerivAt_coordinateDerivative_shift_zero u hu k j x
  have hd : HasDerivAt (fun t ↦ spatialCurl (fullFourierField id u) (x + coordinateShift j t))
      ![coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 1 y) j x 2 -
          coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 2 y) j x 1,
        coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 2 y) j x 0 -
          coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 0 y) j x 2,
        coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 0 y) j x 1 -
          coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) 1 y) j x 0] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ((hasDerivAt_pi.mp (h 1)) 2).fun_sub ((hasDerivAt_pi.mp (h 2)) 1)
    · exact ((hasDerivAt_pi.mp (h 2)) 0).fun_sub ((hasDerivAt_pi.mp (h 0)) 2)
    · exact ((hasDerivAt_pi.mp (h 0)) 1).fun_sub ((hasDerivAt_pi.mp (h 1)) 0)
  exact hd.deriv

theorem gradient_divergence (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) (i : Fin 3) :
    spatialGradient (spatialDivergence (fullFourierField id u)) x i =
      ∑ j : Fin 3, coordinateDerivative (fun y ↦ coordinateDerivative (fullFourierField id u) j y) i x j := by
  have h (j : Fin 3) := (hasDerivAt_pi.mp (hasDerivAt_coordinateDerivative_shift_zero u hu j i x)) j
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ h j)).deriv

theorem curl_curl (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (x : T3) :
    spatialCurl (spatialCurl (fullFourierField id u)) x =
      spatialGradient (spatialDivergence (fullFourierField id u)) x -
        spatialLaplacian (fullFourierField id u) x := by
  have h01 := coordinateDerivative2_commute u hu 0 1 x
  have h02 := coordinateDerivative2_commute u hu 0 2 x
  have h12 := coordinateDerivative2_commute u hu 1 2 x
  ext i
  fin_cases i <;>
    simp [spatialCurl, coordinateDerivative_spatialCurl u hu, gradient_divergence u hu,
      spatialLaplacian, Fin.sum_univ_three, h01, h02, h12] <;> ring

theorem fullFourierField_doubleCurl (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) :
    fullFourierField id (fourierCurl (fourierCurl u)) x =
      spatialGradient (spatialDivergence (fullFourierField id u)) x -
        spatialLaplacian (fullFourierField id u) x := by
  have h := curl_curl u hu x
  rw [spatialCurl_velocity u (summable_firstMoment_of_second u hu),
    spatialCurl_velocity _ (summable_fourierMoment_curl 1 u hu)] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.SpatialCurlCurl
