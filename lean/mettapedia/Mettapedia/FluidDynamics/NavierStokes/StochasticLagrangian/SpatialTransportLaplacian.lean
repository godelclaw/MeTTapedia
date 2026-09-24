import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityCenterEvolution

/-!
# The ordinary Laplacian product rule for material transport

All differentiated fields are reconstructed from absolutely summable Fourier
moments. The two cross terms in the Laplacian of transport are retained; no
commutation of material motion with spatial diffusion is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpatialTransportLaplacian

open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeInfiniteSpatialLaplacian PancakeSpatialGradientDifferentiation
open PancakeSpatialViscousDifferentiation PancakeFourierTranslationCurve PancakeHaarTransportRate

local notation "T3" => UnitAddTorus (Fin 3)

theorem hasDerivAt_transport_shift (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 2 v))
    (j : Fin 3) (x : T3) :
    HasDerivAt (fun h ↦ spatialTransport (fullFourierField id u) (fullFourierField id v)
      (x + coordinateShift j h))
      (spatialTransport (fullFourierField id (indexedDerivativeCoeff id j u)) (fullFourierField id v) x +
        spatialTransport (fullFourierField id u) (fullFourierField id (indexedDerivativeCoeff id j v)) x) 0 := by
  have hU := hasDerivAt_fullFourierField_shift_zero u hu j x
  have hm := summable_firstMoment_of_second v hv
  have h (m : Fin 3) := ((hasDerivAt_pi.mp hU) m).smul
    (hasDerivAt_coordinateDerivative_shift_zero v hv m j x)
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun m _ ↦ h m)
  simp only [Pi.smul_apply', coordinateShift_zero, add_zero,
    coordinateDerivative2_commute v hv j, Finset.sum_add_distrib] at hh
  rw [coordinateDerivative_fullFourierField_eq v hm j] at hh
  simp only [coordinateDerivative_fullFourierField id u
    (by simpa only [indexedFirstMoment_id] using hu)] at hh
  simpa only [spatialTransport, add_comm] using hh

theorem coordinateDerivative_transport (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 2 v))
    (j : Fin 3) (x : T3) :
    coordinateDerivative (spatialTransport (fullFourierField id u) (fullFourierField id v)) j x =
      spatialTransport (fullFourierField id (indexedDerivativeCoeff id j u)) (fullFourierField id v) x +
        spatialTransport (fullFourierField id u) (fullFourierField id (indexedDerivativeCoeff id j v)) x :=
  (hasDerivAt_transport_shift u v hu hv j x).deriv

theorem coordinateDerivative2_transport (u v : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hv : Summable (fourierMoment 3 v))
    (j : Fin 3) (x : T3) :
    coordinateDerivative (fun y ↦
      coordinateDerivative (spatialTransport (fullFourierField id u) (fullFourierField id v)) j y) j x =
      spatialTransport (fullFourierField id (indexedDerivativeCoeff id j (indexedDerivativeCoeff id j u)))
          (fullFourierField id v) x +
        2 • spatialTransport (fullFourierField id (indexedDerivativeCoeff id j u))
          (fullFourierField id (indexedDerivativeCoeff id j v)) x +
        spatialTransport (fullFourierField id u)
          (fullFourierField id (indexedDerivativeCoeff id j (indexedDerivativeCoeff id j v))) x := by
  have hu1 := summable_firstMoment_of_second u hu
  have hv2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hv
  have h1 := hasDerivAt_transport_shift (indexedDerivativeCoeff id j u) v
    (summable_fourierMoment_derivative 1 u hu j) hv2 j x
  have h2 := hasDerivAt_transport_shift u (indexedDerivativeCoeff id j v) hu1
    (summable_fourierMoment_derivative 2 v hv j) j x
  have he := (h1.fun_add h2).deriv
  simp only [coordinateDerivative_transport u v hu1 hv2]
  exact he.trans (by simp only [two_smul]; abel)

/-- Summing transport in its undifferentiated argument needs no regularity
of the transported field. -/
theorem sum_transport_left {ι : Type*} (F : Finset ι)
    (f : ι → T3 → VelocityCoefficient) (v : T3 → VelocityCoefficient) (x : T3) :
    (∑ i ∈ F, spatialTransport (f i) v x) = spatialTransport (fun y ↦ ∑ i ∈ F, f i y) v x := by
  simp only [spatialTransport, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- Finite sums in the differentiated argument are justified by actual
translation derivatives of every summand. -/
theorem sum_transport_right {ι : Type*} (F : Finset ι) (u : T3 → VelocityCoefficient)
    (v : ι → FourierVelocity) (hv : ∀ i ∈ F, Summable (fourierMoment 1 (v i))) (x : T3) :
    (∑ i ∈ F, spatialTransport u (fullFourierField id (v i)) x) =
      spatialTransport u (fun y ↦ ∑ i ∈ F, fullFourierField id (v i) y) x := by
  have hd (j : Fin 3) := (HasDerivAt.fun_sum (u := F)
    (fun i hi ↦ hasDerivAt_fullFourierField_shift_zero (v i) (hv i hi) j x)).deriv
  change ∀ j : Fin 3,
    coordinateDerivative (fun y ↦ ∑ i ∈ F, fullFourierField id (v i) y) j x =
      ∑ i ∈ F, coordinateDerivative (fullFourierField id (v i)) j x at hd
  simp only [spatialTransport, hd, Finset.smul_sum]
  exact Finset.sum_comm

theorem sum_secondDerivativeField (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    (fun x : T3 ↦ ∑ j : Fin 3,
      fullFourierField id (indexedDerivativeCoeff id j (indexedDerivativeCoeff id j u)) x) =
      spatialLaplacian (fullFourierField id u) := by
  funext x
  simp only [spatialLaplacian, coordinateDerivative2_fullFourierField u hu]

/-- The ordinary product rule, including the full cross-derivative source. -/
theorem laplacian_transport (u v : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hv : Summable (fourierMoment 3 v)) (x : T3) :
    spatialLaplacian (spatialTransport (fullFourierField id u) (fullFourierField id v)) x =
      spatialTransport (spatialLaplacian (fullFourierField id u)) (fullFourierField id v) x +
        2 • (∑ j : Fin 3, spatialTransport (fullFourierField id (indexedDerivativeCoeff id j u))
          (fullFourierField id (indexedDerivativeCoeff id j v)) x) +
        spatialTransport (fullFourierField id u) (spatialLaplacian (fullFourierField id v)) x := by
  simp only [spatialLaplacian, coordinateDerivative2_transport u v hu hv,
    Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [sum_transport_left, sum_transport_right]
  · rw [sum_secondDerivativeField u hu, sum_secondDerivativeField v
      (summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hv)]
  · intro j _
    exact summable_fourierMoment_derivative 1 _ (summable_fourierMoment_derivative 2 v hv j) j

end Mettapedia.FluidDynamics.NavierStokes.SpatialTransportLaplacian
