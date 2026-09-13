import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicGradientFluxProduct

/-!
# The actual viscous flux as a depleted infinite pair series

The vorticity and all coordinate derivatives come from the same velocity.
The exact gradient-active series retains the cross-frequency factor
`l dot omegaHat(k)`. The full flux identity keeps inviscid and viscous
contributions together; no separate norm budget is asserted.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalViscousFluxFourier

open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeInfiniteFourierDerivative
open PancakeCurlOutputTail LocalSpatialVorticityJets PancakeInfiniteSpatialCurl
open PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakeIndexedFourierMoments LocalWeightedCurlCancellation PancakeInfiniteFourierProduct
open PeriodicGradientFluxSymbol PeriodicGradientFluxProduct LongitudinalGradientFlux

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def viscousFluxField (u : FourierVelocity) : Fin 3 → C(T3, R3) :=
  ∑ r, curlGradientProduct u r

theorem viscousFluxField_apply (u : FourierVelocity) (j : Fin 3) (x : T3) :
    viscousFluxField u j x = ∑ r, fullCurlGradient u r x j • fullCurlGradient u r x := by
  simp only [viscousFluxField, Finset.sum_apply, ContinuousMap.sum_apply, curlGradientProduct_apply]

def depletedPairCoeff (u : FourierVelocity) (r : Fin 3) (p : Wavevector × Wavevector)
    (j : Fin 3) : VelocityCoefficient :=
  (unitTorusDerivativePhase ^ 2 * (p.1 r : ℂ) * (p.2 r : ℂ) *
    (((p.1 + p.2) j : ℂ) / modeSquare (p.1 + p.2) * modeDot p.2 (fourierCurl u p.1))) • fourierCurl u p.2

theorem projected_pair_eq_depleted (u : FourierVelocity) (r : Fin 3)
    (p : Wavevector × Wavevector) (j : Fin 3) :
    projectedCoeff (p.1 + p.2) (fun l ↦ pairCoeff
      (indexedDerivativeCoeff id r (fourierCurl u)) (indexedDerivativeCoeff id r (fourierCurl u)) l p) j =
      depletedPairCoeff u r p j := by
  have ht : modeDot p.1 (indexedDerivativeCoeff id r (fourierCurl u) p.1) = 0 := by
    rw [indexedDerivativeCoeff, modeDot_smul, fourierCurl_transverse, mul_zero]
  simp only [pairCoeff]
  rw [projectedCoeff_rankOne_of_transverse _ _ _ _ ht]
  simp only [indexedDerivativeCoeff, id_eq, modeDot_smul, smul_smul, depletedPairCoeff]
  congr 1
  ring

theorem summable_depletedPairModes (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (r : Fin 3) :
    Summable (fun p : Wavevector × Wavevector ↦
      toTensorL2 (fun j ↦ realMode (p.1 + p.2) (depletedPairCoeff u r p j))) := by
  have hw : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_curl 1 u hu
  have hd := summable_norm_derivativeCoefficients id (fourierCurl u) hw r
  have h := summable_indexedProjectedModes pairFrequency
    (pairCoeff (indexedDerivativeCoeff id r (fourierCurl u)) (indexedDerivativeCoeff id r (fourierCurl u)))
    (summable_norm_pairCoeff _ _ hd hd)
  simpa only [pairFrequency, projected_pair_eq_depleted] using h

/-- No finite-mode truncation occurs: the product Fourier moments supply
the absolutely convergent physical products and the convergent `L²` image. -/
theorem gradientProjection_viscousFluxField (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ n, u (-n) = coefficientConjugate (u n)) :
    gradientProjection (toTensorL2 (viscousFluxField u)) =
      ∑ r : Fin 3, ∑' p : Wavevector × Wavevector,
        toTensorL2 (fun j ↦ realMode (p.1 + p.2) (depletedPairCoeff u r p j)) := by
  change ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))) (∑ r, curlGradientProduct u r) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  change gradientProjection (toTensorL2 (curlGradientProduct u r)) = _
  rw [gradientProjection_curlGradientProduct u hu hr]
  exact tsum_congr (fun p ↦ by simp only [projected_pair_eq_depleted])

theorem fluxField_eq_inviscid_add_viscous (ν : ℝ) (u : FourierVelocity) :
    fluxField ν u = fluxField 0 u + (2 * ν) • viscousFluxField u := by
  funext j
  ext x
  simp only [Pi.add_apply, Pi.smul_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    viscousFluxField_apply, fluxField, ContinuousMap.coe_mk, mul_zero, zero_smul, add_zero]

theorem projectedFlux_eq_inviscid_add_viscous (ν : ℝ) (u : FourierVelocity) :
    projectedFlux ν u = projectedFlux 0 u +
      (2 * ν) • gradientProjection (toTensorL2 (viscousFluxField u)) := by
  change ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))) (fluxField ν u) = _
  rw [fluxField_eq_inviscid_add_viscous, map_add, map_smul]
  rfl

/-- The exact cost in the longitudinal time inequality. The norm remains
outside the sum of inviscid and viscous contributions. -/
theorem projectedFluxSquare_eq_pairSeries (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ n, u (-n) = coefficientConjugate (u n)) :
    projectedFluxSquare ν u =
      ‖projectedFlux 0 u + (2 * ν) • ∑ r : Fin 3, ∑' p : Wavevector × Wavevector,
        toTensorL2 (fun j ↦ realMode (p.1 + p.2) (depletedPairCoeff u r p j))‖ ^ 2 := by
  rw [projectedFluxSquare, projectedFlux_eq_inviscid_add_viscous,
    gradientProjection_viscousFluxField u hu hr]

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalViscousFluxFourier
