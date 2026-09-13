import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicGradientFluxTriple
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalViscousFluxFourier

/-!
# The actual inviscid flux as a depleted triple series

Incompressibility removes the outer input frequency from the contraction
with the output frequency. The resulting triple series reconstructs the
same inviscid tensor appearing in the longitudinal energy identity.
The joint cost retains its signed sum with the actual viscous pair series.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalInviscidFluxFourier

open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakeCurlOutputTail PancakeIndexedFourierMoments PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakeHigherDerivativeMoments FullLambVector LongitudinalVorticityTime LongitudinalGradientFlux
open PeriodicGradientFluxSymbol PeriodicGradientFluxProduct PeriodicGradientFluxTriple
open LongitudinalViscousFluxFourier

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def depletedStretchCoeff (u : FourierVelocity) (r : Fin 3) (p : TripleIndex)
    (j : Fin 3) : VelocityCoefficient :=
  (unitTorusDerivativePhase * (p.2.2 r : ℂ) * fourierCurl u p.2.1 r *
    ((tripleFrequency p j : ℂ) / modeSquare (tripleFrequency p) *
      modeDot (p.2.1 + p.2.2) (fourierCurl u p.1))) • u p.2.2

theorem projected_triple_eq_depleted (u : FourierVelocity) (r : Fin 3)
    (p : TripleIndex) (j : Fin 3) :
    projectedCoeff (tripleFrequency p)
      (fun l ↦ tripleCoeff (fourierCurl u) (fourierCurl u) (indexedDerivativeCoeff id r u) r l p) j =
      depletedStretchCoeff u r p j := by
  change projectedCoeff (p.1 + (p.2.1 + p.2.2))
    (fun l ↦ fourierCurl u p.1 l •
      (fourierCurl u p.2.1 r • indexedDerivativeCoeff id r u p.2.2)) j = _
  rw [projectedCoeff_rankOne_of_transverse _ _ _ _ (fourierCurl_transverse p.1 u)]
  simp only [indexedDerivativeCoeff, id_eq, smul_smul, depletedStretchCoeff, tripleFrequency]
  congr 1
  ring

theorem summable_depletedTripleModes (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (r : Fin 3) :
    Summable (fun p : TripleIndex ↦
      toTensorL2 (fun j ↦ realMode (tripleFrequency p) (depletedStretchCoeff u r p j))) := by
  have hui : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  have hw : Summable (fun n ↦ ‖fourierCurl u n‖) := summable_norm_curlCoefficients id u hui
  have hd := summable_norm_derivativeCoefficients id u hui r
  have h := summable_indexedProjectedModes tripleFrequency
    (tripleCoeff (fourierCurl u) (fourierCurl u) (indexedDerivativeCoeff id r u) r)
    (summable_norm_tripleCoeff _ _ _ hw hw hd r)
  simpa only [projected_triple_eq_depleted] using h

theorem tripleField_derivative_apply (u : FourierVelocity) (r j : Fin 3) (x : T3) :
    tripleField (fourierCurl u) (fourierCurl u) (indexedDerivativeCoeff id r u) r j x =
      vorticityField u x j • (vorticityField u x r • velocityJet u r x) := rfl

theorem inviscid_fluxField_eq (u : FourierVelocity) :
    fluxField 0 u = -∑ r, tripleField (fourierCurl u) (fourierCurl u) (indexedDerivativeCoeff id r u) r := by
  funext j
  ext x
  simp only [fluxField, ContinuousMap.coe_mk, mul_zero, zero_smul, add_zero,
    Pi.neg_apply, Finset.sum_apply, ContinuousMap.neg_apply, ContinuousMap.sum_apply,
    tripleField_derivative_apply, Finset.smul_sum, Finset.sum_const_zero]

theorem projectedFlux_inviscid_eq_tripleSeries (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ n, u (-n) = coefficientConjugate (u n)) :
    projectedFlux 0 u = -∑ r : Fin 3, ∑' p : TripleIndex,
      toTensorL2 (fun j ↦ realMode (tripleFrequency p) (depletedStretchCoeff u r p j)) := by
  have hui : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  have hw : Summable (fun n ↦ ‖fourierCurl u n‖) := summable_norm_curlCoefficients id u hui
  change ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))) (fluxField 0 u) = _
  rw [inviscid_fluxField_eq, map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  change gradientProjection (toTensorL2 (tripleField _ _ _ r)) = _
  rw [gradientProjection_tripleField _ _ _ hw hw (summable_norm_derivativeCoefficients id u hui r)
    (fourierCurl_real u hr) (fourierCurl_real u hr)]
  exact tsum_congr (fun p ↦ by simp only [projected_triple_eq_depleted])

def jointSeriesCost (ν : ℝ) (u : FourierVelocity) : ℝ :=
  ‖-(∑ r : Fin 3, ∑' p : TripleIndex,
      toTensorL2 (fun j ↦ realMode (tripleFrequency p) (depletedStretchCoeff u r p j))) +
    (2 * ν) • ∑ r : Fin 3, ∑' p : Wavevector × Wavevector,
      toTensorL2 (fun j ↦ realMode (p.1 + p.2) (depletedPairCoeff u r p j))‖ ^ 2

theorem projectedFluxSquare_eq_jointSeriesCost (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ n, u (-n) = coefficientConjugate (u n)) :
    projectedFluxSquare ν u = jointSeriesCost ν u := by
  rw [projectedFluxSquare_eq_pairSeries ν u hu hr,
    projectedFlux_inviscid_eq_tripleSeries u (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) hr]
  rfl

def combinedStretchCoeff (u : FourierVelocity) (p : TripleIndex) (j : Fin 3) : VelocityCoefficient :=
  (unitTorusDerivativePhase * modeDot p.2.2 (fourierCurl u p.2.1) *
    ((tripleFrequency p j : ℂ) / modeSquare (tripleFrequency p) *
      modeDot (p.2.1 + p.2.2) (fourierCurl u p.1))) • u p.2.2

theorem sum_depletedStretchCoeff (u : FourierVelocity) (p : TripleIndex) (j : Fin 3) :
    (∑ r, depletedStretchCoeff u r p j) = combinedStretchCoeff u p j := by
  have hd : modeDot p.2.2 (fourierCurl u p.2.1) =
      ∑ r, (p.2.2 r : ℂ) * fourierCurl u p.2.1 r := rfl
  simp only [depletedStretchCoeff, combinedStretchCoeff, hd, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  ring

theorem projectedFlux_inviscid_eq_combinedTripleSeries (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ n, u (-n) = coefficientConjugate (u n)) :
    projectedFlux 0 u = -∑' p : TripleIndex,
      toTensorL2 (fun j ↦ realMode (tripleFrequency p) (combinedStretchCoeff u p j)) := by
  rw [projectedFlux_inviscid_eq_tripleSeries u hu hr]
  congr 1
  rw [← Summable.tsum_finsetSum (fun r _ ↦ summable_depletedTripleModes u hu r)]
  apply tsum_congr
  intro p
  simp only [toTensorL2, ← map_sum]
  congr 1
  funext j
  change (∑ r, realModeCLM (tripleFrequency p) (depletedStretchCoeff u r p j)) =
    realModeCLM (tripleFrequency p) (combinedStretchCoeff u p j)
  rw [← map_sum, sum_depletedStretchCoeff]

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalInviscidFluxFourier
