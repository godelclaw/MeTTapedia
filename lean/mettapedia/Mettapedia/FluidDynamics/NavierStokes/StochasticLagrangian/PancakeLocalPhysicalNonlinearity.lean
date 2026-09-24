import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherLocalVelocity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalSpatialVelocity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFullAnalyticNonlinearity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFullNonlinearTimeLimit

/-!
# Physical curl and alignment consistency on a constructed local solution

The local higher-order construction supplies the previously conditional
common second-moment envelope. The derivative-defined physical nonlinearity
and its vanishing time-integrated truncation pairing therefore apply to an
actual infinite velocity evolution from the initial physical field.

This is local consistency, not an all-time misalignment-strain budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalPhysicalNonlinearity

open MeasureTheory
open scoped BigOperators ComplexConjugate RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeArbitraryDataBlocks
open PancakeContinuousCoordinateJet PancakeFrequencyProjectorCommutator
open PancakeHigherLocalVelocity PancakeHigherSobolevVelocityRate
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeInfiniteSpatialCurl
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeInfiniteFourierProduct
open PancakeFullAnalyticNonlinearity PancakeFullNonlinearConsistency PancakeFullNonlinearTimeLimit
open PancakePhysicalWeightedTransport PancakeDyadicDirectionEvolution PancakeGalerkinKineticEnergy
open PancakePhysicalSpectralDefect
open PancakeInfiniteRealCurl

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem summable_secondMoment_of_sixthEnergy (u : FourierVelocity) (B : ℝ)
    (hB : ∀ F : Finset Wavevector, velocityEnergy 6 F u ≤ B) :
    Summable (fourierMoment 2 u) :=
  (summable_latticeDecayWeight.mul_left (Real.sqrt B)).of_nonneg_of_le
    (fourierMoment_nonneg 2 u) (orderMoment_le_latticeEnvelope 2 u B hB)

theorem spatialField_coordinateDerivative {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ)
    (hE : ∀ F : Finset Wavevector, velocityEnergy 6 F (s.coefficients t) ≤ B)
    (j : Fin 3) (x : T3) :
    coordinateDerivative (spatialField s t) j x =
      fullFourierField id (indexedDerivativeCoeff id j (s.coefficients t)) x := by
  apply coordinateDerivative_fullFourierField
  simpa only [indexedFirstMoment_id] using
    summable_firstMoment_of_second _ (summable_secondMoment_of_sixthEnergy _ B hE)

theorem spatialField_spatialCurl {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ)
    (hE : ∀ F : Finset Wavevector, velocityEnergy 6 F (s.coefficients t) ≤ B) :
    spatialCurl (spatialField s t) = fullFourierField id (fourierCurl (s.coefficients t)) :=
  spatialCurl_velocity _ (summable_firstMoment_of_second _
    (summable_secondMoment_of_sixthEnergy _ B hE))

theorem local_physicalNonlinearity_eq {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ)
    (hE : ∀ F : Finset Wavevector, velocityEnergy 6 F (s.coefficients t) ≤ B) :
    physicalFullNonlinearity (s.coefficients t) = fullCurlNonlinearity (s.coefficients t) :=
  physicalFullNonlinearity_eq_fullCurlNonlinearity _
    (summable_secondMoment_of_sixthEnergy _ B hE) (s.reality t)

/-- The error uses actual real spatial derivatives on its full-field side. -/
def physicalErrorPairingMass (chi : Wavevector → ℂ) (M : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  ∫ x : T3, |⟪physicalGapWeight chi M u 0 x (spatialVorticity M u x),
    physicalFullNonlinearity u x - retainedCurlNonlinearity M u x⟫|

theorem physicalErrorPairingMass_eq (chi : Wavevector → ℂ) (M : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    physicalErrorPairingMass chi M u = fullErrorPairingMass chi M u := by
  unfold physicalErrorPairingMass fullErrorPairingMass
  rw [physicalFullNonlinearity_eq_fullCurlNonlinearity u hu hr]
  rfl

/-- For an actual evolution constructed from order-eight physical initial
jets, the absolute alignment pairing of the full nonlinear truncation error
tends to zero on its common positive interval, uniformly over bounded filters. -/
theorem exists_physical_local_alignment_consistency (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 8 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
        (∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ F, velocityEnergy 6 F (s.coefficients t) ≤ B) ∧
        ∀ C ≥ (0 : ℝ), ∀ ε > (0 : ℝ), ∃ core : Finset Wavevector,
          ∀ M : Finset Wavevector, core ⊆ M → ∀ chi : Wavevector → ℂ,
            (∀ k, ‖chi k‖ ≤ C) →
            (∫ t in (0 : ℝ)..T, physicalErrorPairingMass chi (M.erase 0) (s.coefficients t)) < ε := by
  obtain ⟨T, hT, B, hB, s, hs⟩ :=
    exists_physical_higher_localVelocity 6 (by omega) nu hnu f hf hr hd hzero
  let g := fun k ↦ Real.sqrt B * latticeDecayWeight k
  have hg : ∀ k, 0 ≤ g k :=
    fun k ↦ mul_nonneg (Real.sqrt_nonneg B) (latticeDecayWeight_pos k).le
  have hSum : Summable g := summable_latticeDecayWeight.mul_left _
  have hb : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 2 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ orderMoment_le_latticeEnvelope 2 _ B (hs t ht) k
  refine ⟨T, hT, B, hB, s, hs, fun C hC ε hε ↦ ?_⟩
  obtain ⟨core, hc⟩ := exists_uniform_integral_fullError_erase_zero_lt g hg hSum C T hC hT.le ε hε
  refine ⟨core, fun M hM chi hchi ↦ ?_⟩
  have he := hc M hM s.coefficients chi hchi (fun q i ↦ (s.continuous q i).continuousOn)
    (fun t _ ↦ s.zero t) (fun t _ q _ ↦ s.transverse t q) hb
  have hi :
      (∫ t in (0 : ℝ)..T, physicalErrorPairingMass chi (M.erase 0) (s.coefficients t)) =
      ∫ t in (0 : ℝ)..T, fullErrorPairingMass chi (M.erase 0) (s.coefficients t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := by simpa only [Set.uIcc_of_le hT.le] using ht
    exact physicalErrorPairingMass_eq chi (M.erase 0) _
      (summable_secondMoment_of_sixthEnergy _ B (hs t ht')) (s.reality t)
  exact hi ▸ he

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalPhysicalNonlinearity
