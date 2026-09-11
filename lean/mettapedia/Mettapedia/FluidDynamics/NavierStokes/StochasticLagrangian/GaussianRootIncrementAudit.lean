import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootIncrementBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicFourierProductConcentration

/-! Collision, diagonal, concentration, and actual-envelope regression checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementAudit

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail LocalLowDiffusionBudget
open GaussianRootIncrementBudget GaussianRootTwoPointIntegral PeriodicFourierProductConcentration
open Mettapedia.Analysis.EuclideanOperatorCoordinates PancakeSpectralProjectorRegularity
open PancakeBilinearPeriodization (firstTorusDisplacement secondTorusDisplacement)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- No spectral separation assumption is imposed, even for coincident strain. -/
example (A : SymmetricStrain) (w v : R3) :
    ‖coordinates (SquaredGapTiltWeight.weightedProjector 1 A w) -
      coordinates (SquaredGapTiltWeight.weightedProjector 1 A v)‖ ^ 2 ≤ 6 * ‖w - v‖ ^ 2 := by
  simpa using SquaredGapTiltWeight.norm_coordinates_weightedProjector_sub_sq_le 1 (by norm_num) A A w v

example (gamma : ℝ) (A B : SymmetricStrain) :
    coordinates (SquaredGapTiltWeight.weightedProjector gamma A 0) -
      coordinates (SquaredGapTiltWeight.weightedProjector gamma B 0) = 0 := by
  simp [SquaredGapTiltWeight.weightedProjector]

/-- Coincident spatial inputs have no field-increment cost. -/
example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau epsilon : ℝ) (y : T3) :
    incrementMoment gamma chi modes u centers tau epsilon y y =
      4 * epsilon ^ 2 + 3 * tau * Real.log (centers.card : ℝ) := by
  simp [incrementMoment]

example (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu0 : ∀ x : T3, fullVorticity u x = 0)
    (centers : Finset T3) (tau epsilon : ℝ) (j : Fin 3) (y z : T3) :
    incrementBudget gamma chi modes u centers tau epsilon j y z = 0 := by
  simp [incrementBudget, hu0]

/-- A high-frequency packet already violates any proposed universal constant. -/
example : ∃ n : ℕ,
    100 * (∫ x : T3, ‖packet n x‖ ^ 2) ^ 2 < ∫ x : T3, ‖packet n x‖ ^ 4 :=
  exists_packet_productEnergy_gt 100

/-- Fixing the square energy at one does not prevent concentration. -/
example : ∃ f : C(T3, ℂ), (∫ x : T3, f x) = 0 ∧
    (∫ x : T3, ‖f x‖ ^ 2) = 1 ∧ 100 < ∫ x : T3, ‖f x‖ ^ 4 :=
  exists_unit_energy_fourthEnergy_gt 100

/-- The new budget is applied to constructed centers and an actual common
channel envelope, not independent assumed kernel bounds. -/
example (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (epsilon : ℝ) (he : 0 < epsilon) (tau : ℝ) (htau : 0 < tau)
    (N : ℝ) (hN : 0 < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    let hu2 := PancakeHigherDerivativeMoments.summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
    ∃ (centers : Finset T3) (hc : centers.Nonempty) (M : T6 → ℝ), Integrable M ∧
      ∀ j : Fin 3,
        normalizedChannelEnergy gamma hg chi modes u hu2 centers hc tau N hN t (.first j) ≤
          (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
            incrementBudget gamma chi modes u centers tau epsilon j
              (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) ∧
        normalizedChannelEnergy gamma hg chi modes u hu2 centers hc tau N hN t (.second j) ≤
          (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
            incrementBudget gamma chi modes u centers tau epsilon j
              (x - secondTorusDisplacement q) (x - firstTorusDisplacement q) := by
  obtain ⟨centers, hc, hcover, _⟩ := exists_projector_increment_cover gamma hg chi modes u
    (PancakeHigherDerivativeMoments.summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu) epsilon he
  obtain ⟨C, _, M, hb⟩ := PressureCoherentRelativeMoment.exists_uniform_periodic_envelope 2
  obtain ⟨hn, _, hi, _, hk, _, _⟩ := hb N hN t ht
  refine ⟨centers, hc, M N hN t, hi, fun j ↦ ?_⟩
  exact channel_sum_energy_le_incrementBudget gamma hg chi modes u hu centers hc tau htau epsilon hcover
    N hN t j (M N hN t) hi hn (hk.mono (fun _ h e he ↦ h e he .undifferentiated))

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementAudit

#print axioms Mettapedia.Analysis.RootPartitionEnergy.integrable_twoPointDerivativeCost_of_continuous
#print axioms Mettapedia.Analysis.RootPartitionEnergy.integrable_twoPointDerivativeCost
#print axioms Mettapedia.Analysis.FiniteFourierConcentration.card_intervalModes
#print axioms Mettapedia.Analysis.FiniteFourierConcentration.scalarEnergy_intervalModes
#print axioms Mettapedia.Analysis.FiniteFourierConcentration.norm_intervalConvolution_ge
#print axioms Mettapedia.Analysis.FiniteFourierConcentration.scalarEnergy_intervalConvolution_ge
#print axioms Mettapedia.Analysis.FiniteFourierConcentration.exists_intervalConvolution_energy_gt
#print axioms Mettapedia.FluidDynamics.NavierStokes.SquaredGapTiltWeight.norm_coordinates_weightedProjector_sub_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementBudget.twoPointDistanceMoment_le_incrementMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementBudget.continuous_incrementMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementBudget.twoPointBudget_le_incrementBudget
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementBudget.integrable_incrementBudget
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementBudget.integral_twoPointBudget_le_incrementBudget
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementBudget.channel_sum_energy_le_incrementBudget
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootIncrementBudget.exists_projector_increment_cover
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.frequencyAxis_injective
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.continuous_packet
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.norm_packet
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.packet_eq_sum
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.packet_frequency_bounds
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.integral_packet
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.integral_norm_packet_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.integral_norm_packet_four_ge
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.exists_packet_productEnergy_gt
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.not_exists_uniform_productEnergy_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration.exists_unit_energy_fourthEnergy_gt
