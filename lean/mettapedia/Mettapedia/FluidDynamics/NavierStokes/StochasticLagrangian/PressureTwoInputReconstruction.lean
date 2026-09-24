import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTwoInputPhysical
import Mettapedia.Analysis.FiniteCharacterConvolution

/-!
# The exact spatial weight of two-input pressure localization

Two cutoff factors on the output reconstruct to their pointwise product.
In particular, using the same cutoff twice gives its fourth power in energy,
not the quadratic weight of a one-cutoff partition. This distinction is
independent of the pressure estimates and persists even for constant cutoffs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputReconstruction

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeFiniteFourierLocalization PancakeFrequencyProjectorCommutator
open PancakePeriodicCoherentSplit PancakeMisalignmentEnergyBridge PancakePressureAnisotropyBudget
open PancakeViscousMisalignmentAbsorption ComplexPressureConvolution PressureBilinearLocalization
open PressureTwoInputLocalization PressureTwoInputPhysical
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def vectorPolynomial (K : Finset Wavevector) (w : Wavevector → C3) (x : T3) : C3 :=
  ∑ q ∈ K, UnitAddTorus.mFourier q x • w q

theorem vectorPolynomial_eq_coefficientReconstruction (K : Finset Wavevector)
    (w : Wavevector → C3) (x : T3) :
    vectorPolynomial K w x = coefficientVec
      (finiteFourierReconstruction K (fun q ↦ WithLp.ofLp (w q)) x) := by
  simp only [vectorPolynomial, coefficientVec, finiteFourierReconstruction,
    WithLp.toLp_sum, WithLp.toLp_smul, WithLp.toLp_ofLp]

theorem integral_vectorPolynomial_sq (K : Finset Wavevector) (w : Wavevector → C3) :
    (∫ x : T3, ‖vectorPolynomial K w x‖ ^ 2) = ∑ q ∈ K, ‖w q‖ ^ 2 := by
  simp only [vectorPolynomial_eq_coefficientReconstruction]
  rw [integral_norm_coefficientReconstruction_sq]
  simp only [fullEnergy, ← norm_coefficientVec_sq, coefficientVec, WithLp.toLp_ofLp]

theorem vectorPolynomial_convolution (A P : Finset Wavevector) (c : Wavevector → ℂ)
    (w : Wavevector → C3) (x : T3) :
    vectorPolynomial (finiteCutoffOutputModes A P) (vectorConvolution A P c w) x =
      finiteScalarFourierReconstruction A c x • vectorPolynomial P w x := by
  exact sum_character_smul_vectorConvolution A P (finiteCutoffOutputModes A P)
    c (fun q ↦ UnitAddTorus.mFourier q x) w (fun _ _ ↦ UnitAddTorus.mFourier_add)
    (fun a ha p hp ↦ (mem_finiteCutoffOutputModes_iff A P _).mpr ⟨a, ha, p, hp, rfl⟩)

theorem doublyLocalizedOutput_polynomial (e : R3) (A D P K : Finset Wavevector)
    (c d : Wavevector → ℂ) (w v : FourierVelocity) (x : T3) :
    vectorPolynomial (finiteCutoffOutputModes A (finiteCutoffOutputModes D (finiteCutoffOutputModes P K)))
        (doublyLocalizedOutput e A D P K c d w v) x =
      (finiteScalarFourierReconstruction A c x * finiteScalarFourierReconstruction D d x) •
        vectorPolynomial (finiteCutoffOutputModes P K) (pairConvolution e P K w v) x := by
  simp only [doublyLocalizedOutput, localizedOutput, vectorPolynomial_convolution, smul_smul]

theorem doublyLocalizedOutput_energy_eq_integral (e : R3) (A D P K : Finset Wavevector)
    (c d : Wavevector → ℂ) (w v : FourierVelocity) :
    (∑ q ∈ finiteCutoffOutputModes A (finiteCutoffOutputModes D (finiteCutoffOutputModes P K)),
      ‖doublyLocalizedOutput e A D P K c d w v q‖ ^ 2) =
      ∫ x : T3, ‖finiteScalarFourierReconstruction A c x‖ ^ 2 *
        ‖finiteScalarFourierReconstruction D d x‖ ^ 2 *
        ‖vectorPolynomial (finiteCutoffOutputModes P K) (pairConvolution e P K w v) x‖ ^ 2 := by
  rw [← integral_vectorPolynomial_sq]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [doublyLocalizedOutput_polynomial, norm_smul, norm_mul]
  ring

theorem same_cutoff_energy_eq_integral_fourth_power (e : R3) (A P K : Finset Wavevector)
    (c : Wavevector → ℂ) (w v : FourierVelocity) :
    (∑ q ∈ finiteCutoffOutputModes A (finiteCutoffOutputModes A (finiteCutoffOutputModes P K)),
      ‖doublyLocalizedOutput e A A P K c c w v q‖ ^ 2) =
      ∫ x : T3, ‖finiteScalarFourierReconstruction A c x‖ ^ 4 *
        ‖vectorPolynomial (finiteCutoffOutputModes P K) (pairConvolution e P K w v) x‖ ^ 2 := by
  rw [doublyLocalizedOutput_energy_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputReconstruction
