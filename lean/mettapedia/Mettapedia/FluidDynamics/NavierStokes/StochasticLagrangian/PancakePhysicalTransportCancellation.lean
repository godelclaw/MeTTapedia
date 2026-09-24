import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeakIncompressibleTransport

/-!
# Transport cancellation for the actual filtered velocity and alignment energy

The coordinate derivatives of the filtered velocity are reconstructed from
its Fourier coefficients. Their trace vanishes by retained incompressibility.
The weak periodic integration-by-parts theorem then applies to the actual
locally Lipschitz regularized alignment energy, including spectral collisions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalTransportCancellation

open scoped Topology NNReal Matrix.Norms.Elementwise
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakePeriodicCoherentSplit
open PancakeFilteredStrainDynamics PancakeFourierMaterialPaths PancakeFourierTranslationCurve
open PancakeMeasurableMaterialRate PancakePhysicalViscousSplit PancakeMappedFourierDiffusion
open PancakePhysicalDiffusionLimit PancakeLocallyLipschitzEnergy PancakeHaarTransportRate
open PancakeWeakIncompressibleTransport PancakePhysicalSpectralDefect
open PancakeFrequencyProjectorCommutator PancakeDyadicDirectionEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def velocityComponent (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ := spatialVelocity chi modes u x j

theorem mappedField_velocity (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) :
    mappedField complexRealPartEuclideanCLM modes (filteredVelocity chi u) = spatialVelocity chi modes u := by
  funext x
  simp only [mappedField, fourierField_vector_eq, spatialVelocity]

theorem continuous_velocityComponent (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) : Continuous (velocityComponent chi modes u j) := by
  have hv : Continuous (spatialVelocity chi modes u) := by
    rw [← mappedField_velocity]
    exact continuous_mappedField _ _ _
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) j).continuous.comp hv

theorem contDiff_real_velocityComponent (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) :
    ContDiff ℝ 1 (fun r : X3 ↦ velocityComponent chi modes u j (torusPoint r)) := by
  have hv : ContDiff ℝ 1 (fun z : ℝ × X3 ↦ spatialVelocity chi modes u (torusPoint z.2)) :=
    complexRealPartEuclideanCLM.contDiff.comp
      (contDiff_real_reconstruction modes (fun _ : ℝ ↦ filteredVelocity chi u)
        (fun _ _ _ ↦ contDiff_const))
  have hline : ContDiff ℝ 1 (fun r : X3 ↦ ((0 : ℝ), r)) := contDiff_const.prodMk contDiff_id
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) j).contDiff.comp (hv.comp hline)

theorem shiftRate_velocityComponent (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) :
    shiftRate (velocityComponent chi modes u j) (coordinateShift j) x =
      (finiteFourierReconstruction modes (derivativeCoeff j (filteredVelocity chi u)) x j).re := by
  have hv := hasDerivAt_mappedField_shift complexRealPartEuclideanCLM modes
    (filteredVelocity chi u) j 0 x
  have hj := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) j).hasFDerivAt.comp_hasDerivAt 0 hv
  simpa only [shiftRate, velocityComponent, mappedField_velocity, coordinateShift_zero, add_zero,
    mappedField, fourierField_vector_eq, complexRealPartEuclideanCLM_apply,
    spatialVelocity, Function.comp_def,
    PancakeTransverseEnergyFreezing.complexRealPartEuclidean, PiLp.proj_apply, PiLp.toLp_apply]
    using hj.deriv

theorem coordinateDivergence_velocity_zero (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : ∀ q ∈ modes, modeDot q (u q) = 0) (x : T3) :
    coordinateDivergence (velocityComponent chi modes u) x = 0 := by
  simp only [coordinateDivergence, shiftRate_velocityComponent]
  rw [← Complex.re_sum]
  suffices (∑ j : Fin 3,
      finiteFourierReconstruction modes (derivativeCoeff j (filteredVelocity chi u)) x j) = 0 by
    rw [this, Complex.zero_re]
  simp only [finiteFourierReconstruction, derivativeCoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro q hq
  have hdot := filteredVelocity_transverse chi u q (hu q hq)
  calc
    (∑ j : Fin 3, UnitAddTorus.mFourier q x *
        ((unitTorusDerivativePhase * (q j : ℂ)) * filteredVelocity chi u q j)) =
        (UnitAddTorus.mFourier q x * unitTorusDerivativePhase) * modeDot q (filteredVelocity chi u q) := by
      simp only [modeDot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hdot, mul_zero]

theorem locallyLipschitz_timeSlice (f : ℝ × X3 → ℝ) (hf : LocallyLipschitz f) (t : ℝ) :
    LocallyLipschitz (fun r : X3 ↦ f (t, r)) :=
  hf.comp (LipschitzWith.prodMk_left t).locallyLipschitz

theorem locallyLipschitz_spatial_energy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) :
    LocallyLipschitz (fun r : X3 ↦ physicalRegularizedEnergy chi modes u delta (torusPoint r)) := by
  have hE := locallyLipschitz_real_energy chi modes (fun _ : ℝ ↦ u) delta (fun _ _ _ ↦ contDiff_const)
  exact locallyLipschitz_timeSlice _ hE 0

theorem integral_physicalEnergy_transport_zero
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (delta : ℝ)
    (hu : ∀ q ∈ modes, modeDot q (u q) = 0) :
    Integrable (coordinateTransport (physicalRegularizedEnergy chi modes u delta)
      (velocityComponent chi modes u)) ∧
    (∫ x : T3, coordinateTransport (physicalRegularizedEnergy chi modes u delta)
      (velocityComponent chi modes u) x) = 0 := by
  have he : Continuous (physicalRegularizedEnergy chi modes u delta) := by
    exact PancakeHaarDiffusionIncrement.continuous_regularizedEnergy _ _ delta
      (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
      (PancakeMaterialDiffusionBudget.continuous_vorticity modes u)
  exact integral_coordinateTransport_zero _ _ he (continuous_velocityComponent chi modes u)
    (locallyLipschitz_spatial_energy chi modes u delta)
    (fun j ↦ (contDiff_real_velocityComponent chi modes u j).locallyLipschitz)
    (Filter.Eventually.of_forall (coordinateDivergence_velocity_zero chi modes u hu))

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalTransportCancellation
