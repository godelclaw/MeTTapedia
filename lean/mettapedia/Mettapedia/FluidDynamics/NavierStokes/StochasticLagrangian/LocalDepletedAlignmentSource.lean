import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralCommutatorEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalInitialAlignmentBudget

/-!
# Continuous alignment-depleted source for the actual local fields

Only the strain is filtered. A scalar envelope retains alignment depletion
and distinguishes source tilt through the strain commutator, without
integrating a selected eigenline. It is pointwise no larger than
the previous signed source, and leaves the mismatch and regularizer
stretching with their signs. No all-scale source bound is asserted.
The source smoothing parameter `epsilon` is independent of the energy
regularizer `delta` that pays the joint viscous estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalDepletedAlignmentSource

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeHigherDerivativeMoments
open PancakeFilteredStrainDynamics PancakeGalerkinKineticEnergy PancakePhysicalLaplacian
open PancakeFourierMaterialPaths PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution
open PancakeRegularizedMaterialRate PancakeFourierStrainGradient InfiniteConvectionEnergy
open PancakeLocalInfiniteVelocity
open PancakeMeasurableMaterialRate
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing LocalAlignmentContinuity
open LocalSignedAlignmentBudget

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def depletedForcingEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon : ℝ) (x : T3) : ℝ :=
  SpectralCommutatorEnvelope.envelope (spatialStrain modes (filteredVelocity chi u) x)
    (nonviscousRemainder chi modes outputs u x) (fullVorticity u x) epsilon +
      2 * ⟪residual chi modes u x, strainMismatch chi modes u x⟫ +
      2 * delta * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫

theorem depletedForcingEnvelope_le_signed (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta epsilon : ℝ) (x : T3) :
    depletedForcingEnvelope chi modes outputs u delta epsilon x ≤
      signedForcingEnvelope chi modes outputs u delta x := by
  have h := SpectralCommutatorEnvelope.envelope_le_coarse
    (spatialStrain modes (filteredVelocity chi u) x)
    (nonviscousRemainder chi modes outputs u x) (fullVorticity u x) epsilon
  unfold depletedForcingEnvelope signedForcingEnvelope
  linarith

theorem materialRate_depleted_le (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta nu epsilon : ℝ) (heps : 0 < epsilon) (x : T3) :
    materialRate chi modes outputs u delta nu x + ‖residual chi modes u x‖ ^ 2 ≤
      nu * linearRate (spatialStrain modes (filteredVelocity chi u) x) delta (fullVorticity u x)
        (strainLaplacian modes (filteredVelocity chi u) x) (fullVorticityLaplacian u x) +
      depletedForcingEnvelope chi modes outputs u delta epsilon x := by
  have hR := (le_abs_self (remainderAnisotropy (nonviscousRemainder chi modes outputs u x)
    (topVector (spatialStrain modes (filteredVelocity chi u) x)) (fullVorticity u x))).trans
      (SpectralCommutatorEnvelope.abs_remainderAnisotropy_le_envelope _ _ _ epsilon heps)
  unfold materialRate
  rw [linearRate_viscous_split, resolved_add_strainMismatch]
  unfold depletedForcingEnvelope LocalAlignmentForcing.residual
  linarith

theorem continuous_depletedForcingEnvelope (chi : Wavevector → ℂ)
    (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (delta epsilon : ℝ) (heps : 0 < epsilon) :
    Continuous (depletedForcingEnvelope chi modes outputs u delta epsilon) := by
  have hw := continuous_fullVorticity u hu
  have hE := SpectralCommutatorEnvelope.continuous_envelope _ _ _ epsilon heps
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_nonviscousRemainder chi modes outputs u) hw
  exact (hE.add (continuous_const.mul ((continuous_residual chi modes u hu).inner
    (continuous_strainMismatch chi modes u hu)))).add
    (continuous_const.mul (hw.inner ((continuous_fullStrainOperator u hu).clm_apply hw)))

theorem continuous_depletedForcingEnvelope_spaceTime {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (delta epsilon : ℝ) (heps : 0 < epsilon) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      depletedForcingEnvelope chi modes outputs (s.coefficients z.1) delta epsilon z.2) := by
  have hc (q : Wavevector) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
    (s.continuous q i).comp continuous_subtype_val
  have hS := continuous_parametric_strain modes chi
    (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t) (fun q _ i ↦ hc q i)
  have hw := continuous_fullVorticity_spaceTime s g hSum hu
  have hR := continuous_nonviscousRemainder_parametric _ hc g hg hSum (fun t ↦ hu t t.2)
    chi C hchi modes outputs
  have hF := continuous_fullStrainOperator_parametric _ hc g hSum (fun t ↦ hu t t.2)
  have hE := SpectralCommutatorEnvelope.continuous_envelope _ _ _ epsilon heps hS hR hw
  exact (hE.add (continuous_const.mul ((continuous_residual_spaceTime s g hSum hu chi modes).inner
    (continuous_strainMismatch_spaceTime s g hSum hu chi modes)))).add
    (continuous_const.mul (hw.inner (hF.clm_apply hw)))

theorem integral_materialRate_add_residual_le
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (delta nu epsilon : ℝ)
    (hd : 0 < delta) (heps : 0 < epsilon) (hnu : 0 ≤ nu)
    (hF : Integrable (materialRate chi modes outputs u delta nu)) :
    (∫ x : T3, materialRate chi modes outputs u delta nu x) + (∫ x : T3, ‖residual chi modes u x‖ ^ 2) ≤
      (16 * nu / delta) * strainGradientCutoffWeight modes chi * kineticEnergy u * kineticEnergy (fourierCurl u) +
      ∫ x : T3, depletedForcingEnvelope chi modes outputs u delta epsilon x := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hz : Integrable (fun x : T3 ↦ ‖residual chi modes u x‖ ^ 2) :=
    ((continuous_residual chi modes u hu1).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (depletedForcingEnvelope chi modes outputs u delta epsilon) :=
    (continuous_depletedForcingEnvelope chi modes outputs u hu1 delta epsilon heps).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_laplacian_diffusion_energy_paid modes chi u hu
    (fun x ↦ materialRate chi modes outputs u delta nu x + ‖residual chi modes u x‖ ^ 2)
    (depletedForcingEnvelope chi modes outputs u delta epsilon) delta nu hd hnu (hF.add hz) hR
    (Filter.Eventually.of_forall (materialRate_depleted_le chi modes outputs u delta nu epsilon heps))
  rw [integral_add hF hz] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.LocalDepletedAlignmentSource
