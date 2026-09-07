import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAEMaterialRate

/-!
# The paid spatial material estimate from the retained velocity equation

The supplied finite velocity solution gives C¹ coefficient regularity.
Rademacher and periodic Haar transport give AE spectral differentiability;
the constructed measurable derivative then agrees with the physical rate.
No separate differentiability, integrability, or full-rate budget is assumed.
Construction of the velocity solution and the time-integrated advective
balance are separate obligations, not conclusions of this module.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeMaterialSpatialEstimate

open scoped Topology ComplexConjugate RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakePhysicalDefectODEBudget
open PancakeMeasurableMaterialRate PancakeFrozenMaterialDerivative PancakeAEMaterialRate
open PancakeMaterialDiffusionBudget PancakeFourierStrainGradient PancakeSpectralDefectEvolution
open PancakePhysicalSpectralDefect
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeFrequencyProjectorCommutator

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem contDiff_coefficients_of_velocityRHS
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (nu : ℝ)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ t, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ t, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    ∀ q ∈ modes, ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i) := by
  have hc : ∀ q ∈ modes, ∀ i, ContinuousOn (fun t ↦ u t q i) Set.univ :=
    continuousOn_coefficients_of_velocityRHS modes u nu Set.univ (fun t _ ↦ hd t)
  intro q hq i
  have hR : Continuous (fun t ↦ velocityRHS modes (u t) nu q i) :=
    continuousOn_univ.mp
      (continuousOn_velocityRHS modes u nu Set.univ hk (fun t _ ↦ hu t) hc q hq i)
  exact contDiff_one_iff_deriv.mpr
    ⟨fun t ↦ (hd t q hq i).differentiableAt, hR.congr (fun t ↦ (hd t q hq i).deriv.symm)⟩

/-- The AE time slice estimate uses the actual derivative of the actual
regularized energy along the actual instantaneous material direction.
The nonviscous forcing and the cutoff-dependent price remain explicit. -/
theorem ae_integral_frozenMaterialRate_paid_of_velocityRHS
    (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (delta nu : ℝ) (hdelt : 0 < delta) (hnu : 0 ≤ nu)
    (hlow : low ⊆ modes) (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ t, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ t, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    ∀ᵐ t : ℝ,
      (∫ x : T3, frozenMaterialRate chi modes u delta t x) + (1 / 2 : ℝ) * (∫ x : T3,
        ‖spectralResidual (spatialStrain modes (filteredVelocity chi (u t)) x).1
          (topEigenvalue (spatialStrain modes (filteredVelocity chi (u t)) x))
          (spatialVorticity modes (u t) x)‖ ^ 2) ≤
        (16 * nu / delta) * strainGradientCutoffWeight low chi *
          PancakeViscousMisalignmentAbsorption.fullEnergy modes (u t) *
          PancakeViscousMisalignmentAbsorption.fullEnergy modes (fourierCurl (u t)) +
        ∫ x : T3, physicalNonviscousEnvelope chi modes outputs (u t) delta x := by
  have hc := contDiff_coefficients_of_velocityRHS modes u nu hk hu hd
  filter_upwards [ae_ae_materialSpectralDifferentiable chi modes u hc] with t hL
  exact integral_frozenMaterialRate_paid chi low modes outputs u delta nu t hdelt hnu
    hlow hsub hout hchi hchir hs (hr t) hk (hu t)
    (fun q hq i ↦ (hc q hq i).continuous) (hd t) hL

end Mettapedia.FluidDynamics.NavierStokes.PancakeMaterialSpatialEstimate
