import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSignedTransportForcing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeEulerianAlignmentBudget

/-!
# A paid material estimate with the transport mismatch removed before Young

The reduced envelope squares only the remaining vector forcing. The
transport mismatch contributes the signed variation of the actual low
spectral weight. The diffusion price is unchanged and remains explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeReducedMaterialBudget

open MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
open PeriodicFourierTriad PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakePhysicalSpectralDefect PancakeMaterialDiffusionBudget PancakePhysicalWeightedTransport
open PancakePhysicalTransportCancellation PancakeWeightedOperatorTransport PancakeSignedTransportForcing
open PancakeRegularizedMaterialRate PancakeRegularizedDiffusion PancakeSpectralDefectEvolution
open PancakePhysicalViscousSplit PancakePhysicalLaplacian PancakeFourierStrainGradient
open PancakeSpatialStrainEvolution PancakeGalerkinKineticEnergy PancakeViscousMisalignmentAbsorption
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeEulerianAlignmentBudget
open PancakeLowDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def physicalReducedEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  nonviscousEnvelope (spatialStrain modes (filteredVelocity chi u) x) (spatialVorticity modes u x)
    (spatialStrainRemainder chi modes outputs u 0 x) (reducedVorticityForcing chi modes u 0 x) delta

def physicalTransportPairing (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : T3 → ℝ :=
  gapForcingPairing chi modes u delta
    (vectorTransport (spatialVorticity modes u) (velocityComponent (fun q ↦ chi q - 1) modes u))

theorem continuous_physicalReducedEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : Continuous (physicalReducedEnvelope chi modes outputs u delta) :=
  continuous_nonviscousEnvelope _ _ _ _ delta (continuous_strain modes (filteredVelocity chi u))
    (continuous_vorticity modes u) (continuous_strainRemainder chi modes outputs u 0)
    (continuous_reducedVorticityForcing chi modes u 0)

theorem integral_physicalTransportPairing (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (hu : ∀ q ∈ modes, modeDot q (u q) = 0) :
    Integrable (physicalTransportPairing chi modes u delta) ∧
      (∫ x : T3, physicalTransportPairing chi modes u delta x) =
        -(∫ x : T3, physicalWeightVariation chi (fun q ↦ chi q - 1) modes u delta x) := by
  obtain ⟨hi, _, he⟩ := integral_physical_weighted_transport chi (fun q ↦ chi q - 1) modes u delta hu
  refine ⟨hi.const_mul 2, ?_⟩
  exact (integral_const_mul 2 _).trans he

theorem physicalMaterialRate_reduced_le
    (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector) (u : FourierVelocity)
    (delta nu : ℝ) (x : T3) (hlow : low ⊆ modes) (hout : modes ⊆ outputs)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    physicalMaterialRate chi modes outputs u delta nu x + (1 / 2 : ℝ) *
      ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
        (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2 ≤
      nu * linearRate (spatialStrain low (filteredVelocity chi u) x) delta (spatialVorticity modes u x)
        (strainLaplacian low (filteredVelocity chi u) x) (vorticityLaplacian modes u x) +
      physicalReducedEnvelope chi modes outputs u delta x + physicalTransportPairing chi modes u delta x := by
  have hR := spatialStrainRemainder_viscous_split chi modes outputs u nu x
  rw [strainLaplacian_filtered_subset low outputs chi u x (hlow.trans hout) hchi] at hR
  have hf := spatialVorticityForcing_viscous_split chi modes u nu x
  have hf0 := forcing_eq_reduced_add_transport chi modes u 0 x hs hr hchir
  unfold physicalMaterialRate physicalReducedEnvelope physicalTransportPairing gapForcingPairing physicalGapWeight
  dsimp only
  rw [hR, hf, hf0]
  simp only [← add_assoc]
  have hm := material_linearRate_transport_le (spatialStrain modes (filteredVelocity chi u) x)
    (spatialVorticity modes u x) (spatialStrainRemainder chi modes outputs u 0 x)
    (strainLaplacian low (filteredVelocity chi u) x) (reducedVorticityForcing chi modes u 0 x)
    (vectorTransport (spatialVorticity modes u) (velocityComponent (fun q ↦ chi q - 1) modes u) x)
    (vorticityLaplacian modes u x) delta nu
  rw [spatialStrain_filtered_subset low modes chi u x hlow hchi] at hm ⊢
  exact hm

theorem integral_materialRate_reduced_paid
    (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector) (u : FourierVelocity)
    (delta nu : ℝ) (F : T3 → ℝ) (hdelt : 0 < delta) (hnu : 0 ≤ nu)
    (hlow : low ⊆ modes) (hout : modes ⊆ outputs)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q))
    (hu : ∀ q ∈ modes, modeDot q (u q) = 0)
    (hF : Integrable F) (hpoint : ∀ᵐ x : T3, F x ≤ physicalMaterialRate chi modes outputs u delta nu x) :
    (∫ x : T3, F x) + (1 / 2 : ℝ) * meanResidualSquare chi modes u ≤
      (16 * nu / delta) * strainGradientCutoffWeight low chi * fullEnergy modes u * fullEnergy modes (fourierCurl u) +
      (∫ x : T3, physicalReducedEnvelope chi modes outputs u delta x) -
      (∫ x : T3, physicalWeightVariation chi (fun q ↦ chi q - 1) modes u delta x) := by
  let Z := fun x ↦ ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
    (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2
  have hZ : Integrable Z := ((continuous_residual _ _ (continuous_strain modes (filteredVelocity chi u))
    (continuous_vorticity modes u)).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (physicalReducedEnvelope chi modes outputs u delta) :=
    (continuous_physicalReducedEnvelope chi modes outputs u delta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨hT, hcancel⟩ := integral_physicalTransportPairing chi modes u delta hu
  have hp : ∀ᵐ x : T3, F x + (1 / 2 : ℝ) * Z x ≤
      nu * linearRate (spatialStrain low (filteredVelocity chi u) x) delta (spatialVorticity modes u x)
        (strainLaplacian low (filteredVelocity chi u) x) (vorticityLaplacian modes u x) +
      (physicalReducedEnvelope chi modes outputs u delta x + physicalTransportPairing chi modes u delta x) := by
    filter_upwards [hpoint] with x hx
    have h := physicalMaterialRate_reduced_le chi low modes outputs u delta nu x hlow hout hchi hchir hs hr
    dsimp only [Z]
    linarith
  have h := integral_laplacian_diffusion_energy_paid low modes chi u
    (fun x ↦ F x + (1 / 2 : ℝ) * Z x)
    (fun x ↦ physicalReducedEnvelope chi modes outputs u delta x + physicalTransportPairing chi modes u delta x)
    delta nu hdelt hnu hlow (hF.add (hZ.const_mul (1 / 2))) (hG.add hT) hp
  rw [integral_add hF (hZ.const_mul (1 / 2)), integral_const_mul, integral_add hG hT, hcancel] at h
  simpa only [meanResidualSquare, Z, sub_eq_add_neg, add_assoc] using h

end Mettapedia.FluidDynamics.NavierStokes.PancakeReducedMaterialBudget
