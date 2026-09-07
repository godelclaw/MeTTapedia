import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeProjectionWeightOscillation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeReducedMaterialBudget

/-!
# Retaining signed projection cancellation in the material budget

Young's inequality is applied only to the high-strain vector forcing.
The transport mismatch remains a signed weight derivative and the
projection defect remains a signed oscillation pairing. This avoids
squaring the discarded nonlinear field. Neither remaining term is
declared uniformly paid.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeProjectionMaterialBudget

open MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
open PeriodicFourierTriad PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakePhysicalSpectralDefect PancakeMaterialDiffusionBudget PancakePhysicalWeightedTransport
open PancakePhysicalTransportCancellation PancakeWeightedOperatorTransport PancakeSignedTransportForcing
open PancakeRegularizedMaterialRate PancakeRegularizedDiffusion PancakeSpectralDefectEvolution
open PancakePhysicalViscousSplit PancakePhysicalLaplacian PancakeFourierStrainGradient
open PancakeSpatialStrainEvolution PancakeGalerkinKineticEnergy PancakeViscousMisalignmentAbsorption
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeEulerianAlignmentBudget
open PancakeLowDiffusionBudget PancakeReducedMaterialBudget PancakeBlockReality
open PancakeProjectionWeightOscillation PancakeFrequencyProjectorCommutator PancakeRetainedProjectionDefect

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def highStrainForcing (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 :=
  ((spatialStrain modes u x).1 - (spatialStrain modes (filteredVelocity chi u) x).1)
    (spatialVorticity modes u x)

def physicalHighStrainEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  nonviscousEnvelope (spatialStrain modes (filteredVelocity chi u) x) (spatialVorticity modes u x)
    (spatialStrainRemainder chi modes outputs u 0 x) (highStrainForcing chi modes u x) delta

theorem continuous_highStrainForcing (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) : Continuous (highStrainForcing chi modes u) :=
  ((continuous_subtype_val.comp (continuous_strain modes u)).sub
    (continuous_subtype_val.comp (continuous_strain modes (filteredVelocity chi u)))).clm_apply
      (continuous_vorticity modes u)

theorem continuous_physicalHighStrainEnvelope (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) : Continuous (physicalHighStrainEnvelope chi modes outputs u delta) :=
  continuous_nonviscousEnvelope _ _ _ _ delta (continuous_strain modes (filteredVelocity chi u))
    (continuous_vorticity modes u) (continuous_strainRemainder chi modes outputs u 0)
    (continuous_highStrainForcing chi modes u)

theorem reducedForcing_eq_full_add_highStrain (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    reducedVorticityForcing chi modes u 0 x = spatialVorticityForcing (fun _ ↦ 1) modes u 0 x +
      highStrainForcing chi modes u x := by
  have hf : filteredVelocity (fun _ ↦ 1) u = u := by funext q i; simp [filteredVelocity]
  simp only [reducedVorticityForcing, highStrainForcing, hf]

theorem physicalMaterialRate_projection_le
    (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector) (u : FourierVelocity)
    (delta nu : ℝ) (x : T3) (hlow : low ⊆ modes) (hout : modes ⊆ outputs)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    physicalMaterialRate chi modes outputs u delta nu x + (1 / 2 : ℝ) *
      ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
        (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2 ≤
      nu * linearRate (spatialStrain low (filteredVelocity chi u) x) delta (spatialVorticity modes u x)
        (strainLaplacian low (filteredVelocity chi u) x) (vorticityLaplacian modes u x) +
      physicalHighStrainEnvelope chi modes outputs u delta x + physicalTransportPairing chi modes u delta x +
      gapForcingPairing chi modes u delta (spatialVorticityForcing (fun _ ↦ 1) modes u 0) x := by
  have hR := spatialStrainRemainder_viscous_split chi modes outputs u nu x
  rw [strainLaplacian_filtered_subset low outputs chi u x (hlow.trans hout) hchi] at hR
  have hf := spatialVorticityForcing_viscous_split chi modes u nu x
  have hf0 := forcing_eq_reduced_add_transport chi modes u 0 x hs hr hchir
  rw [reducedForcing_eq_full_add_highStrain] at hf0
  have hm := material_linearRate_transport_le (spatialStrain modes (filteredVelocity chi u) x)
    (spatialVorticity modes u x) (spatialStrainRemainder chi modes outputs u 0 x)
    (strainLaplacian low (filteredVelocity chi u) x) (highStrainForcing chi modes u x)
    (vectorTransport (spatialVorticity modes u) (velocityComponent (fun q ↦ chi q - 1) modes u) x +
      spatialVorticityForcing (fun _ ↦ 1) modes u 0 x)
    (vorticityLaplacian modes u x) delta nu
  unfold physicalMaterialRate physicalHighStrainEnvelope physicalTransportPairing gapForcingPairing physicalGapWeight
  dsimp only
  rw [hR, hf, hf0]
  have he : (spatialStrain modes (filteredVelocity chi u) x).1 (spatialVorticity modes u x) +
      (spatialVorticityForcing (fun _ ↦ 1) modes u 0 x + highStrainForcing chi modes u x +
        vectorTransport (spatialVorticity modes u) (velocityComponent (fun q ↦ chi q - 1) modes u) x +
        nu • vorticityLaplacian modes u x) =
      (spatialStrain modes (filteredVelocity chi u) x).1 (spatialVorticity modes u x) +
        highStrainForcing chi modes u x +
        (vectorTransport (spatialVorticity modes u) (velocityComponent (fun q ↦ chi q - 1) modes u) x +
          spatialVorticityForcing (fun _ ↦ 1) modes u 0 x) + nu • vorticityLaplacian modes u x := by abel
  rw [he]
  simp only [← add_assoc, inner_add_right, mul_add] at hm ⊢
  rw [spatialStrain_filtered_subset low modes chi u x hlow hchi] at hm ⊢
  exact hm

theorem integral_materialRate_projection_paid
    (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector) (u : FourierVelocity)
    (delta nu : ℝ) (F : T3 → ℝ) (x₀ : T3) (hdelt : 0 < delta) (hnu : 0 ≤ nu)
    (hlow : low ⊆ modes) (hout : modes ⊆ outputs)
    (hpair : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hu : ∀ q ∈ modes, modeDot q (u q) = 0)
    (hF : Integrable F) (hpoint : ∀ᵐ x : T3, F x ≤ physicalMaterialRate chi modes outputs u delta nu x) :
    (∫ x : T3, F x) + (1 / 2 : ℝ) * meanResidualSquare chi modes u ≤
      (16 * nu / delta) * strainGradientCutoffWeight low chi * fullEnergy modes u * fullEnergy modes (fourierCurl u) +
      (∫ x : T3, physicalHighStrainEnvelope chi modes outputs u delta x) -
      (∫ x : T3, physicalWeightVariation chi (fun q ↦ chi q - 1) modes u delta x) -
      2 * ∫ x : T3, ⟪(physicalGapWeight chi modes u 0 x - physicalGapWeight chi modes u 0 x₀)
        (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫ := by
  let Z := fun x ↦ ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
    (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2
  have hZ : Integrable Z := ((continuous_residual _ _ (continuous_strain modes (filteredVelocity chi u))
    (continuous_vorticity modes u)).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (physicalHighStrainEnvelope chi modes outputs u delta) :=
    (continuous_physicalHighStrainEnvelope chi modes outputs u delta).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨hT, hcancel⟩ := integral_physicalTransportPairing chi modes u delta hu
  have hGT : Integrable (fun x : T3 ↦ physicalHighStrainEnvelope chi modes outputs u delta x +
      physicalTransportPairing chi modes u delta x) := hG.add hT
  have hP : Integrable (gapForcingPairing chi modes u delta (spatialVorticityForcing (fun _ ↦ 1) modes u 0)) :=
    (continuous_gapForcingPairing chi modes u delta _ (continuous_vorticityForcing (fun _ ↦ 1) modes u 0)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp : ∀ᵐ x : T3, F x + (1 / 2 : ℝ) * Z x ≤
      nu * linearRate (spatialStrain low (filteredVelocity chi u) x) delta (spatialVorticity modes u x)
        (strainLaplacian low (filteredVelocity chi u) x) (vorticityLaplacian modes u x) +
      (physicalHighStrainEnvelope chi modes outputs u delta x + physicalTransportPairing chi modes u delta x +
        gapForcingPairing chi modes u delta (spatialVorticityForcing (fun _ ↦ 1) modes u 0) x) := by
    filter_upwards [hpoint] with x hx
    have h := physicalMaterialRate_projection_le chi low modes outputs u delta nu x hlow hout hchi hchir hs hr
    dsimp only [Z]
    linarith
  have h := integral_laplacian_diffusion_energy_paid low modes chi u
    (fun x ↦ F x + (1 / 2 : ℝ) * Z x)
    (fun x ↦ physicalHighStrainEnvelope chi modes outputs u delta x + physicalTransportPairing chi modes u delta x +
      gapForcingPairing chi modes u delta (spatialVorticityForcing (fun _ ↦ 1) modes u 0) x)
    delta nu hdelt hnu hlow (hF.add (hZ.const_mul (1 / 2))) (hGT.add hP) hp
  rw [integral_add hF (hZ.const_mul (1 / 2)), integral_const_mul,
    integral_add hGT hP, integral_add hG hT, hcancel,
    integral_projection_pairing_eq_frozen_oscillation chi modes outputs u delta x₀ hout hpair hk hu hs hr] at h
  simpa only [meanResidualSquare, Z, sub_eq_add_neg, neg_mul, add_assoc] using h

end Mettapedia.FluidDynamics.NavierStokes.PancakeProjectionMaterialBudget
