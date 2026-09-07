import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalLaplacian
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalDefectODEBudget

/-!
# Explicit viscosity separation in the physical material equations

The previously constructed strain remainder and vorticity forcing split
into their zero-viscosity expressions plus the actual spatial Laplacians.
The zero-viscosity parameter here selects terms of the instantaneous RHS;
it does not replace a viscous solution by an Euler solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalViscousSplit

open scoped Topology ComplexConjugate RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicVorticityEquation PancakePeriodicCoherentSplit
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakeMappedFourierDiffusion
open PancakePhysicalLaplacian PancakePhysicalDiffusionLimit PancakePhysicalSpectralDefect
open PancakeDyadicDirectionEvolution PancakeRegularizedMaterialRate PancakeFilteredStrainDynamics
open PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator PancakeSpatialStrainEvolution
open PancakeMovingBlockEvolution PancakeFourierPressureStrain PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeRegularizedDiffusion
open PancakeSpectralDefectEvolution PancakeSpectralFiniteDifference

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

theorem viscousStrainCoeff_zero (u : FourierVelocity) (q : Wavevector) : viscousStrainCoeff 0 u q = 0 := by
  simp [viscousStrainCoeff_eq]

theorem strainForcingCoeff_viscous_split (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) :
    strainForcingCoeff chi modes u nu = fun q ↦
      strainForcingCoeff chi modes u 0 q + viscousStrainCoeff nu (filteredVelocity chi u) q := by
  funext q
  simp only [strainForcingCoeff, viscousStrainCoeff_zero, add_zero]
  abel

theorem spatialStrainRemainder_viscous_split (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) :
    spatialStrainRemainder chi modes outputs u nu x = spatialStrainRemainder chi modes outputs u 0 x +
      nu • strainLaplacian outputs (filteredVelocity chi u) x := by
  unfold spatialStrainRemainder spatialStrainForcing
  rw [strainForcingCoeff_viscous_split, matrixReconstruction_add, realMatrixOperator_add,
    reconstructed_viscousStrain]
  abel

theorem finiteVorticityRHS_viscous_split (modes : Finset Wavevector) (a : FourierVelocity)
    (nu : ℝ) (q : Wavevector) :
    finiteUnitTorusVorticityRHS modes modes a a nu q =
      finiteUnitTorusVorticityRHS modes modes a a 0 q + unitTorusViscousVorticityCoeff nu a q := by
  simp only [finiteUnitTorusVorticityRHS, finiteUnitTorusNonstretchingCoeff,
    unitTorusViscousVorticityCoeff, Complex.ofReal_zero, zero_mul, zero_smul, add_zero]
  abel

theorem movingDerivative_viscous_split (modes : Finset Wavevector) (a : FourierVelocity)
    (phase : Wavevector → ℂ) (nu : ℝ) (x : T3) :
    movingFiniteFourierDerivative modes a (finiteUnitTorusVorticityRHS modes modes a a nu) phase x =
      movingFiniteFourierDerivative modes a (finiteUnitTorusVorticityRHS modes modes a a 0) phase x +
      finiteFourierReconstruction modes (unitTorusViscousVorticityCoeff nu a) x := by
  have heq : finiteUnitTorusVorticityRHS modes modes a a nu = fun q ↦
      finiteUnitTorusVorticityRHS modes modes a a 0 q + unitTorusViscousVorticityCoeff nu a q :=
    funext (finiteVorticityRHS_viscous_split modes a nu)
  rw [heq]
  simp only [movingFiniteFourierDerivative, smul_add,
    ← add_assoc, Finset.sum_add_distrib, finiteFourierReconstruction]

theorem spatialVorticityMaterialRate_viscous_split (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) :
    spatialVorticityMaterialRate chi modes u nu x = spatialVorticityMaterialRate chi modes u 0 x +
      nu • vorticityLaplacian modes u x := by
  unfold spatialVorticityMaterialRate
  rw [movingDerivative_viscous_split]
  simp only [← complexRealPartEuclideanCLM_apply, map_add, reconstructed_viscousVorticity]

theorem spatialVorticityForcing_viscous_split (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) :
    spatialVorticityForcing chi modes u nu x = spatialVorticityForcing chi modes u 0 x +
      nu • vorticityLaplacian modes u x := by
  unfold spatialVorticityForcing
  rw [spatialVorticityMaterialRate_viscous_split]
  abel

theorem strainLaplacian_filtered_subset (outputs modes : Finset Wavevector)
    (chi : Wavevector → ℂ) (u : FourierVelocity) (x : T3) (hsub : outputs ⊆ modes)
    (hchi : ∀ q, q ∉ outputs → chi q = 0) :
    strainLaplacian modes (filteredVelocity chi u) x = strainLaplacian outputs (filteredVelocity chi u) x := by
  rw [strainLaplacian_eq, strainLaplacian_eq]
  congr 1
  apply matrixReconstruction_subset outputs modes _ x hsub
  intro q hq
  simp [laplacianCoeff, filtered_strain_zero_of_not_mem chi outputs u hchi q hq]

def physicalRegularizedEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  regularizedEnergy (spatialStrain modes (filteredVelocity chi u) x) delta (spatialVorticity modes u x)

/-- The full regularized energy rate along an actual finite velocity
material path, with viscosity isolated as the actual spatial Laplacian. -/
theorem hasDerivAt_physicalRegularizedEnergy
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (X : ℝ → Fin 3 → ℝ) (delta nu t : ℝ)
    (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hchi : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ p ∈ modes, ∀ k : Fin 3,
      HasDerivAt (fun tau ↦ u tau p k) (velocityRHS modes (u t) nu p k) t)
    (hX : ∀ i, HasDerivAt (fun tau ↦ X tau i)
      (finiteFourierReconstruction modes (filteredVelocity chi (u t)) (torusPoint (X t)) i).re t)
    (hlambda : DifferentiableAt ℝ (fun tau ↦ topEigenvalue (physicalStrainPath chi modes u X tau)) t) :
    let x := torusPoint (X t)
    let S := spatialStrain modes (filteredVelocity chi (u t)) x
    let w := spatialVorticity modes (u t) x
    let z := spectralResidual S.1 (topEigenvalue S) w
    let R := spatialStrainRemainder chi modes outputs (u t) 0 x
    let f := spatialVorticityForcing chi modes (u t) 0 x
    HasDerivAt (fun tau ↦ physicalRegularizedEnergy chi modes (u tau) delta (torusPoint (X tau)))
      (-‖z‖ ^ 2 + remainderAnisotropy R (topVector S) w + 2 * ⟪z, f⟫ +
        2 * delta * ⟪w, S.1 w + f⟫ + nu * linearRate S delta w
          (strainLaplacian modes (filteredVelocity chi (u t)) x) (vorticityLaplacian modes (u t) x)) t := by
  dsimp only
  have hS := hasDerivAt_spatialStrain_material chi modes outputs u X nu t hsub hout hchi hchir hs hr hk hu hd hX
  have hw := hasDerivAt_spatialVorticity_material chi modes u X nu t hchir hs hr hk hu hd hX
  have he := hasDerivAt_regularizedEnergy (physicalStrainPath chi modes u X)
    (physicalVorticityPath modes u X) _ _ delta t hS hw hlambda
  have hR := spatialStrainRemainder_viscous_split chi modes outputs (u t) nu (torusPoint (X t))
  have hf := spatialVorticityForcing_viscous_split chi modes (u t) nu (torusPoint (X t))
  rw [strainLaplacian_filtered_subset modes outputs chi (u t) (torusPoint (X t)) hsub hchi] at hR
  apply he.congr_deriv
  simp only [physicalStrainPath, physicalVorticityPath, hR, hf, ← add_assoc, linearRate_viscous_split]

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalViscousSplit
