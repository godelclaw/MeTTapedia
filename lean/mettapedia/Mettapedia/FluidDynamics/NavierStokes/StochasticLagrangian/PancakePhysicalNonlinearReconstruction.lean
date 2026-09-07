import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeVorticityTransportSplit

/-!
# Full-output reconstruction of the physical nonlinear vorticity term

The actual symmetric strain acting on the actual retained vorticity is
recovered from its convolution coefficients. The Fourier transport term
is likewise identified with the actual coordinate transport. Output
closure, physical curl inversion and reality are explicit hypotheses.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalNonlinearReconstruction

open scoped Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFourierPressureStrain PancakeFourierMaterialPaths
open PancakeFilteredStrainDynamics PancakePhysicalSpectralDefect PancakeSpatialStrainEvolution
open PancakeVorticityTransportSplit PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeWeightedOperatorTransport PancakePhysicalTransportCancellation PancakeDyadicDirectionEvolution
open PancakeBlockReality PancakeTransverseEnergyFreezing

local notation "T3" => UnitAddTorus (Fin 3)

theorem vectorReconstruction_pairSum
    (modes outputs : Finset Wavevector) (F : Wavevector → Wavevector → VelocityCoefficient)
    (x : T3) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs) :
    finiteFourierReconstruction outputs
      (fun q ↦ ∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then F k l else 0) x =
        ∑ k ∈ modes, ∑ l ∈ modes, UnitAddTorus.mFourier (k + l) x • F k l := by
  classical
  simp only [finiteFourierReconstruction, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp [smul_ite, hout k hk l hl]

theorem reconstruction_matrixVector_product
    (modes outputs : Finset Wavevector) (A : FourierMatrix) (w : FourierVelocity) (x : T3)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs) :
    finiteFourierReconstruction outputs
      (fun q ↦ ∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then (A k).mulVec (w l) else 0) x =
        (matrixReconstruction modes A x).mulVec (finiteFourierReconstruction modes w x) := by
  rw [vectorReconstruction_pairSum modes outputs _ x hout]
  simp only [matrixReconstruction, finiteFourierReconstruction, Matrix.sum_mulVec, Matrix.mulVec_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [UnitAddTorus.mFourier_add, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]

theorem unitTorusStrainStretchAmp_fourierCurl (k : Wavevector) (u : FourierVelocity)
    (w : VelocityCoefficient) (hk : frequencyVec k ≠ 0) (hu : modeDot k (u k) = 0) :
    unitTorusStrainStretchAmp k (fourierCurl u k) w = (strainCoeff u k).mulVec w := by
  unfold unitTorusStrainStretchAmp
  rw [physicalBiotSavart_fourierCurl k u hk hu]
  ext i
  simp [strainCoeff, gradientCoeff, Matrix.mulVec, dotProduct, coefficientDot, modeDot,
    wavevectorCoefficient, Fin.sum_univ_three]
  ring

theorem complexRealPart_mulVec (A : MatrixCoefficient) (w : VelocityCoefficient)
    (hA : ∀ i j, (A i j).im = 0) :
    complexRealPartEuclideanCLM (A.mulVec w) = realMatrixOperator A (complexRealPartEuclidean w) := by
  ext i
  simp [complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
    realMatrixOperator_apply, Matrix.mulVec, dotProduct, Complex.mul_re, hA]

theorem reconstruction_stretching_physical
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    complexRealPartEuclideanCLM (finiteFourierReconstruction outputs
      (finiteUnitTorusStretchingCoeff modes modes (fourierCurl u) (fourierCurl u)) x) =
        (spatialStrain modes u x).1 (spatialVorticity modes u x) := by
  classical
  have he : finiteUnitTorusStretchingCoeff modes modes (fourierCurl u) (fourierCurl u) =
      fun q ↦ ∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then
        (strainCoeff u k).mulVec (fourierCurl u l) else 0 := by
    funext q
    simp only [finiteUnitTorusStretchingCoeff, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro k hkM
    apply Finset.sum_congr rfl
    intro l _
    rw [unitTorusStrainStretchAmp_fourierCurl k u _ (hk k hkM) (hu k hkM)]
  rw [he, reconstruction_matrixVector_product modes outputs _ _ x hout,
    complexRealPart_mulVec _ _ (matrixReconstruction_real modes _ hs (strainCoeff_conjugate u hr) x)]
  rfl

theorem reconstruction_negativeTransport_physical
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    complexRealPartEuclideanCLM (finiteFourierReconstruction outputs
      (finiteUnitTorusNegativeTransportCoeff modes modes (fourierCurl u) (fourierCurl u)) x) =
        -vectorTransport (spatialVorticity modes u) (velocityComponent (fun _ ↦ 1) modes u) x := by
  classical
  have he : finiteUnitTorusNegativeTransportCoeff modes modes (fourierCurl u) (fourierCurl u) =
      fun q ↦ ∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then
        (-(unitTorusDerivativePhase * modeDot l (u k))) • fourierCurl u l else 0 := by
    funext q
    rw [PancakeMaterialTransportCommutator.finiteUnitTorusNegativeTransportCoeff_eq_doubleSum]
    apply Finset.sum_congr rfl
    intro k hkM
    apply Finset.sum_congr rfl
    intro l _
    simp only [unitTorusNegativeTransportAmp, physicalBiotSavart_fourierCurl k u (hk k hkM) (hu k hkM)]
  rw [he, vectorReconstruction_pairSum modes outputs _ x hout]
  have hc : (∑ k ∈ modes, ∑ l ∈ modes, UnitAddTorus.mFourier (k + l) x •
      (-(unitTorusDerivativePhase * modeDot l (u k))) • fourierCurl u l) =
        -(∑ l ∈ modes, finiteVelocityCharacterRate modes u l x • fourierCurl u l) := by
    rw [Finset.sum_comm]
    simp only [finiteVelocityCharacterRate, ← Finset.sum_neg_distrib, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    ext i
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  rw [hc, map_neg]
  have hf : filteredVelocity (fun _ ↦ 1) u = u := by funext q i; simp [filteredVelocity]
  simpa only [hf] using congrArg Neg.neg
    (real_characterTransport_eq (fun _ ↦ 1) modes u x hs hr (fun _ ↦ by simp))

theorem reconstruction_nonlinear_physical
    (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    complexRealPartEuclideanCLM (finiteFourierReconstruction outputs
      (finiteUnitTorusVorticityRHS modes modes (fourierCurl u) (fourierCurl u) 0) x) =
        (spatialStrain modes u x).1 (spatialVorticity modes u x) -
          vectorTransport (spatialVorticity modes u) (velocityComponent (fun _ ↦ 1) modes u) x := by
  have he : finiteUnitTorusVorticityRHS modes modes (fourierCurl u) (fourierCurl u) 0 =
      fun q ↦ finiteUnitTorusStretchingCoeff modes modes (fourierCurl u) (fourierCurl u) q +
        finiteUnitTorusNegativeTransportCoeff modes modes (fourierCurl u) (fourierCurl u) q := by
    funext q
    simp [finiteUnitTorusVorticityRHS, finiteUnitTorusNonstretchingCoeff, unitTorusViscousVorticityCoeff]
  rw [he]
  simp only [finiteFourierReconstruction, smul_add, Finset.sum_add_distrib, map_add]
  change complexRealPartEuclideanCLM (finiteFourierReconstruction outputs
    (finiteUnitTorusStretchingCoeff modes modes (fourierCurl u) (fourierCurl u)) x) +
    complexRealPartEuclideanCLM (finiteFourierReconstruction outputs
    (finiteUnitTorusNegativeTransportCoeff modes modes (fourierCurl u) (fourierCurl u)) x) = _
  rw [reconstruction_stretching_physical modes outputs u x hout hk hu hs hr,
    reconstruction_negativeTransport_physical modes outputs u x hout hk hu hs hr, sub_eq_add_neg]

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalNonlinearReconstruction
