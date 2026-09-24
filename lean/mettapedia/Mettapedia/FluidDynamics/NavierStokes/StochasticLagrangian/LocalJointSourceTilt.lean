import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTilt

/-!
# Direct tilt of the complete nonviscous source

All actual source channels are symmetric. Consequently only one
transverse action is needed, rather than separate actions of the source
and its adjoint. The exact pressure/subgrid cancellation and pressure
Fourier kernel are retained inside this action before taking its norm.
These pointwise identities do not supply its global time-integrated bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalJointSourceTilt

open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakeSpatialStrainEvolution PancakeAnisotropyDepletion PancakeSpectralFiniteDifference
open PancakeSpectralDefectEvolution PancakeSobolevFiberEnvelope PancakeLocalInfiniteVelocity
open LocalAlignmentForcing LocalSourceCommutator SpectralSourceCommutator
open LocalPressureCommutator FourierPressureCommutator FourierPressureTilt LocalLowDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem spatialSpin_adjoint (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    (spatialSpin modes u x).adjoint = -spatialSpin modes u x := by
  rw [spatialSpin, realMatrixOperator_adjoint, matrixReconstruction_transpose]
  simp only [spinCoeff_transpose, matrixReconstruction_neg, realMatrixOperator_neg]

theorem pressureOperator_adjoint (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    (pressureOperator chi modes outputs u x).adjoint = pressureOperator chi modes outputs u x := by
  rw [pressureOperator, realMatrixOperator_adjoint, matrixReconstruction_transpose]
  simp only [pressureHessianCoeff_symmetric]

theorem subgridOperator_adjoint (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    (subgridOperator chi outputs u x).adjoint = subgridOperator chi outputs u x := by
  rw [subgridOperator, realMatrixOperator_adjoint, matrixReconstruction_strain_symmetric]

theorem transportOperator_adjoint (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    (transportOperator chi modes outputs u x).adjoint = transportOperator chi modes outputs u x := by
  have ht (q : Wavevector) :
      (LocalFilteredStrain.transportCorrectionCoeff modes (filteredVelocity chi u)
        (fun i ↦ InfiniteFourierTransport.velocityComponent u i x) x q).transpose =
      LocalFilteredStrain.transportCorrectionCoeff modes (filteredVelocity chi u)
        (fun i ↦ InfiniteFourierTransport.velocityComponent u i x) x q := by
    simp only [LocalFilteredStrain.transportCorrectionCoeff, Matrix.transpose_smul, strainCoeff_transpose]
  rw [transportOperator, realMatrixOperator_adjoint, matrixReconstruction_transpose]
  simp only [ht]

theorem nonviscousRemainder_adjoint (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    (nonviscousRemainder chi modes outputs u x).adjoint = nonviscousRemainder chi modes outputs u x := by
  rw [nonviscousRemainder_eq]
  simp only [map_add, map_sub, map_neg, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.adjoint_comp, spatialSpin_adjoint, pressureOperator_adjoint,
    subgridOperator_adjoint, transportOperator_adjoint]
  congr 3
  ext v
  simp only [ContinuousLinearMap.comp_apply, neg_apply, map_neg, neg_neg]

def jointTilt (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 :=
  let e := topVector (spatialStrain modes (filteredVelocity chi u) x)
  lineRemainder e (nonviscousRemainder chi modes outputs u x e)

theorem abs_sourceAnisotropy_le_jointTilt
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    let w := fullVorticity u x
    let m := lineRemainder (topVector S) w
    |remainderAnisotropy (nonviscousRemainder chi modes outputs u x) (topVector S) w| ≤
      2 * ‖nonviscousRemainder chi modes outputs u x‖ * ‖m‖ ^ 2 +
        2 * ‖w‖ * ‖m‖ * ‖jointTilt chi modes outputs u x‖ := by
  dsimp only
  have h := abs_anisotropy_le_transverse (spatialStrain modes (filteredVelocity chi u) x)
    (nonviscousRemainder chi modes outputs u x) (fullVorticity u x)
  rw [nonviscousRemainder_adjoint] at h
  dsimp only [jointTilt]
  nlinarith only [h]

theorem jointTilt_eq_pressure_kernel
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes outputs : Finset Wavevector) (hs : ∀ k, k ∉ modes → chi k = 0)
    (hd : ∀ k, modeDot k (u k) = 0)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) (x : T3) :
    let e := topVector (spatialStrain modes (filteredVelocity chi u) x)
    let W := spatialSpin modes (filteredVelocity chi u) x
    jointTilt chi modes outputs u x =
      lineRemainder e (-(W (W e)) + rawSubgridOperator chi outputs u x e +
        transportOperator chi modes outputs u x e) - ∑ q ∈ outputs,
          (pressureModeAmplitude chi u q x * ⟪realFrequency q, e⟫) • lineRemainder e (realFrequency q) := by
  dsimp only [jointTilt]
  rw [nonviscousRemainder_eq_joint chi u C hchi modes outputs hs hd hu x]
  simp only [add_apply, sub_apply, neg_apply, mul_apply_eq_comp]
  rw [← transverse_filteredPressure_eq_sum]
  simp only [lineRemainder, inner_add_right, inner_sub_right, inner_neg_right,
    add_smul, sub_smul, neg_smul]
  abel

theorem jointTilt_eq_pressure_kernel_of_localSolution {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes outputs : Finset Wavevector) (hs : ∀ k, k ∉ modes → chi k = 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (x : T3) :
    let u := s.coefficients t
    let e := topVector (spatialStrain modes (filteredVelocity chi u) x)
    let W := spatialSpin modes (filteredVelocity chi u) x
    jointTilt chi modes outputs u x =
      lineRemainder e (-(W (W e)) + rawSubgridOperator chi outputs u x e +
        transportOperator chi modes outputs u x e) - ∑ q ∈ outputs,
          (pressureModeAmplitude chi u q x * ⟪realFrequency q, e⟫) • lineRemainder e (realFrequency q) :=
  jointTilt_eq_pressure_kernel chi (s.coefficients t) C hchi modes outputs hs
    (s.transverse t) (s.summable_convection t ht) x

end Mettapedia.FluidDynamics.NavierStokes.LocalJointSourceTilt
