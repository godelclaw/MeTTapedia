import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalMeanBalance

/-!
# Joint continuity of the actual nonviscous forcing

Only retained coefficients need be continuous. At viscosity parameter zero,
the strain forcing is a finite quadratic expression in those coefficients,
even at output modes outside the retained set. The vorticity forcing uses
the actual curl of the retained velocity RHS. These facts give time
integrability on compact intervals, not a uniform forcing budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeParametricForcing

open MeasureTheory
open scoped RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakePeriodicCoherentSplit
open PancakeFourierPressureStrain PancakeFilteredStrainDynamics PancakeFourierMaterialPaths
open PancakeMeasurableMaterialRate PancakePhysicalMeanBalance PancakePhysicalSpectralDefect
open PancakePhysicalViscousSplit PancakeMaterialDiffusionBudget PancakeSpatialStrainEvolution
open PancakePhysicalDefectODEBudget PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakeFrequencyProjectorCommutator PancakeLowDiffusionBudget PancakeMovingBlockEvolution
open PancakeLowPressureBudget PancakeDyadicDirectionEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem continuous_subgridConvection (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i))
    (q : Wavevector) (i : Fin 3) :
    Continuous (fun t ↦ subgridConvection chi modes (u t) q i) := by
  simp only [subgridConvection, Finset.sum_apply]
  apply continuous_finsetSum
  intro k hk
  apply continuous_finsetSum
  intro l hl
  by_cases hkl : k + l = q
  · simp only [hkl, ite_true, orderedConvection, Pi.smul_apply, smul_eq_mul]
    have hm : Continuous (fun t ↦ modeDot l (u t k)) := by
      unfold modeDot
      exact continuous_finsetSum _ (fun j _ ↦ continuous_const.mul (hc k hk j))
    exact continuous_const.mul (hm.mul (hc l hl i))
  · simp only [hkl, ite_false, Pi.zero_apply]
    exact continuous_const

theorem continuous_strainForcingCoeff_zero (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i))
    (q : Wavevector) (i j : Fin 3) :
    Continuous (fun t ↦ strainForcingCoeff chi modes (u t) 0 q i j) := by
  have hp := continuousOn_univ.mp (continuousOn_pressureCoeff modes u q Set.univ
    (fun q hq i ↦ (hc q hq i).continuousOn))
  have hi := continuous_subgridConvection chi modes u hc q i
  have hj := continuous_subgridConvection chi modes u hc q j
  simp only [strainForcingCoeff, viscousStrainCoeff_zero, add_zero, subgridStrainCoeff,
    symmetrize, subgridGradient, gradientCoeff, pressureHessianCoeff, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
    Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

theorem continuous_parametric_matrixReconstruction
    (modes : Finset Wavevector) (A : ℝ → FourierMatrix)
    (hA : ∀ q ∈ modes, ∀ i j, Continuous (fun t ↦ A t q i j)) :
    Continuous (fun z : ℝ × T3 ↦ matrixReconstruction modes (A z.1) z.2) := by
  refine continuous_pi (fun i ↦ continuous_pi (fun j ↦ ?_))
  simp only [matrixReconstruction_apply]
  apply continuous_finsetSum
  intro q hq
  exact ((UnitAddTorus.mFourier q).continuous.comp continuous_snd).mul
    ((hA q hq i j).comp continuous_fst)

theorem continuous_parametric_strainRemainder_zero
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i)) :
    Continuous (fun z : ℝ × T3 ↦ spatialStrainRemainder chi modes outputs (u z.1) 0 z.2) := by
  have hspin : ∀ q ∈ modes, ∀ i j, Continuous (fun t ↦ spinCoeff (filteredVelocity chi (u t)) q i j) := by
    intro q hq i j
    have hi := hc q hq i
    have hj := hc q hq j
    simp only [spinCoeff, gradientCoeff, filteredVelocity, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hW := realMatrixOperatorCLM.continuous.comp
    (continuous_parametric_matrixReconstruction modes _ hspin)
  have hF := realMatrixOperatorCLM.continuous.comp
    (continuous_parametric_matrixReconstruction outputs _
      (fun q _ i j ↦ continuous_strainForcingCoeff_zero chi modes u hc q i j))
  exact (hW.mul hW).neg.add hF

theorem continuous_parametric_vorticityForcing_zero
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i))
    (hk : ∀ q ∈ modes, frequencyVec q ≠ 0)
    (hu : ∀ t, ∀ q ∈ modes, modeDot q (u t q) = 0) :
    Continuous (fun z : ℝ × T3 ↦ spatialVorticityForcing chi modes (u z.1) 0 z.2) := by
  have hcurl : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ fourierCurl (u t) q i) :=
    fun q hq i ↦ continuousOn_univ.mp
      (continuousOn_fourierCurl_coefficient u Set.univ q (fun j ↦ (hc q hq j).continuousOn) i)
  have hR : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ velocityRHS modes (u t) 0 q i) :=
    fun q hq i ↦ continuousOn_univ.mp (continuousOn_velocityRHS modes u 0 Set.univ hk
      (fun t _ ↦ hu t) (fun q hq j ↦ (hc q hq j).continuousOn) q hq i)
  have hRcurl : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦
      finiteUnitTorusVorticityRHS modes modes (fourierCurl (u t)) (fourierCurl (u t)) 0 q i) := by
    intro q hq i
    simp_rw [← fourierCurl_velocityRHS modes (u _) 0 q hk (hu _)]
    exact continuousOn_univ.mp (continuousOn_fourierCurl_coefficient _ Set.univ q
      (fun j ↦ (hR q hq j).continuousOn) i)
  have hv := continuous_parametric_reconstruction modes (fun t ↦ filteredVelocity chi (u t))
    (fun q hq i ↦ continuous_const.mul (hc q hq i))
  have hphase : ∀ q, Continuous (fun z : ℝ × T3 ↦
      finiteVelocityCharacterRate modes (filteredVelocity chi (u z.1)) q z.2) := by
    intro q
    simp only [finiteVelocityCharacterRate_eq, modeDot]
    fun_prop
  have hM : Continuous (fun z : ℝ × T3 ↦ spatialVorticityMaterialRate chi modes (u z.1) 0 z.2) := by
    apply complexRealPartEuclideanCLM.continuous.comp
    change Continuous (fun z : ℝ × T3 ↦ movingFiniteFourierDerivative modes (fourierCurl (u z.1))
      (finiteUnitTorusVorticityRHS modes modes (fourierCurl (u z.1)) (fourierCurl (u z.1)) 0)
      (fun q ↦ finiteVelocityCharacterRate modes (filteredVelocity chi (u z.1)) q z.2) z.2)
    unfold movingFiniteFourierDerivative
    apply continuous_finsetSum
    intro q hq
    exact ((hphase q).smul (continuous_pi (fun i ↦ (hcurl q hq i).comp continuous_fst))).add
      (((UnitAddTorus.mFourier q).continuous.comp continuous_snd).smul
        (continuous_pi (fun i ↦ (hRcurl q hq i).comp continuous_fst)))
  exact hM.sub (((continuous_subtype_val.comp (continuous_parametric_strain modes chi u hc)).clm_apply
    (continuous_parametric_spatialVorticity modes u hc)))

theorem continuous_parametric_nonviscousEnvelope
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity) (delta : ℝ)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i))
    (hk : ∀ q ∈ modes, frequencyVec q ≠ 0)
    (hu : ∀ t, ∀ q ∈ modes, modeDot q (u t q) = 0) :
    Continuous (fun z : ℝ × T3 ↦ physicalNonviscousEnvelope chi modes outputs (u z.1) delta z.2) := by
  have hS := continuous_subtype_val.comp (continuous_parametric_strain modes chi u hc)
  have hw := continuous_parametric_spatialVorticity modes u hc
  have hR := continuous_parametric_strainRemainder_zero chi modes outputs u hc
  have hf := continuous_parametric_vorticityForcing_zero chi modes u hc hk hu
  unfold physicalNonviscousEnvelope nonviscousEnvelope
  exact (((hR.norm.const_mul 2).mul (hw.norm.pow 2)).add ((hf.norm.pow 2).const_mul 2)).add
    ((hw.inner ((hS.clm_apply hw).add hf)).const_mul (2 * delta))

end Mettapedia.FluidDynamics.NavierStokes.PancakeParametricForcing
