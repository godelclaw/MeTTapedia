import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityWeightedStretching
import Mettapedia.Analysis.SignedCrossKernelTests

/-! Actual-field, zero-mode and sign regressions for the signed stretching representation. -/

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFourierPressureStrain PancakeCurlOutputTail
open PancakeGalerkinKineticEnergy
open PancakeBlockReality PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open VorticityStretchingKernel VorticityWeightedStretching
open Mettapedia.Analysis.SignedCrossKernel Mettapedia.Analysis.EuclideanCrossProduct

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

example (u : FourierVelocity) (w : VelocityCoefficient) :
    unitTorusStrainStretchAmp 0 (fourierCurl u 0) w = (strainCoeff u 0).mulVec w :=
  strainStretch_fourierCurl 0 u w (by simp [modeDot])

example (a : R3) : projectionSymbol 0 a = 0 := by
  have hz : FourierPressureCommutator.realFrequency 0 = (0 : R3) := by
    ext i
    simp [FourierPressureCommutator.realFrequency]
  simp [projectionSymbol_apply, hz]

example (modes : Finset Wavevector) (x y : T3) :
    kernel modes (y - x) = kernel modes (x - y) := kernel_sub_swap modes x y

example (n : ℕ) (u : FourierVelocity) : pairedIntegral n ∅ u = 0 := by
  simp [pairedIntegral, pairedStretch, kernel]

example (n : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    Tendsto (fun modes : Finset Wavevector ↦ pairedIntegral n modes u)
      atTop (𝓝 (fullStretching n u)) :=
  tendsto_pairedIntegral n u (summable_fourierMoment_of_le u (by norm_num : 1 ≤ 3) hu) hr hd

example {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (t : ℝ) (hu : Summable (fourierMoment 3 (s.coefficients t))) :
    Tendsto (fun modes : Finset Wavevector ↦ pairedIntegral 6 modes (s.coefficients t))
      atTop (𝓝 (LocalVorticityEighthMoment.stretching (s.coefficients t))) :=
  tendsto_eighthMoment_pair _ (summable_fourierMoment_of_le _ (by norm_num : 1 ≤ 3) hu)
    (s.reality t) (s.transverse t)

example :
    ⟪cross (WithLp.toLp 2 ![(1 : ℝ), 0, 1]) (WithLp.toLp 2 ![0, 1, 0]),
      (WithLp.toLp 2 ![1, 0, 0] : R3)⟫ = -1 := by
  simp only [cross, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, dotProduct, Fin.sum_univ_three]
  change (1 * (0 * 0 - 1 * 1) + 0 * (1 * 0 - 1 * 0) +
    0 * (1 * 1 - 0 * 0) : ℝ) = -1
  norm_num

#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel.projectionSymbol_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel.kernel_sub_swap
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel.coefficientDot_quadraticSymbol
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel.integral_character_sub_vorticity
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel.integral_real_character_inner
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel.strainStretch_fourierCurl
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel.integral_singleMode_stretch
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel.integral_kernel_stretch
#print axioms Mettapedia.FluidDynamics.NavierStokes.FullStrainFourierSeries.summable_norm_strainCoeff
#print axioms Mettapedia.FluidDynamics.NavierStokes.FullStrainFourierSeries.hasSum_strain_matrix
#print axioms Mettapedia.FluidDynamics.NavierStokes.FullStrainFourierSeries.fullStrainOperator_eq_fourierSeries
#print axioms Mettapedia.FluidDynamics.NavierStokes.FullStrainFourierSeries.tendsto_spatialStrain
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityWeightedStretching.finiteStretching_eq_pair
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityWeightedStretching.tendsto_finiteStretching
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityWeightedStretching.tendsto_pairedIntegral
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityWeightedStretching.tendsto_eighthMoment_pair
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityWeightedStretching.fullStretching_eq_zero_of_collinear
