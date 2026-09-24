import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputReconstruction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalJointSourceTilt

/-!
# Fixed-output pressure in the actual pointwise joint source

The finite output set is constructed from the filter. The pressure action
uses both full vorticity fields and no external output filter. The exact
identity retains the complementary pressure, spin, raw subgrid, and
transport terms before any norm estimate is taken.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputJointSource

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakeSpatialStrainEvolution PancakeAnisotropyDepletion PancakeSpectralFiniteDifference
open PancakeSobolevFiberEnvelope PancakeBlockReality PancakeCurlOutputTail
open PancakeInfiniteVelocityEnvelope PancakeHigherDerivativeMoments PancakeTransverseEnergyFreezing
open LocalAlignmentForcing LocalPressureCommutator LocalJointSourceTilt LocalSourceCommutator
open FourierPressureCommutator FourierPressureTilt GaussianRootOperatorBudget
open PressureFixedOutputSymbol PressureFixedOutputAction PressureFixedOutputReconstruction

local notation "T3" => UnitAddTorus (Fin 3)

theorem norm_outputMultiplier_complex_le (N : ℝ) (q : Wavevector) :
    ‖(outputMultiplier N q : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (outputMultiplier_nonneg N q)]
  exact outputMultiplier_le_one N q

theorem jointTilt_eq_fixed_output (N : ℝ) (hN : 0 < N) (j : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (x : T3) :
    let chi := fun q ↦ (outputMultiplier N q : ℂ)
    let modes := outputModes N
    let hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu
    let e := topVector (spatialStrain modes (filteredVelocity chi u) x)
    let W := spatialSpin modes (filteredVelocity chi u) x
    jointTilt chi modes modes u x =
      lineRemainder e (-(W (W e)) + rawSubgridOperator chi modes u x e +
        transportOperator chi modes modes u x e) -
      complexRealPartEuclidean (WithLp.ofLp
        (-operator N hN j e (complexVorticityField u hu1) (complexVorticityField u hu1) x -
          complementField N j e u x)) := by
  have hconv (q : Wavevector) (i : Fin 3) : Summable (fun k ↦ outputFiber q u k i) :=
    ((summable_pairEnvelope (fourierMoment 2 u) (fourierMoment_nonneg _ _) hu).prod_factor q).of_norm_bounded
      (fun k ↦ norm_outputFiber_le_momentEnvelope u (fourierMoment 2 u)
        (fourierMoment_nonneg _ _) (fun _ ↦ le_rfl) q k i)
  have hs (q : Wavevector) (hq : q ∉ outputModes N) : (outputMultiplier N q : ℂ) = 0 := by
    rw [outputMultiplier_eq_zero_of_not_mem N hN q hq, Complex.ofReal_zero]
  dsimp only
  rw [jointTilt_eq_pressure_kernel _ u 1 (norm_outputMultiplier_complex_le N)
    (outputModes N) (outputModes N) hs hd hconv x,
    ← transverse_filteredPressure_eq_sum,
    transverse_pressure_eq N hN j _ (topVector_norm _) u hu
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) hr hd x]

end Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputJointSource
