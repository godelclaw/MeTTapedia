import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPhysicalIdentification
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalJointSourceTilt

/-!
# Exact dyadic pressure decomposition in the joint alignment source

The pressure/subgrid cancellation is performed by the actual filtered
strain identity before inserting the dyadic kernel. Spin, raw subgrid,
transport, the output filter, and the complementary input sector all
remain in the signed equality. No dynamical budget is assumed or concluded.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicJointSource

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakeSpatialStrainEvolution PancakeAnisotropyDepletion PancakeSpectralFiniteDifference
open PancakeSobolevFiberEnvelope PancakeBlockReality PancakeCurlOutputTail
open PancakeInfiniteVelocityEnvelope PancakeHigherDerivativeMoments PancakeTransverseEnergyFreezing
open LocalAlignmentForcing LocalPressureCommutator LocalJointSourceTilt LocalSourceCommutator
open FourierPressureCommutator FourierPressureTilt PressureTwoInputReconstruction
open GaussianRootOperatorBudget PressureDyadicPhysicalIdentification

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

theorem jointTilt_eq_dyadic_decomposition (N : ℝ) (hN : 0 < N)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes outputs : Finset Wavevector) (hs : ∀ k, k ∉ modes → chi k = 0)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (houtputs : ∀ q ∈ outputs, ‖realFrequency q‖ ≤ N / 256) (x : T3) :
    let hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu
    let e := topVector (spatialStrain modes (filteredVelocity chi u) x)
    let W := spatialSpin modes (filteredVelocity chi u) x
    jointTilt chi modes outputs u x =
      lineRemainder e (-(W (W e)) + rawSubgridOperator chi outputs u x e +
        transportOperator chi modes outputs u x e) -
      complexRealPartEuclidean (WithLp.ofLp (vectorPolynomial outputs
        (fun q ↦ (-chi q) • (UnitAddTorus.mFourierCoeff (PressureDyadicAction.sumAction N hN e
          (complexVorticityField u hu1) (complexVorticityField u hu1)) q +
            complementaryTiltCoefficient N e u q)) x)) := by
  have hconv (q : Wavevector) (i : Fin 3) : Summable (fun k ↦ outputFiber q u k i) :=
    ((summable_pairEnvelope (fourierMoment 2 u) (fourierMoment_nonneg _ _) hu).prod_factor q).of_norm_bounded
      (fun k ↦ norm_outputFiber_le_momentEnvelope u (fourierMoment 2 u)
        (fourierMoment_nonneg _ _) (fun _ ↦ le_rfl) q k i)
  dsimp only
  rw [jointTilt_eq_pressure_kernel chi u C hchi modes outputs hs hd hconv x,
    ← transverse_filteredPressure_eq_sum,
    transverse_pressure_eq_dyadic_decomposition N hN chi outputs _ (topVector_norm _)
      u hu (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) hr hd houtputs x]

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicJointSource
