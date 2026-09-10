import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSourceCommutator
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFilteredPressure

/-!
# Joint pressure and subgrid source of the actual filtered strain

Resolved pressure is canceled against the pressure correction in the
projected subgrid force. The resulting pressure belongs to the full
velocity, with the filter applied only to its output. The remaining
unprojected force still contains all unresolved interactions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalPressureCommutator

open scoped Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFilteredStrainDynamics PancakeFourierPressureStrain PancakeFourierMaterialPaths
open PancakeSpatialStrainEvolution PancakeSobolevFiberEnvelope PancakeLocalInfiniteVelocity
open LocalSourceCommutator LocalAlignmentForcing SpectralSourceCommutator InfiniteFilteredPressure

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def filteredPressureOperator (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  realMatrixOperator (matrixReconstruction outputs (fun q ↦ chi q • infinitePressureHessianCoeff u q) x)

def rawSubgridOperator (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 →L[ℝ] R3 :=
  realMatrixOperator (matrixReconstruction outputs (strainCoeff (rawSubgridForce chi u)) x)

theorem pressure_subgrid_balance
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes outputs : Finset Wavevector) (hs : ∀ k, k ∉ modes → chi k = 0)
    (hd : ∀ k, modeDot k (u k) = 0)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) (x : T3) :
    -pressureOperator chi modes outputs u x + subgridOperator chi outputs u x =
      -filteredPressureOperator chi outputs u x + rawSubgridOperator chi outputs u x := by
  have h : (fun q ↦ -pressureHessianCoeff modes (filteredVelocity chi u) q +
      strainCoeff (InfiniteFilteredEquation.subgridForce chi u) q) =
      (fun q ↦ -(chi q • infinitePressureHessianCoeff u q) + strainCoeff (rawSubgridForce chi u) q) := by
    funext q
    exact resolvedPressure_subgridStrain_balance chi u C hchi modes hs hd hu q
  have h' := congrArg (fun A ↦ realMatrixOperator (matrixReconstruction outputs A x)) h
  simpa only [matrixReconstruction_add, matrixReconstruction_neg, realMatrixOperator_add,
    realMatrixOperator_neg, pressureOperator, subgridOperator, filteredPressureOperator,
    rawSubgridOperator] using h'

theorem nonviscousRemainder_eq_joint
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes outputs : Finset Wavevector) (hs : ∀ k, k ∉ modes → chi k = 0)
    (hd : ∀ k, modeDot k (u k) = 0)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) (x : T3) :
    nonviscousRemainder chi modes outputs u x =
      -(spatialSpin modes (filteredVelocity chi u) x * spatialSpin modes (filteredVelocity chi u) x) -
      filteredPressureOperator chi outputs u x + rawSubgridOperator chi outputs u x +
      transportOperator chi modes outputs u x := by
  rw [nonviscousRemainder_eq]
  have h := pressure_subgrid_balance chi u C hchi modes outputs hs hd hu x
  calc
    _ = -(spatialSpin modes (filteredVelocity chi u) x * spatialSpin modes (filteredVelocity chi u) x) +
        (-pressureOperator chi modes outputs u x + subgridOperator chi outputs u x) +
        transportOperator chi modes outputs u x := by abel
    _ = _ := by rw [h]; abel

theorem sourceCommutator_eq_joint
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes outputs : Finset Wavevector) (hs : ∀ k, k ∉ modes → chi k = 0)
    (hd : ∀ k, modeDot k (u k) = 0)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    let W := spatialSpin modes (filteredVelocity chi u) x
    sourceCommutator chi modes outputs u x =
      -(commutator S W * W + W * commutator S W) -
      commutator S (filteredPressureOperator chi outputs u x) +
      commutator S (rawSubgridOperator chi outputs u x) +
      commutator S (transportOperator chi modes outputs u x) := by
  dsimp only
  rw [sourceCommutator, nonviscousRemainder_eq_joint chi u C hchi modes outputs hs hd hu x]
  simp only [sub_eq_add_neg, commutator_add, commutator_neg, commutator_mul]

theorem sourceCommutator_eq_joint_of_localSolution {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes outputs : Finset Wavevector) (hs : ∀ k, k ∉ modes → chi k = 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (x : T3) :
    let u := s.coefficients t
    let S := spatialStrain modes (filteredVelocity chi u) x
    let W := spatialSpin modes (filteredVelocity chi u) x
    sourceCommutator chi modes outputs u x =
      -(commutator S W * W + W * commutator S W) -
      commutator S (filteredPressureOperator chi outputs u x) +
      commutator S (rawSubgridOperator chi outputs u x) +
      commutator S (transportOperator chi modes outputs u x) :=
  sourceCommutator_eq_joint chi (s.coefficients t) C hchi modes outputs hs
    (s.transverse t) (s.summable_convection t ht) x

end Mettapedia.FluidDynamics.NavierStokes.LocalPressureCommutator
