import Mettapedia.Analysis.RankOneCommutator
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPressureCommutator

/-!
# The pressure-tilt Fourier kernel

Each real pressure Hessian mode is a scalar multiple of the wavevector's
rank-one operator. Its commutator depends only on the part of the strain
action not parallel to that wavevector. The exact sum retains the signs
and spatial phases before a separate upper bound takes absolute values.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressureCommutator

open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeInfinitePressureCoefficients
open PancakeSpectralProjectorRegularity SpectralSourceCommutator
open InfiniteFilteredPressure LocalPressureCommutator

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def realFrequency (q : Wavevector) : R3 := WithLp.toLp 2 (fun i ↦ (q i : ℝ))

def pressureModeAmplitude (chi : Wavevector → ℂ) (u : FourierVelocity)
    (q : Wavevector) (x : T3) : ℝ :=
  (UnitAddTorus.mFourier q x * chi q * unitTorusDerivativePhase ^ 2 * infinitePressureCoeff u q).re

theorem realMatrixOperator_rankOne (a : ℂ) (v : R3) :
    realMatrixOperator (fun i j ↦ a * (v i : ℂ) * (v j : ℂ)) =
      a.re • InnerProductSpace.rankOne ℝ v v := by
  ext w i
  simp [realMatrixOperator_apply, smul_apply, InnerProductSpace.rankOne_apply,
    PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum, mul_assoc, mul_comm]

theorem pressure_mode_eq_rankOne (chi : Wavevector → ℂ) (u : FourierVelocity)
    (q : Wavevector) (x : T3) :
    realMatrixOperator (UnitAddTorus.mFourier q x • (chi q • infinitePressureHessianCoeff u q)) =
      pressureModeAmplitude chi u q x • InnerProductSpace.rankOne ℝ (realFrequency q) (realFrequency q) := by
  have h : UnitAddTorus.mFourier q x • (chi q • infinitePressureHessianCoeff u q) =
      fun i j ↦ (UnitAddTorus.mFourier q x * chi q * unitTorusDerivativePhase ^ 2 * infinitePressureCoeff u q) *
        ((realFrequency q i : ℝ) : ℂ) * ((realFrequency q j : ℝ) : ℂ) := by
    ext i j
    simp only [infinitePressureHessianCoeff, Matrix.smul_apply, smul_eq_mul, realFrequency,
      PiLp.toLp_apply, Complex.ofReal_intCast]
    ring
  rw [h, realMatrixOperator_rankOne]
  rfl

theorem filteredPressureOperator_eq_sum (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    filteredPressureOperator chi outputs u x = ∑ q ∈ outputs,
      pressureModeAmplitude chi u q x • InnerProductSpace.rankOne ℝ (realFrequency q) (realFrequency q) := by
  change realMatrixOperatorCLM (∑ q ∈ outputs,
    UnitAddTorus.mFourier q x • (chi q • infinitePressureHessianCoeff u q)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact pressure_mode_eq_rankOne chi u q x

theorem commutator_filteredPressure_eq_sum (S : SymmetricStrain)
    (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (a : Wavevector → ℝ) :
    commutator S (filteredPressureOperator chi outputs u x) = ∑ q ∈ outputs,
      pressureModeAmplitude chi u q x •
        (InnerProductSpace.rankOne ℝ (S.1 (realFrequency q) - a q • realFrequency q) (realFrequency q) -
         InnerProductSpace.rankOne ℝ (realFrequency q) (S.1 (realFrequency q) - a q • realFrequency q)) := by
  rw [filteredPressureOperator_eq_sum, commutator_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [commutator_smul]
  congr 1
  exact InnerProductSpace.rankOne_self_commutator_eq_shifted S.1 (fun v w ↦ (S.2 v w).symm) _ (a q)

theorem norm_commutator_filteredPressure_le (S : SymmetricStrain)
    (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (a : Wavevector → ℝ) :
    ‖commutator S (filteredPressureOperator chi outputs u x)‖ ≤ ∑ q ∈ outputs,
      |pressureModeAmplitude chi u q x| * (2 * ‖realFrequency q‖ *
        ‖S.1 (realFrequency q) - a q • realFrequency q‖) := by
  rw [filteredPressureOperator_eq_sum, commutator_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [commutator_smul, norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact InnerProductSpace.norm_rankOne_self_commutator_le S.1 (fun v w ↦ (S.2 v w).symm) _ (a q)

theorem commutator_filteredPressure_eq_zero_of_eigenvectors (S : SymmetricStrain)
    (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity) (x : T3)
    (a : Wavevector → ℝ)
    (ha : ∀ q ∈ outputs, pressureModeAmplitude chi u q x ≠ 0 →
      S.1 (realFrequency q) = a q • realFrequency q) :
    commutator S (filteredPressureOperator chi outputs u x) = 0 := by
  rw [commutator_filteredPressure_eq_sum S chi outputs u x a]
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hz : pressureModeAmplitude chi u q x = 0
  · rw [hz, zero_smul]
  · rw [ha q hq hz, sub_self]
    simp

end Mettapedia.FluidDynamics.NavierStokes.FourierPressureCommutator
