import Mettapedia.Analysis.OrthonormalOperatorBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTiltEnergy

/-!
# Squared spatial operator norm of the full-pressure Hessian

Parseval is applied to the action on each member of an orthonormal basis.
The basis sum recovers the exact Hessian coefficient weight. There is no
factor counting pressure modes or basis vectors in the final bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressureHessianEnergy

open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeViscousMisalignmentAbsorption PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open PancakeFourierMaterialPaths LocalPressureCommutator FourierPressureCommutator
open FourierPressureTilt FourierPressureTiltEnergy PancakeBoundaryEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def actionCoefficient (chi : Wavevector → ℂ) (u : FourierVelocity) (e : R3) : FourierVelocity :=
  fun q i ↦ pressureAmplitude chi u q * ((⟪realFrequency q, e⟫ * realFrequency q i : ℝ) : ℂ)

def actionEnergy (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) : ℝ :=
  ∑ q ∈ outputs, ‖pressureAmplitude chi u q‖ ^ 2 * ⟪realFrequency q, e⟫ ^ 2 * ‖realFrequency q‖ ^ 2

theorem fullEnergy_actionCoefficient (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) : fullEnergy outputs (actionCoefficient chi u e) =
      actionEnergy chi outputs u e := by
  apply Finset.sum_congr rfl
  intro q _
  change coefficientEnergy (fun i ↦ pressureAmplitude chi u q *
    (((⟪realFrequency q, e⟫ • realFrequency q) i : ℝ) : ℂ)) = _
  rw [coefficientEnergy_real_multiple, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem pressure_apply_eq_real_reconstruction (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) (e : R3) :
    filteredPressureOperator chi outputs u x e =
      complexRealPartEuclidean (finiteFourierReconstruction outputs (actionCoefficient chi u e) x) := by
  rw [filteredPressure_apply_eq_sum]
  ext i
  simp only [WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul,
    complexRealPartEuclidean, PiLp.toLp_apply, finiteFourierReconstruction,
    Finset.sum_apply, Pi.smul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [actionCoefficient, pressureModeAmplitude, pressureAmplitude,
    Complex.ofReal_mul, ← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem integral_pressure_apply_sq_le (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) :
    (∫ x : T3, ‖filteredPressureOperator chi outputs u x e‖ ^ 2) ≤ actionEnergy chi outputs u e := by
  simp_rw [pressure_apply_eq_real_reconstruction]
  rw [← fullEnergy_actionCoefficient]
  exact integral_real_reconstruction_energy_le outputs (actionCoefficient chi u e)

theorem sum_actionEnergy_orthonormalBasis (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (b : OrthonormalBasis (Fin 3) ℝ R3) :
    (∑ j, actionEnergy chi outputs u (b j)) = hessianEnergy chi outputs u := by
  unfold actionEnergy hessianEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Finset.sum_mul, ← Finset.mul_sum, b.sum_sq_inner_left]
  ring

theorem continuous_filteredPressureOperator (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) : Continuous (filteredPressureOperator chi outputs u) :=
  realMatrixOperatorCLM.continuous.comp (PancakeMaterialDiffusionBudget.continuous_matrixReconstruction _ _)

theorem integrable_pressure_norm_sq (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) : Integrable (fun x : T3 ↦ ‖filteredPressureOperator chi outputs u x‖ ^ 2) :=
  ((continuous_filteredPressureOperator chi outputs u).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_pressure_norm_sq_le_hessianEnergy (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) :
    (∫ x : T3, ‖filteredPressureOperator chi outputs u x‖ ^ 2) ≤ hessianEnergy chi outputs u := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hi (j : Fin 3) : Integrable (fun x : T3 ↦ ‖filteredPressureOperator chi outputs u x (b j)‖ ^ 2) :=
    (((continuous_filteredPressureOperator chi outputs u).clm_apply continuous_const).norm.pow 2
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono (integrable_pressure_norm_sq chi outputs u)
    (integrable_finsetSum Finset.univ (fun j _ ↦ hi j))
    (fun x ↦ (filteredPressureOperator chi outputs u x).norm_sq_le_sum_orthonormalBasis b)
  rw [integral_finsetSum _ (fun j _ ↦ hi j)] at h
  exact h.trans ((Finset.sum_le_sum (fun j _ ↦ integral_pressure_apply_sq_le chi outputs u (b j))).trans_eq
    (sum_actionEnergy_orthonormalBasis chi outputs u b))

end Mettapedia.FluidDynamics.NavierStokes.FourierPressureHessianEnergy
