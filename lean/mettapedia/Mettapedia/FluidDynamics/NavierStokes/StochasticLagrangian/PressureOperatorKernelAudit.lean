import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputOperatorBudget

/-! Complex-phase and physical-symbol regressions for low-output pressure operators. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureOperatorKernelAudit

open Mettapedia.Analysis.EuclideanBilinearCoordinates
open Mettapedia.Analysis.EuclideanCrossProduct
open PeriodicFourierTriad FourierPressureCommutator
open PressureBilinearOperator PressureOperatorCoordinates PressureLowOutputOperatorKernel
open PressureLowOutputSymbol PressureLowOutputPhysicalKernel
open PressureTiltSymbol PancakeAnisotropyDepletion
open scoped RealInnerProductSpace FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

/-- The Fourier identification acts on arbitrary complex vectors. -/
example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) (w v : C3) :
    (𝓕 (operatorKernel N hN t e)) (pairEquiv.symm (realFrequency k, realFrequency p)) w v =
      (physicalCutoff t (N⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) : ℂ) •
        pressurePairOperator e he k p w v := by
  rw [fourier_operatorKernel N hN t e he]
  simp

/-- Two imaginary inputs reverse the sign of the real low-output pressure entry. -/
example :
    (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![256, 0, 0] ![-255, 1, 0]
      (Complex.I • EuclideanSpace.single 2 1) (Complex.I • EuclideanSpace.single 2 1)) 1 =
      (1 / 130052 : ℂ) := by
  simp only [map_smul, smul_apply, smul_smul, Complex.I_mul_I, neg_one_smul, PiLp.neg_apply]
  change -Mettapedia.Analysis.EuclideanBilinearCoordinates.entry
    (pressurePairOperator (EuclideanSpace.single 0 1) (by simp) ![256, 0, 0] ![-255, 1, 0]) 1 2 2 = _
  rw [entry_pressurePairOperator]
  norm_num [CoherentPressurePair.tiltPair, CoherentPressurePair.tracePair, tiltSymbol,
    lineRemainder, cross, cross_apply, realFrequency, EuclideanSpace.norm_sq_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- A single imaginary input multiplies the output by i, not by its conjugate. -/
example (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) (w v : C3) :
    pressurePairOperator e he k p (Complex.I • w) v =
      Complex.I • pressurePairOperator e he k p w v := by simp

/-- Opposite lattice inputs have identically zero pressure symbol. -/
example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (he : ‖e‖ = 1)
    (k : Wavevector) :
    (𝓕 (operatorKernel N hN t e)) (pairEquiv.symm (realFrequency k, realFrequency (-k))) = 0 := by
  rw [fourier_operatorKernel N hN t e he]
  have hz : pressurePairOperator e he k (-k) = 0 := by
    apply Mettapedia.Analysis.EuclideanBilinearCoordinates.ext_basis
    intro j l
    ext i
    change Mettapedia.Analysis.EuclideanBilinearCoordinates.entry
      (pressurePairOperator e he k (-k)) i j l = 0
    rw [entry_pressurePairOperator]
    have hneg : realFrequency (-k) = -realFrequency k := by
      ext r
      simp [realFrequency]
    simp [CoherentPressurePair.tiltPair, hneg, tiltSymbol_zero]
  rw [hz, smul_zero]

end Mettapedia.FluidDynamics.NavierStokes.PressureOperatorKernelAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureOperatorCoordinates.ofLp_single_eq_realCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureOperatorCoordinates.entry_pressurePairOperator
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureOperatorCoordinates.reconstruct_pressurePairOperator
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputOperatorKernel.fourier_operatorKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputOperatorKernel.moment_operatorKernel_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputOperatorKernel.exists_uniform_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputOperatorKernel.exists_uniform_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputOperatorBudget.exists_uniform_mass_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputOperatorBudget.exists_uniform_firstMoment_budget
