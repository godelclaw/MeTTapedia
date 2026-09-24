import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPhysicalIdentification
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicJointSource

/-! Full-field coefficient identification, zero output, and retained annular weights. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicReconstructionAudit

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator FourierPressureTraceSymbol
open PressureDyadicFourierReconstruction PressureDyadicBilinearAction PressureBilinearOperator
open PressureDyadicPhysicalIdentification PressureOperatorCoordinates
open PancakeInfiniteFourierDerivative PancakeFourierTranslationCurve
open ComplexPressurePair PressureTiltSymbol PancakeAnisotropyDepletion
open Mettapedia.Analysis.UnitTorusContinuousFourier Mettapedia.Analysis.DyadicAnnulus
open Mettapedia.Analysis.EuclideanBilinearCoordinates Mettapedia.Analysis.EuclideanCrossProduct
open scoped RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

private theorem output_small : ‖realFrequency ![3, 4, 0]‖ ≤ (1280 : ℝ) / 256 := by
  have h : ‖realFrequency ![3, 4, 0]‖ ^ 2 = 25 := by
    norm_num [realFrequency, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  norm_num only
  nlinarith [norm_nonneg (realFrequency ![3, 4, 0])]

private theorem input_half : normalizedCutoff ((1280 : ℝ)⁻¹ • realFrequency ![1280, 0, 0]) = 1 / 2 := by
  apply normalizedCutoff_eq_half_of_norm_eq_one
  have he : (1280 : ℝ)⁻¹ • realFrequency ![1280, 0, 0] = EuclideanSpace.single 0 (1 : ℝ) := by
    ext i
    fin_cases i <;> norm_num [realFrequency]
  rw [he]
  simp

private theorem pair_entry :
    entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2 = (-192 / 40768625 : ℂ) := by
  rw [entry_pressurePairOperator]
  norm_num [CoherentPressurePair.tiltPair, CoherentPressurePair.tracePair, tiltSymbol,
    lineRemainder, cross, cross_apply, realFrequency, EuclideanSpace.norm_sq_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- The reconstructed low output retains the half-weight on the input annulus. -/
example : (coefficientCLM ![3, 4, 0]
    (sumOperator 1280 (by norm_num) (EuclideanSpace.single 0 1)
      (modeField ![1280, 0, 0] (EuclideanSpace.single 2 (1 : ℂ)))
      (modeField ![-1277, 4, 0] (EuclideanSpace.single 2 (1 : ℂ))))) 1 =
      (-96 / 40768625 : ℂ) := by
  rw [coefficient_sumOperator_modes_low _ _ _ (by simp) _ output_small]
  have hq : (![3, 4, 0] : Wavevector) = ![1280, 0, 0] + ![-1277, 4, 0] := by
    ext i
    fin_cases i <;> norm_num
  rw [if_pos hq, input_half]
  change ((1 / 2 : ℝ) : ℂ) * entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
    ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2 = _
  rw [pair_entry]
  norm_num

/-- Its complementary half is nonzero: a single annulus is not the whole pressure. -/
example : (1 - (normalizedCutoff ((1280 : ℝ)⁻¹ • realFrequency ![1280, 0, 0]) : ℂ)) *
    entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2 ≠ 0 := by
  rw [input_half, pair_entry]
  norm_num

/-- The full reconstructed field has zero pressure-tilt mode at zero output. -/
example (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1)
    (a b : Wavevector → C3) (ha : Summable (fun k ↦ ‖a k‖))
    (hb : Summable (fun k ↦ ‖b k‖)) :
    UnitAddTorus.mFourierCoeff
      (PressureDyadicAction.sumAction N hN e (fullFourierField id a) (fullFourierField id b)) 0 = 0 := by
  have hz : realFrequency (0 : Wavevector) = 0 := by ext i; simp [realFrequency]
  have hcz : complexTiltSymbol e (0 : Wavevector) = 0 := by
    rw [complexTiltSymbol, hz, tiltSymbol_zero]
    rfl
  rw [mFourierCoeff_sumAction_low N hN e he a b ha hb 0 (by rw [hz, norm_zero]; positivity)]
  simp [pressurePairOperator_apply, tiltPair, hcz]

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicReconstructionAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureContinuousBilinearAction.fieldAction_add_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureContinuousBilinearAction.fieldAction_smul_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureContinuousBilinearAction.fieldAction_add_right
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureContinuousBilinearAction.fieldAction_smul_right
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureContinuousBilinearAction.norm_bilinearAction_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicBilinearAction.exists_uniform_operator_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicBilinearAction.sumOperator_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicBilinearAction.exists_uniform_sumOperator_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicFourierReconstruction.bandOperator_modes
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicFourierReconstruction.coefficient_sumOperator_modes_low
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicFourierReconstruction.hasSum_sumOperator_fourierPairs
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicFourierReconstruction.mFourierCoeff_sumAction_low
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalIdentification.complexVorticityField_eq_fullFourierField
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalIdentification.mFourierCoeff_sumAction_vorticity_low
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalIdentification.summable_norm_curlTiltPair
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalIdentification.annular_add_complementaryTiltCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalIdentification.tiltCoefficient_eq_sumAction_add_complement
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalIdentification.transverse_pressure_eq_dyadic_decomposition
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicJointSource.jointTilt_eq_dyadic_decomposition
