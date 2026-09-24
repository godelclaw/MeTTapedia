import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootDirectionFreezing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureHighInputFourier

/-! Exact secants, direction reversal, and nonzero direction-sensitive output tests. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDirectionAudit

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator FourierPressureTraceSymbol
open PressureFixedOutputSymbol PressureHighInputAction PressureHighInputFourier
open PressureOperatorCoordinates PressureBilinearOperator ComplexPressurePair PressureTiltSymbol
open PancakeAnisotropyDepletion PancakeInfiniteFourierDerivative PancakeFourierTranslationCurve
open Mettapedia.Analysis.UnitTorusContinuousFourier
open Mettapedia.Analysis.EuclideanBilinearCoordinates Mettapedia.Analysis.EuclideanCrossProduct
open scoped RealInnerProductSpace SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

/-- The secant is exact across a non-infinitesimal direction change. -/
example (t : ℝ) (e w v : R3) (i : Fin 3) :
    PressureDyadicSymbol.symbol (t, (3 : ℝ) • e) w v i - PressureDyadicSymbol.symbol (t, e) w v i =
      (2 : ℝ) • PressureDirectionSecant.symbol (t, (3 : ℝ) • e, e, e) w v i := by
  apply PressureDirectionSecant.symbol_sub_eq_smul
  module

example (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) (u v : C(T3, C3)) (x : T3) :
    tailOperator N hN J (-e) u v x = -tailOperator N hN J e u v x := by
  rw [PressureDirectionParity.tailOperator_neg]
  rfl

private theorem transition_half : outputMultiplier 640 ![3, 4, 0] = 1 / 2 := by
  apply Mettapedia.Analysis.DyadicLowPass.multiplier_eq_half_of_norm_eq_two
  have h : ‖(256 / 640 : ℝ) • realFrequency ![3, 4, 0]‖ ^ 2 = 4 := by
    norm_num [realFrequency, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  nlinarith [norm_nonneg ((256 / 640 : ℝ) • realFrequency ![3, 4, 0])]

private theorem high_one : inputMultiplier 640 0 ![1280, 0, 0] = 1 := by
  apply Mettapedia.Analysis.DyadicHighPass.multiplier_eq_one_of_le_norm
  have he : (inputScale 640 0)⁻¹ • realFrequency ![1280, 0, 0] =
      EuclideanSpace.single 0 (2 : ℝ) := by
    ext i
    fin_cases i <;> norm_num [inputScale, realFrequency]
  rw [he]
  norm_num

private theorem pair_entry (j : Fin 3) :
    entry (pressurePairOperator (EuclideanSpace.single j 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2 =
      if j = 0 then (-192 / 40768625 : ℂ) else 0 := by
  rw [entry_pressurePairOperator]
  fin_cases j <;>
    norm_num [CoherentPressurePair.tiltPair, CoherentPressurePair.tracePair, tiltSymbol,
      lineRemainder, cross, cross_apply, realFrequency, EuclideanSpace.norm_sq_eq,
      PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

private theorem coefficient_direction (j : Fin 3) :
    (coefficientCLM ![3, 4, 0]
      (tailOperator 640 (by norm_num) 0 (EuclideanSpace.single j 1)
        (modeField ![1280, 0, 0] (EuclideanSpace.single 2 (1 : ℂ)))
        (modeField ![-1277, 4, 0] (EuclideanSpace.single 2 (1 : ℂ))))) 1 =
        (1 / 2 : ℂ) * if j = 0 then (-192 / 40768625 : ℂ) else 0 := by
  rw [coefficient_tailOperator_modes _ _ _ _ (by simp)]
  have hq : (![3, 4, 0] : Wavevector) = ![1280, 0, 0] + ![-1277, 4, 0] := by
    ext i
    fin_cases i <;> norm_num
  rw [if_pos hq, transition_half, high_one]
  change ((1 / 2 : ℝ) : ℂ) * ((1 : ℂ) *
    entry (pressurePairOperator (EuclideanSpace.single j 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2) = _
  rw [pair_entry]
  norm_num

/-- Changing the direction changes a nonzero reconstructed Fourier output. -/
example :
    (coefficientCLM ![3, 4, 0] (tailOperator 640 (by norm_num) 0 (EuclideanSpace.single 0 1)
      (modeField ![1280, 0, 0] (EuclideanSpace.single 2 (1 : ℂ)))
      (modeField ![-1277, 4, 0] (EuclideanSpace.single 2 (1 : ℂ))))) 1 -
    (coefficientCLM ![3, 4, 0] (tailOperator 640 (by norm_num) 0 (EuclideanSpace.single 2 1)
      (modeField ![1280, 0, 0] (EuclideanSpace.single 2 (1 : ℂ)))
      (modeField ![-1277, 4, 0] (EuclideanSpace.single 2 (1 : ℂ))))) 1 =
      (-96 / 40768625 : ℂ) := by
  rw [coefficient_direction, coefficient_direction]
  norm_num [show (2 : Fin 3) ≠ 0 by decide]

example :
    (coefficientCLM ![3, 4, 0] (tailOperator 640 (by norm_num) 0 (EuclideanSpace.single 1 1)
      (modeField ![1280, 0, 0] (EuclideanSpace.single 2 (1 : ℂ)))
      (modeField ![-1277, 4, 0] (EuclideanSpace.single 2 (1 : ℂ))))) 1 =
      (0 : ℂ) := by
  rw [coefficient_direction]
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.PressureDirectionAudit

#print axioms Mettapedia.Analysis.SchwartzBilinearKernel.assemble_sub
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionSecant.symbol_sub_eq_smul
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionSecant.contDiff_symbol
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionSecant.tsupport_symbol_subset
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionSecant.exists_uniform_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionKernel.kernel_sub_eq_smul
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionKernel.exists_uniform_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionKernel.exists_uniform_basis_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionKernel.exists_uniform_scaled_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionKernel.exists_uniform_scaled_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodizationLinearity.ae_summable_norm_orbit
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodizationLinearity.periodize_sub_ae
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionOperatorKernel.moment_operatorKernel_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionOperatorKernel.exists_uniform_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionOperatorKernel.exists_uniform_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionOperatorKernel.moment_periodicKernel_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionOperatorKernel.exists_uniform_periodic_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureContinuousBilinearAction.bilinearAction_congr_ae
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureContinuousBilinearAction.bilinearAction_sub_kernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionAction.exists_uniform_band_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionAction.exists_uniform_fixed_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionAction.exists_uniform_tail_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionAction.exists_uniform_field_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionParity.symbol_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionParity.scaledKernel_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionParity.operatorKernel_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionParity.periodicKernel_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionParity.bandOperator_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionParity.operator_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionParity.tailOperator_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDirectionFreezing.exists_uniform_weighted_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootDirectionFreezing.exists_local_root_transfer
