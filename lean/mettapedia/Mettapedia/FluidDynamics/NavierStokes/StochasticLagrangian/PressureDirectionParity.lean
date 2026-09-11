import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureHighInputAction

/-! Reversing a pressure direction reverses the actual bilinear field action. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDirectionParity

open MeasureTheory PressureDyadicSymbol PressureDyadicKernel PressureDyadicPhysicalKernel
open PressureDyadicOperatorKernel PressureDyadicPeriodization PressureDyadicBilinearAction
open PressureContinuousBilinearAction PressureFixedOutputAction PressureHighInputAction
open PressureKernelAction (kernelAction)
open PancakeBilinearPeriodization FrequencyPairPeriodization
open Mettapedia.Analysis.SchwartzBilinearKernel Mettapedia.Analysis.EuclideanBilinearCoordinates
open Mettapedia.Analysis.SchwartzLinearChange Mettapedia.Analysis.SchwartzDilation
open Mettapedia.Analysis.FundamentalDomainPeriodization
open scoped SchwartzMap FourierTransform RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Field" => C(T3, C3)
local notation "FieldOp" => Field →L[ℂ] Field →L[ℂ] Field
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Field →L[ℂ] Field) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (Field →L[ℂ] Field) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup FieldOp := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ FieldOp := ContinuousLinearMap.toNormedSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem symbol_neg (t : ℝ) (e w v : R3) (i : Fin 3) :
    symbol (t, -e) w v i = -symbol (t, e) w v i := by
  ext x
  simp [symbol_apply, PressureDyadicSymbol.entry, PressureLowOutputSymbol.entry]
  ring

theorem kernel_neg (t : ℝ) (e w v : R3) (i : Fin 3) :
    kernel (t, -e) w v i = -kernel (t, e) w v i := by
  rw [kernel, symbol_neg, FourierTransform.fourierInv_neg]
  rfl

theorem scaledKernel_neg (N : ℝ) (hN : 0 < N) (t : ℝ) (e w v : R3) (i : Fin 3) :
    scaledKernel N hN (t, -e) w v i = -scaledKernel N hN (t, e) w v i := by
  by_cases h : PressureLowOutputCutoff.ratio t = 0
  all_goals
    ext x
    simp [scaledKernel, dilate, physicalKernel, retainedKernel, kernel_neg, pullback_apply, h]

theorem operatorKernel_neg (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) :
    operatorKernel N hN t (-e) = -operatorKernel N hN t e := by
  ext x
  simp [operatorKernel, assemble_apply, scaledKernel_neg, reconstruct, neg_smul, Finset.sum_neg_distrib]

theorem periodicKernel_neg (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (q : T6) :
    periodicKernel N hN t (-e) q = -periodicKernel N hN t e q := by
  simp [periodicKernel, operatorKernel_neg, periodize, addPeriodization, tsum_neg]

theorem bandOperator_neg (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) :
    bandOperator N hN t (-e) = -bandOperator N hN t e := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro g
  apply ContinuousMap.ext
  intro x
  change (∫ q : T6, periodicKernel N hN t (-e) q (f (x - firstTorusDisplacement q))
    (g (x - secondTorusDisplacement q))) = _
  simp only [periodicKernel_neg, neg_apply]
  exact integral_neg _

theorem operator_neg (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3) :
    operator N hN j (-e) = -operator N hN j e := by
  simp only [operator, bandOperator_neg, tsum_neg]

theorem tailOperator_neg (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) :
    tailOperator N hN J (-e) = -tailOperator N hN J e := by
  simp only [tailOperator, operator_neg, tsum_neg]

end Mettapedia.FluidDynamics.NavierStokes.PressureDirectionParity
