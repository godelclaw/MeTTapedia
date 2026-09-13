import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionStrainWork
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatGeometry
import Mettapedia.Analysis.VorticityJetSourceTests

/-!
# Actual-flow regressions for signed projection work

Every horizontal parallel flow has zero inviscid momentum RHS and zero
subgrid force for any scalar multiplier. The full projection material
work must therefore integrate to zero. These tests use the actual
Fourier fields. The imported compatible-jet sign tests separately guard
against mistaking spatial rotation-flux cancellation for a pointwise sign.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ProjectionMaterialWorkTests

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakeCoefficientLimitEquation PancakePeriodicVorticityEquation PancakeSobolevFiberEnvelope
open LocalLowDiffusionBudget LocalProjectionSourceWork LocalProjectionInviscidWork
open InfiniteFilteredEquation FilteredProjectionSourceSplit ParallelHeatFlow

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fullVorticity_zero (x : T3) : fullVorticity (0 : FourierVelocity) x = 0 := by
  have hz : (fun q ↦ vertical ((0 : Wavevector →₀ ℂ) q)) = (0 : FourierVelocity) := by
    ext q i
    simp
  rw [← hz, fullVorticity_vertical]
  ext i
  fin_cases i <;> simp [scalarGradient, Matrix.cons_val_two]

theorem parallel_inviscidRHS_zero (a : Wavevector → ℂ) (ha : IsHorizontal a) :
    infiniteVelocityRHS 0 (fun q ↦ vertical (a q)) = 0 := by
  funext q
  simp [infiniteVelocityRHS_eq_viscous ha, unitTorusViscousVorticityCoeff]

theorem parallel_subgridForce_zero (χ : Wavevector → ℂ) (a : Wavevector → ℂ)
    (ha : IsHorizontal a) : subgridForce χ (fun q ↦ vertical (a q)) = 0 := by
  have hc (q : Wavevector) : subgridConvection χ (fun q ↦ vertical (a q)) q = 0 := by
    ext i
    simp [subgridConvection, outputFiber_eq_zero ha]
  ext q i
  by_cases hq : modeSquare q = 0 <;> simp [subgridForce, hc, lerayMode, modeDot, hq]

theorem parallel_fullSubgridWork_zero (δ κ : ℝ) (χ : Wavevector → ℂ)
    (a : Wavevector → ℂ) (ha : IsHorizontal a) :
    fullSubgridWork δ κ χ (fun q ↦ vertical (a q)) = 0 := by
  simp [fullSubgridWork, parallel_subgridForce_zero χ a ha, fullVorticity_zero]

/-- This is zero total inviscid projection work for actual fields, not
zero of every individual material-rate component. -/
theorem parallel_integral_projectionMaterialRate_zero (δ : ℝ) (hδ : 0 < δ)
    (a : Wavevector →₀ ℂ) (ha : IsHorizontal a) (hr : ∀ q, a (-q) = conj (a q)) :
    (∫ x : T3, projectionMaterialRate δ (fun q ↦ vertical (a q)) x) = 0 := by
  have hre (q : Wavevector) : vertical (a (-q)) = coefficientConjugate (vertical (a q)) := by
    rw [hr, vertical_conj]
  have h := integral_correctedGradient_inviscidRHS δ 3 hδ _
    (summable_initial_fourierMoment 5 a) (transverse ha) hre
  rw [parallel_inviscidRHS_zero a ha, stretching_eq_zero a ha] at h
  simp only [fullVorticity_zero, inner_zero_right, integral_zero] at h
  norm_num at h
  linarith only [h]

/-- Changing the rotation coefficient destroys the cancellation. -/
theorem rotation_coefficient_mismatch (κ : ℝ) (hκ : κ ≠ 0) (c : ℝ) :
    -(3 / κ) * (c / 4) - ((-3 / 4) * c) / κ = 0 ∧
      -(3 / κ) * (c / 4) - ((-3 / 2) * c) / κ = 3 * c / (4 * κ) := by
  constructor <;> field_simp <;> ring

end Mettapedia.FluidDynamics.NavierStokes.ProjectionMaterialWorkTests
