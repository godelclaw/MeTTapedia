import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootMovingPressureBudget

/-! Collision, zero-vorticity, and actual moving-field integrability checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureMovingEnergyAudit

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeFourierMaterialPaths
open PancakeFilteredStrainDynamics PressureMovingDirectionEnergy PressureHighInputLocalization
open LocalLowDiffusionBudget
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (N : ℝ) (hN : 0 < N) (J : ℕ) (gamma : ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (f g : C(T3, C3)) (x : T3)
    (hw : fullVorticity u x = 0) : energy N hN J gamma chi modes u f g x = 0 :=
  energy_eq_zero_of_vorticity_eq_zero N hN J gamma chi modes u f g x hw

/-- The closed cutoff boundary is included; no simple top eigenvalue is assumed. -/
example (N : ℝ) (hN : 0 < N) (J : ℕ) (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (f g : C(T3, C3)) (x : T3) (hgap : topGap (spatialStrain modes (filteredVelocity chi u) x) = gamma) :
    energy N hN J gamma chi modes u f g x = 0 :=
  energy_eq_zero_of_topGap_le N hN J gamma hg chi modes u f g x hgap.le

example (N : ℝ) (hN : 0 < N) (J : ℕ) (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (f g : C(T3, C3)) :
    Integrable (energy N hN J gamma chi modes u f g) :=
  integrable_energy N hN J gamma hg chi modes u hu f g

example (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) (f g : C(T3, C3)) (x : T3) :
    ‖PressureHighInputAction.tailOperator N hN J e f g x‖ ^ 2 ≤
      2 * ‖PressureHighInputAction.tailOperator N hN J e f g x‖ ^ 2 := by
  have h := norm_weighted_action_sq_le N hN J e f g 1 1 x
  have hone (v : C(T3, C3)) : (1 : C(T3, ℂ)) • v = v := by
    apply ContinuousMap.ext
    intro y
    change (1 : ℂ) • v y = v y
    exact one_smul ℂ (v y)
  have hz : tailLocalization N hN J e f g 1 1 = 0 := by
    simp only [tailLocalization, one_mul, hone, sub_self]
  simpa only [hz, ContinuousMap.one_apply, ContinuousMap.zero_apply, norm_one, one_pow,
    one_mul, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, hone] using h

end Mettapedia.FluidDynamics.NavierStokes.PressureMovingEnergyAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureMovingDirectionEnergy.continuous_localAmplitude
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureMovingDirectionEnergy.continuous_weighted_norm
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureMovingDirectionEnergy.energy_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureMovingDirectionEnergy.energy_eq_zero_of_vorticity_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureMovingDirectionEnergy.energy_eq_zero_of_topGap_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureMovingDirectionEnergy.continuous_energy
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureMovingDirectionEnergy.integrable_energy
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureHighInputLocalization.norm_weighted_action_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootMovingPressureBudget.exists_local_root_budget
