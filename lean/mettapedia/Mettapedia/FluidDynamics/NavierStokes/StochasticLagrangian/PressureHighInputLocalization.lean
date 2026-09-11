import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureHighInputAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputLocalization

/-! Localization commutes with the convergent high-input operator series. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureHighInputLocalization

open MeasureTheory PressureHighInputAction PressureFixedOutputLocalization
open PressureDyadicLocalization (multiplyField)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def tailLocalization (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) : C(T3, C3) :=
  (c * d) • tailOperator N hN J e f g - tailOperator N hN J e (c • f) (d • g)

theorem hasSum_tailLocalization (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) (he : ‖e‖ = 1)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) :
    HasSum (fun j : ℕ ↦ localization N hN (J + j) e f g c d)
      (tailLocalization N hN J e f g c d) :=
  ((multiplyField (c * d)).hasSum (hasSum_tailOperator_apply N hN J e he f g)).sub
    (hasSum_tailOperator_apply N hN J e he (c • f) (d • g))

theorem finite_tailLocalization_spatial_norm_le {ι : Type*} [Fintype ι]
    (N : ℝ) (hN : 0 < N) (J : ℕ) (e : ι → R3) (he : ∀ i, ‖e i‖ = 1)
    (f g : C(T3, C3)) (c d : ι → C(T3, ℂ))
    (hs : Summable (fun j : ℕ ↦ Real.sqrt (∫ x : T3, ∑ i,
      ‖localization N hN (J + j) (e i) f g (c i) (d i) x‖ ^ 2))) :
    Real.sqrt (∫ x : T3, ∑ i, ‖tailLocalization N hN J (e i) f g (c i) (d i) x‖ ^ 2) ≤
      ∑' j : ℕ, Real.sqrt (∫ x : T3, ∑ i,
        ‖localization N hN (J + j) (e i) f g (c i) (d i) x‖ ^ 2) :=
  Mettapedia.Analysis.ContinuousFieldMinkowski.hasSum_finite_spatial_norm_le volume
    (fun j i ↦ localization N hN (J + j) (e i) f g (c i) (d i))
    (fun i ↦ tailLocalization N hN J (e i) f g (c i) (d i))
    (fun i ↦ hasSum_tailLocalization N hN J (e i) (he i) f g (c i) (d i)) hs

end Mettapedia.FluidDynamics.NavierStokes.PressureHighInputLocalization
