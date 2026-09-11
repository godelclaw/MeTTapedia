import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicLocalization

/-! Localization of the fixed-output pressure operator in continuous-field norm. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputLocalization

open MeasureTheory PressureFixedOutputSymbol PressureFixedOutputAction PressureDyadicLocalization
open PressureLowOutputDyadicBudget

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def localization (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) : C(T3, C3) :=
  (c * d) • operator N hN j e f g - operator N hN j e (c • f) (d • g)

theorem hasSum_localization (N : ℝ) (hN : 0 < N) (j : ℕ) (e : R3) (he : ‖e‖ = 1)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) :
    HasSum (fun m : ℕ ↦ localizationAction (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) e f g c d) (localization N hN j e f g c d) :=
  ((multiplyField (c * d)).hasSum (hasSum_operator_apply N hN j e he f g)).sub
    (hasSum_operator_apply N hN j e he (c • f) (d • g))

theorem finite_localization_spatial_norm_le {ι : Type*} [Fintype ι]
    (N : ℝ) (hN : 0 < N) (j : ℕ) (e : ι → R3) (he : ∀ i, ‖e i‖ = 1)
    (f g : C(T3, C3)) (c d : ι → C(T3, ℂ))
    (hs : Summable (fun m : ℕ ↦ Real.sqrt (∫ x : T3, ∑ i,
      ‖localizationAction (inputScale N j) (inputScale_pos N hN j)
        (dyadicParameter (j + m)) (e i) f g (c i) (d i) x‖ ^ 2))) :
    Real.sqrt (∫ x : T3, ∑ i, ‖localization N hN j (e i) f g (c i) (d i) x‖ ^ 2) ≤
      ∑' m : ℕ, Real.sqrt (∫ x : T3, ∑ i,
        ‖localizationAction (inputScale N j) (inputScale_pos N hN j)
          (dyadicParameter (j + m)) (e i) f g (c i) (d i) x‖ ^ 2) :=
  Mettapedia.Analysis.ContinuousFieldMinkowski.hasSum_finite_spatial_norm_le volume
    (fun m i ↦ localizationAction (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) (e i) f g (c i) (d i))
    (fun i ↦ localization N hN j (e i) f g (c i) (d i))
    (fun i ↦ hasSum_localization N hN j (e i) (he i) f g (c i) (d i)) hs

end Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputLocalization
