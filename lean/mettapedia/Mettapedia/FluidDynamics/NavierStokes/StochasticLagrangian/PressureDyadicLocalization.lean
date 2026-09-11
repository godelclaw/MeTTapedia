import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLocalizationField
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicAction

/-!
# Spatial localization of the complete output-band pressure sum

The continuous-field series converges before the spatial norm is estimated.
The spatial triangle inequality keeps all finite patches in one Hilbert norm.
This sums output bands at a fixed input scale, not distinct input scales.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicLocalization

open MeasureTheory PressureDyadicAction
open PressureLowOutputDyadicBudget (dyadicParameter)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def localizationAction (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) : C(T3, C3) :=
  (c * d) • action N hN t e f g - action N hN t e (c • f) (d • g)

def sumLocalizationAction (N : ℝ) (hN : 0 < N) (e : R3)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) : C(T3, C3) :=
  (c * d) • sumAction N hN e f g - sumAction N hN e (c • f) (d • g)

def multiplyField (c : C(T3, ℂ)) : C(T3, C3) →L[ℂ] C(T3, C3) where
  toFun f := c • f
  map_add' f g := smul_add c f g
  map_smul' a f := by
    apply ContinuousMap.ext
    intro x
    exact smul_comm (c x) a (f x)
  cont := by
    apply ContinuousMap.continuous_of_continuous_uncurry _
    change Continuous (fun z : C(T3, C3) × T3 ↦ c z.2 • z.1 z.2)
    exact (c.continuous.comp continuous_snd).smul continuous_eval

theorem hasSum_localizationAction (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) :
    HasSum (fun n : ℕ ↦ localizationAction N hN (dyadicParameter n) e f g c d)
      (sumLocalizationAction N hN e f g c d) :=
  ((multiplyField (c * d)).hasSum (summable_action N hN e he f g).hasSum).sub
    (summable_action N hN e he (c • f) (d • g)).hasSum

theorem finite_sumLocalization_spatial_norm_le {ι : Type*} [Fintype ι]
    (N : ℝ) (hN : 0 < N) (e : ι → R3) (he : ∀ i, ‖e i‖ = 1)
    (f g : C(T3, C3)) (c d : ι → C(T3, ℂ))
    (hs : Summable (fun n : ℕ ↦ Real.sqrt (∫ x : T3, ∑ i,
      ‖localizationAction N hN (dyadicParameter n) (e i) f g (c i) (d i) x‖ ^ 2))) :
    Real.sqrt (∫ x : T3, ∑ i, ‖sumLocalizationAction N hN (e i) f g (c i) (d i) x‖ ^ 2) ≤
      ∑' n : ℕ, Real.sqrt (∫ x : T3, ∑ i,
        ‖localizationAction N hN (dyadicParameter n) (e i) f g (c i) (d i) x‖ ^ 2) :=
  Mettapedia.Analysis.ContinuousFieldMinkowski.hasSum_finite_spatial_norm_le volume
    (fun n i ↦ localizationAction N hN (dyadicParameter n) (e i) f g (c i) (d i))
    (fun i ↦ sumLocalizationAction N hN (e i) f g (c i) (d i))
    (fun i ↦ hasSum_localizationAction N hN (e i) (he i) f g (c i) (d i)) hs

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicLocalization
