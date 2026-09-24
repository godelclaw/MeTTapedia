import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAEMaterialChainRule

/-!
# Almost-everywhere differentiation in a periodic material direction

A periodic scalar with a locally Lipschitz real space-time lift is
differentiable along the frozen material direction almost everywhere
in time and space. The velocity may be any spatially continuous field.
There is no finite Fourier or incompressibility hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicMaterialDifferentiability

open scoped Topology
open MeasureTheory Measure
open PancakeFourierMaterialPaths PancakeMeasurableMaterialRate PancakeMaterialChainRule
open PancakeAEMaterialRate PancakePeriodicWeakDerivative PancakeAEMaterialChainRule

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "ST" => ℝ × X3

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsAddHaarMeasure (volume : Measure ST) :=
  inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure X3)))

theorem differentiableAt_materialPath_of_real_fderiv
    (f : ℝ → T3 → ℝ) (v : T3 → R3) (t : ℝ) (r : X3)
    (hf : DifferentiableAt ℝ (fun z : ST ↦ f z.1 (torusPoint z.2)) (t, r)) :
    DifferentiableAt ℝ (fun h ↦ f (t + h) (torusPoint r + materialShift (v (torusPoint r)) h)) 0 := by
  have hp := hasDerivAt_real_material_path t r (v (torusPoint r))
  have hf' : DifferentiableAt ℝ (fun z : ST ↦ f z.1 (torusPoint z.2))
      (t + 0, fun i : Fin 3 ↦ r i + 0 * v (torusPoint r) i) := by
    simpa only [add_zero, zero_mul] using hf
  simpa only [Function.comp_def, torusPoint_line] using hf'.comp 0 hp.differentiableAt

theorem ae_ae_differentiableAt_materialPath
    (f : ℝ → T3 → ℝ) (v : ℝ → T3 → R3)
    (hf : Continuous f.uncurry) (hv : ∀ t, Continuous (v t))
    (hL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2))) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T3,
      DifferentiableAt ℝ (fun h ↦ f (t + h) (x + materialShift (v t x) h)) 0 := by
  have hr := ae_differentiableAt_locallyLipschitz (volume : Measure ST) _ hL
  filter_upwards [ae_ae_of_ae_prod hr] with t ht
  apply ae_torus_of_ae_real _ (measurableSet_differentiableAt_zero
    (fun x : T3 ↦ fun h : ℝ ↦ f (t + h) (x + materialShift (v t x) h))
    (continuous_scalarMaterialFamily f (v t) hf (hv t) t))
  exact ht.mono (fun r hrf ↦ differentiableAt_materialPath_of_real_fderiv f (v t) t r hrf)

end Mettapedia.FluidDynamics.NavierStokes.PeriodicMaterialDifferentiability
