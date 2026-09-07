import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMaterialChainRule

/-!
# The periodic material chain rule almost everywhere in spacetime

Measurability of the actual scalar rates allows real-spacetime Rademacher
differentiability to descend through the measured torus quotient. The
velocity is only required to be continuous in space at each fixed time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeAEMaterialChainRule

open scoped Topology
open MeasureTheory Measure
open PancakeMaterialChainRule PancakeMeasurableMaterialRate PancakeCompactMeanDerivative
open PancakeFourierMaterialPaths PancakeFourierTranslationCurve PancakeHaarTransportRate
open PancakeWeakIncompressibleTransport PancakePeriodicWeakDerivative PancakeAEMaterialRate

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

theorem continuous_scalarMaterialFamily (f : ℝ → T3 → ℝ) (v : T3 → R3)
    (hf : Continuous f.uncurry) (hv : Continuous v) (t : ℝ) :
    Continuous (fun z : T3 × ℝ ↦ f (t + z.2) (z.1 + materialShift (v z.1) z.2)) := by
  have hs : Continuous (fun z : T3 × ℝ ↦ z.1 + materialShift (v z.1) z.2) := by
    apply Continuous.add continuous_fst
    apply continuous_pi
    intro i
    change Continuous (fun z : T3 × ℝ ↦ ((z.2 * v z.1 i : ℝ) : UnitAddCircle))
    have hvi : Continuous (fun z : T3 × ℝ ↦ v z.1 i) :=
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).continuous.comp hv).comp continuous_fst
    exact continuous_quot_mk.comp (continuous_snd.mul hvi)
  exact hf.comp ((continuous_const.add continuous_snd).prodMk hs)

theorem measurable_scalarMaterialRate (f : ℝ → T3 → ℝ) (v : T3 → R3)
    (hf : Continuous f.uncurry) (hv : Continuous v) (t : ℝ) :
    Measurable (scalarMaterialRate f v t) :=
  measurable_deriv_at_zero (fun x : T3 ↦ fun h : ℝ ↦ f (t + h) (x + materialShift (v x) h))
    (continuous_scalarMaterialFamily f v hf hv t)

theorem measurable_coordinateTransport (f : T3 → ℝ) (v : Fin 3 → T3 → ℝ)
    (hf : Continuous f) (hv : ∀ j, Measurable (v j)) : Measurable (coordinateTransport f v) := by
  apply Finset.measurable_sum
  intro j _
  exact (measurable_shiftRate f (coordinateShift j) hf (continuous_coordinateShift j)).mul (hv j)

theorem measurableSet_timeDifferentiable (f : ℝ → T3 → ℝ)
    (hf : Continuous f.uncurry) (t : ℝ) :
    MeasurableSet {x : T3 | DifferentiableAt ℝ (fun h ↦ f h x) t} := by
  have hm := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x : T3 ↦ fun h : ℝ ↦ f h x) (hf.comp continuous_swap)
  exact hm.preimage (show Measurable (fun x : T3 ↦ (x, t)) from measurable_id.prodMk measurable_const)

theorem measurableSet_materialRate_split (f : ℝ → T3 → ℝ) (v : T3 → R3)
    (hf : Continuous f.uncurry) (hv : Continuous v) (t : ℝ) :
    MeasurableSet {x : T3 | DifferentiableAt ℝ (fun h ↦ f h x) t ∧
      scalarMaterialRate f v t x = parameterRate f t x + coordinateTransport (f t) (fun j y ↦ v y j) x} := by
  have hft : Continuous (f t) := hf.comp (continuous_const.prodMk continuous_id)
  have hvt : ∀ j, Measurable (fun x : T3 ↦ v x j) := fun j ↦
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) j).continuous.comp hv).measurable
  exact (measurableSet_timeDifferentiable f hf t).inter
    (measurableSet_eq_fun (measurable_scalarMaterialRate f v hf hv t)
      ((measurable_parameterRate f hf t).add (measurable_coordinateTransport (f t) _ hft hvt)))

theorem ae_ae_materialRate_split (f : ℝ → T3 → ℝ) (v : ℝ → T3 → R3)
    (hf : Continuous f.uncurry) (hv : ∀ t, Continuous (v t))
    (hL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2))) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T3, DifferentiableAt ℝ (fun h ↦ f h x) t ∧
      scalarMaterialRate f (v t) t x = parameterRate f t x +
        coordinateTransport (f t) (fun j y ↦ v t y j) x := by
  have hr := ae_differentiableAt_locallyLipschitz (volume : Measure ST) _ hL
  have ht := ae_ae_of_ae_prod hr
  filter_upwards [ht] with t htr
  apply ae_torus_of_ae_real _ (measurableSet_materialRate_split f (v t) hf (hv t) t)
  exact htr.mono (fun r hr ↦ materialRate_split_of_real_fderiv f (v t) t r hr)

end Mettapedia.FluidDynamics.NavierStokes.PancakeAEMaterialChainRule
