import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicWeakDerivative

/-!
# Incompressible transport has zero mean for locally Lipschitz energies

The transport and divergence are built from the actual periodic coordinate
derivatives. Integration by parts, finite summation and zero divergence
give the cancellation without a differentiable scalar energy everywhere.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeWeakIncompressibleTransport

open MeasureTheory
open PancakeFourierMaterialPaths PancakeFourierTranslationCurve PancakeHaarTransportRate
open PancakePeriodicWeakDerivative

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def coordinateTransport (f : T3 → ℝ) (v : Fin 3 → T3 → ℝ) (x : T3) : ℝ :=
  ∑ j : Fin 3, shiftRate f (coordinateShift j) x * v j x

def coordinateDivergence (v : Fin 3 → T3 → ℝ) (x : T3) : ℝ :=
  ∑ j : Fin 3, shiftRate (v j) (coordinateShift j) x

theorem integral_coordinateTransport_zero
    (f : T3 → ℝ) (v : Fin 3 → T3 → ℝ)
    (hf : Continuous f) (hv : ∀ j, Continuous (v j))
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r)))
    (hvL : ∀ j, LocallyLipschitz (fun r : X3 ↦ v j (torusPoint r)))
    (hdiv : ∀ᵐ x : T3, coordinateDivergence v x = 0) :
    Integrable (coordinateTransport f v) ∧ (∫ x : T3, coordinateTransport f v x) = 0 := by
  have hA : ∀ j : Fin 3, Integrable (fun x : T3 ↦ shiftRate f (coordinateShift j) x * v j x) :=
    fun j ↦ integrable_mul_continuous _ _ (integral_coordinateRate_zero f j hf hfL).1 (hv j)
  have hB : ∀ j : Fin 3, Integrable (fun x : T3 ↦ f x * shiftRate (v j) (coordinateShift j) x) := by
    intro j
    simpa only [mul_comm] using
      integrable_mul_continuous _ f (integral_coordinateRate_zero (v j) j (hv j) (hvL j)).1 hf
  refine ⟨integrable_finsetSum Finset.univ (fun j _ ↦ hA j), ?_⟩
  unfold coordinateTransport
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hA j)]
  simp_rw [integral_coordinateRate_mul f (v _) _ hf (hv _) hfL (hvL _)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun j _ ↦ hB j)]
  have he : (∫ x : T3, ∑ j : Fin 3, f x * shiftRate (v j) (coordinateShift j) x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hdiv] with x hx
    rw [← Finset.mul_sum]
    change f x * coordinateDivergence v x = 0
    rw [hx, mul_zero]
  rw [he, neg_zero]

end Mettapedia.FluidDynamics.NavierStokes.PancakeWeakIncompressibleTransport
