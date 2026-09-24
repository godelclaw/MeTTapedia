import Mettapedia.Analysis.FiniteTorusProduct
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureIntegrableKernelAction

/-!
# Swapping the inputs of a pressure kernel

The transformed kernel exchanges both displacement blocks and both
bilinear inputs. This is a measure-preserving change of variables,
not an assumption that the original kernel is symmetric.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureKernelSwap

open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization
open PressureKernelAction (kernelAction)
open Mettapedia.Analysis.FiniteTorusProduct

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def swapTorus : T6 ≃ᵐ T6 :=
  ((splitEquiv 3 3).trans MeasurableEquiv.prodComm).trans (splitEquiv 3 3).symm

theorem measurePreserving_swapTorus : MeasurePreserving swapTorus volume volume :=
  (measurePreserving_splitEquiv 3 3).symm.comp
    ((MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure T3))
      (ν := (volume : Measure T3))).comp (measurePreserving_splitEquiv 3 3))

private theorem split_eq (q : T6) :
    splitEquiv 3 3 q = (firstTorusDisplacement q, secondTorusDisplacement q) := by
  rw [splitEquiv_apply 3 3 q]
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    change q ⟨3 + i.val, _⟩ = q ⟨i.val + 3, _⟩
    congr 1
    exact Fin.ext (Nat.add_comm _ _)

theorem firstDisplacement_swap (q : T6) :
    firstTorusDisplacement (swapTorus q) = secondTorusDisplacement q := by
  have h : splitEquiv 3 3 (swapTorus q) = (splitEquiv 3 3 q).swap := by
    simp only [swapTorus, MeasurableEquiv.trans_apply, MeasurableEquiv.apply_symm_apply]
    rfl
  rw [split_eq, split_eq] at h
  exact congrArg Prod.fst h

theorem secondDisplacement_swap (q : T6) :
    secondTorusDisplacement (swapTorus q) = firstTorusDisplacement q := by
  have h : splitEquiv 3 3 (swapTorus q) = (splitEquiv 3 3 q).swap := by
    simp only [swapTorus, MeasurableEquiv.trans_apply, MeasurableEquiv.apply_symm_apply]
    rfl
  rw [split_eq, split_eq] at h
  exact congrArg Prod.snd h

def swapKernel (K : T6 → Op) (q : T6) : Op := (K (swapTorus q)).flip

theorem integrable_swapKernel (K : T6 → Op) (hK : Integrable K) : Integrable (swapKernel K) :=
  (ContinuousLinearMap.flipₗᵢ ℂ C3 C3 C3).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
    (measurePreserving_swapTorus.integrable_comp_of_integrable hK)

theorem integral_norm_swapKernel (K : T6 → Op) :
    (∫ q : T6, ‖swapKernel K q‖) = ∫ q : T6, ‖K q‖ := by
  simp only [swapKernel, ContinuousLinearMap.opNorm_flip]
  exact measurePreserving_swapTorus.integral_comp' (fun q ↦ ‖K q‖)

theorem kernelAction_swapKernel (K : T6 → Op) (f g : T3 → C3) (x : T3) :
    kernelAction (swapKernel K) f g x = kernelAction K g f x := by
  unfold kernelAction
  have he (q : T6) : swapKernel K q (f (x - firstTorusDisplacement q))
      (g (x - secondTorusDisplacement q)) =
      K (swapTorus q) (g (x - firstTorusDisplacement (swapTorus q)))
        (f (x - secondTorusDisplacement (swapTorus q))) := by
    simp only [swapKernel, ContinuousLinearMap.flip_apply, firstDisplacement_swap, secondDisplacement_swap]
  simp_rw [he]
  exact measurePreserving_swapTorus.integral_comp'
    (fun q : T6 ↦ K q (g (x - firstTorusDisplacement q)) (f (x - secondTorusDisplacement q)))

theorem mFourierCoeff_swapKernel_apply (K : T6 → Op) (hK : Integrable K)
    (k p : Wavevector) (u v : C3) :
    UnitAddTorus.mFourierCoeff (swapKernel K) (pairWavevector k p) u v =
      UnitAddTorus.mFourierCoeff K (pairWavevector p k) v u := by
  have h := kernelAction_swapKernel K
    (fun y ↦ UnitAddTorus.mFourier k y • u) (fun y ↦ UnitAddTorus.mFourier p y • v) 0
  rw [PressureIntegrableKernelAction.kernelAction_monomials _ (integrable_swapKernel K hK),
    PressureIntegrableKernelAction.kernelAction_monomials _ hK] at h
  simpa [UnitAddTorus.mFourier] using h

end Mettapedia.FluidDynamics.NavierStokes.PressureKernelSwap
