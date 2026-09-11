import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FinitePressureKernel
import Mettapedia.Analysis.BilinearKernelLocalization

/-!
# Physical action and localization of the pressure-pair kernel

The integral identities keep the cutoff differences attached to their
own input vectors. Continuous fields and cutoffs on the compact torus
give the required integrability, without a scalar-cutoff gradient bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureKernelAction

open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization
open PressureBilinearOperator FinitePressureKernel
open Mettapedia.Analysis.BilinearKernelLocalization

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup (C3 →L[ℂ] C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace (C3 →L[ℂ] C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def kernelAction (K : T6 → C3 →L[ℂ] C3 →L[ℂ] C3) (f g : T3 → C3) (x : T3) : C3 :=
  ∫ q : T6, K q (f (x - firstTorusDisplacement q)) (g (x - secondTorusDisplacement q))

theorem integrable_action_integrand (K : T6 → C3 →L[ℂ] C3 →L[ℂ] C3)
    (f g : T3 → C3) (x : T3) (hK : Continuous K) (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun q : T6 ↦ K q (f (x - firstTorusDisplacement q)) (g (x - secondTorusDisplacement q))) := by
  have hc : Continuous (fun q : T6 ↦ K q (f (x - firstTorusDisplacement q)) (g (x - secondTorusDisplacement q))) := by
    fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem kernelAction_localization (K : T6 → C3 →L[ℂ] C3 →L[ℂ] C3)
    (f g : T3 → C3) (c d : T3 → ℂ) (x : T3)
    (hK : Continuous K) (hf : Continuous f) (hg : Continuous g)
    (hc : Continuous c) (hd : Continuous d) :
    (c x * d x) • kernelAction K f g x -
      kernelAction K (fun y ↦ c y • f y) (fun y ↦ d y • g y) x =
      ∫ q : T6, (c x * d x - c (x - firstTorusDisplacement q) * d (x - secondTorusDisplacement q)) •
        K q (f (x - firstTorusDisplacement q)) (g (x - secondTorusDisplacement q)) := by
  exact smul_integral_sub_integral_apply_smul K _ _ _ _ _ _
    (integrable_action_integrand K f g x hK hf hg)
    (integrable_action_integrand K _ _ x hK (hc.smul hf) (hd.smul hg))

theorem norm_kernelAction_localization_le (K : T6 → C3 →L[ℂ] C3 →L[ℂ] C3)
    (f g : T3 → C3) (c d : T3 → ℂ) (x : T3)
    (hK : Continuous K) (hf : Continuous f) (hg : Continuous g)
    (hc : Continuous c) (hd : Continuous d) :
    ‖(c x * d x) • kernelAction K f g x -
      kernelAction K (fun y ↦ c y • f y) (fun y ↦ d y • g y) x‖ ≤
      ∫ q : T6, ‖K q‖ *
        (‖d x‖ * (‖c x - c (x - firstTorusDisplacement q)‖ * ‖f (x - firstTorusDisplacement q)‖) *
          ‖g (x - secondTorusDisplacement q)‖ +
        ‖c (x - firstTorusDisplacement q)‖ * ‖f (x - firstTorusDisplacement q)‖ *
          (‖d x - d (x - secondTorusDisplacement q)‖ * ‖g (x - secondTorusDisplacement q)‖)) := by
  apply norm_smul_integral_sub_integral_apply_smul_le K _ _ _ _ _ _
    (integrable_action_integrand K f g x hK hf hg)
    (integrable_action_integrand K _ _ x hK (hc.smul hf) (hd.smul hg))
  have hb : Continuous (fun q : T6 ↦ ‖K q‖ *
      (‖d x‖ * (‖c x - c (x - firstTorusDisplacement q)‖ * ‖f (x - firstTorusDisplacement q)‖) *
        ‖g (x - secondTorusDisplacement q)‖ +
      ‖c (x - firstTorusDisplacement q)‖ * ‖f (x - firstTorusDisplacement q)‖ *
        (‖d x - d (x - secondTorusDisplacement q)‖ * ‖g (x - secondTorusDisplacement q)‖))) := by
    fun_prop
  exact hb.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem kernelAction_monomials (K : T6 → C3 →L[ℂ] C3 →L[ℂ] C3) (hK : Continuous K)
    (k p : Wavevector) (u v : C3) (x : T3) :
    kernelAction K (fun y ↦ UnitAddTorus.mFourier k y • u)
      (fun y ↦ UnitAddTorus.mFourier p y • v) x =
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier p x) •
        (UnitAddTorus.mFourierCoeff K (pairWavevector k p)) u v := by
  let W : T6 → C3 →L[ℂ] C3 →L[ℂ] C3 := fun q ↦ UnitAddTorus.mFourier (-pairWavevector k p) q • K q
  have hW : Continuous W := (UnitAddTorus.mFourier _).continuous.smul hK
  have hiW : Integrable W := hW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiWu : Integrable (fun q ↦ W q u) :=
    (hW.clm_apply continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (q : T6) : K q (UnitAddTorus.mFourier k (x - firstTorusDisplacement q) • u)
      (UnitAddTorus.mFourier p (x - secondTorusDisplacement q) • v) =
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier p x) • W q u v := by
    simp only [W, mFourier_sub_apply_spatial, neg_pairWavevector, mFourier_pairWavevector,
      map_smul, smul_apply, smul_smul]
    congr 1
    ring
  unfold kernelAction
  simp_rw [he]
  rw [integral_smul]
  congr 1
  rw [UnitAddTorus.mFourierCoeff]
  change (∫ q : T6, W q u v) = (∫ q : T6, W q) u v
  rw [ContinuousLinearMap.integral_apply hiW u, ContinuousLinearMap.integral_apply hiWu v]

end Mettapedia.FluidDynamics.NavierStokes.PressureKernelAction
