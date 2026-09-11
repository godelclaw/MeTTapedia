import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureKernelAction
import Mettapedia.Analysis.BilinearKernelIntegrability

/-!
# Full-field pressure action for integrable kernels

The kernel need only be integrable in operator norm. Continuous full fields
on the compact torus give well-defined continuous output, exact localization,
and the same monomial Fourier identity as the continuous-kernel interface.
No scalar-cutoff derivative or absolute Fourier summability is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureIntegrableKernelAction

open MeasureTheory Filter PeriodicFourierTriad PancakeBilinearPeriodization
open PressureKernelAction (kernelAction)
open Mettapedia.Analysis.BilinearKernelLocalization
open Mettapedia.Analysis.BilinearKernelIntegrability

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integrable_action_integrand (K : T6 → Op) (f g : T3 → C3) (x : T3)
    (hK : Integrable K) (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun q : T6 ↦ K q (f (x - firstTorusDisplacement q))
      (g (x - secondTorusDisplacement q))) :=
  integrable_bilinear_apply_continuous K _ _ hK (by fun_prop) (by fun_prop)

theorem kernelAction_congr_ae (K L : T6 → Op) (hKL : K =ᵐ[volume] L)
    (f g : T3 → C3) (x : T3) : kernelAction K f g x = kernelAction L f g x := by
  apply integral_congr_ae
  filter_upwards [hKL] with q hq
  rw [hq]

theorem norm_kernelAction_le (K : T6 → Op) (hK : Integrable K)
    (f g : C(T3, C3)) (x : T3) :
    ‖kernelAction K f g x‖ ≤ (∫ q : T6, ‖K q‖) * ‖f‖ * ‖g‖ := by
  have hbound (q : T6) : ‖K q (f (x - firstTorusDisplacement q))
      (g (x - secondTorusDisplacement q))‖ ≤ ‖K q‖ * ‖f‖ * ‖g‖ :=
    (K q).le_of_opNorm₂_le_of_le le_rfl (f.norm_coe_le_norm _) (g.norm_coe_le_norm _)
  have h := norm_integral_le_of_norm_le ((hK.norm.mul_const ‖f‖).mul_const ‖g‖)
    (Eventually.of_forall hbound)
  simpa only [kernelAction, integral_mul_const] using h

theorem continuous_kernelAction (K : T6 → Op) (hK : Integrable K)
    (f g : T3 → C3) (hf : Continuous f) (hg : Continuous g) : Continuous (kernelAction K f g) := by
  let fc : C(T3, C3) := ⟨f, hf⟩
  let gc : C(T3, C3) := ⟨g, hg⟩
  apply continuous_of_dominated
    (fun x ↦ (integrable_action_integrand K f g x hK hf hg).aestronglyMeasurable)
    (bound := fun q ↦ ‖K q‖ * ‖fc‖ * ‖gc‖)
  · intro x
    exact Eventually.of_forall (fun q ↦ (K q).le_of_opNorm₂_le_of_le le_rfl
      (fc.norm_coe_le_norm _) (gc.norm_coe_le_norm _))
  · exact (hK.norm.mul_const ‖fc‖).mul_const ‖gc‖
  · filter_upwards [] with q
    fun_prop

theorem kernelAction_localization (K : T6 → Op) (f g : T3 → C3) (c d : T3 → ℂ) (x : T3)
    (hK : Integrable K) (hf : Continuous f) (hg : Continuous g)
    (hc : Continuous c) (hd : Continuous d) :
    (c x * d x) • kernelAction K f g x -
      kernelAction K (fun y ↦ c y • f y) (fun y ↦ d y • g y) x =
      ∫ q : T6, (c x * d x - c (x - firstTorusDisplacement q) * d (x - secondTorusDisplacement q)) •
        K q (f (x - firstTorusDisplacement q)) (g (x - secondTorusDisplacement q)) :=
  smul_integral_sub_integral_apply_smul K _ _ _ _ _ _
    (integrable_action_integrand K f g x hK hf hg)
    (integrable_action_integrand K _ _ x hK (hc.smul hf) (hd.smul hg))

theorem norm_kernelAction_localization_le (K : T6 → Op)
    (f g : T3 → C3) (c d : T3 → ℂ) (x : T3)
    (hK : Integrable K) (hf : Continuous f) (hg : Continuous g)
    (hc : Continuous c) (hd : Continuous d) :
    ‖(c x * d x) • kernelAction K f g x -
      kernelAction K (fun y ↦ c y • f y) (fun y ↦ d y • g y) x‖ ≤
      ∫ q : T6, ‖K q‖ *
        (‖d x‖ * (‖c x - c (x - firstTorusDisplacement q)‖ * ‖f (x - firstTorusDisplacement q)‖) *
          ‖g (x - secondTorusDisplacement q)‖ +
        ‖c (x - firstTorusDisplacement q)‖ * ‖f (x - firstTorusDisplacement q)‖ *
          (‖d x - d (x - secondTorusDisplacement q)‖ * ‖g (x - secondTorusDisplacement q)‖)) :=
  norm_smul_integral_sub_integral_apply_smul_le K _ _ _ _ _ _
    (integrable_action_integrand K f g x hK hf hg)
    (integrable_action_integrand K _ _ x hK (hc.smul hf) (hd.smul hg))
    (integrable_localization_density K _ _ _ _ _ _ hK
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))

theorem kernelAction_monomials (K : T6 → Op) (hK : Integrable K)
    (k p : Wavevector) (u v : C3) (x : T3) :
    kernelAction K (fun y ↦ UnitAddTorus.mFourier k y • u)
      (fun y ↦ UnitAddTorus.mFourier p y • v) x =
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier p x) •
        (UnitAddTorus.mFourierCoeff K (pairWavevector k p)) u v := by
  let W : T6 → Op := fun q ↦ UnitAddTorus.mFourier (-pairWavevector k p) q • K q
  have hiW : Integrable W := hK.bdd_smul 1 (UnitAddTorus.mFourier _).continuous.aestronglyMeasurable
    (Eventually.of_forall (fun q ↦ ((UnitAddTorus.mFourier _).norm_coe_le_norm q).trans_eq
      UnitAddTorus.mFourier_norm))
  have hiWu : Integrable (fun q ↦ W q u) :=
    (ContinuousLinearMap.apply ℂ (C3 →L[ℂ] C3) u).integrable_comp hiW
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

end Mettapedia.FluidDynamics.NavierStokes.PressureIntegrableKernelAction
