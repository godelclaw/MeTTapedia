import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureIntegrableKernelAction

/-!
# Integrable pressure kernels as bounded bilinear maps on continuous fields

Both input linearities follow from Bochner integrability. The operator norm
is bounded by the integral of the kernel's bilinear operator norm.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureContinuousBilinearAction

open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization
open PressureKernelAction (kernelAction)
open PressureIntegrableKernelAction

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local notation "Field" => C(T3, C3)

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Field →L[ℂ] Field) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (Field →L[ℂ] Field) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Field →L[ℂ] Field →L[ℂ] Field) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fieldAction (K : T6 → Op) (hK : Integrable K) (f g : Field) : Field :=
  ⟨kernelAction K f g, continuous_kernelAction K hK f g f.continuous g.continuous⟩

@[simp] theorem fieldAction_apply (K : T6 → Op) (hK : Integrable K) (f g : Field) (x : T3) :
    fieldAction K hK f g x = kernelAction K f g x := rfl

theorem fieldAction_add_left (K : T6 → Op) (hK : Integrable K) (f h g : Field) :
    fieldAction K hK (f + h) g = fieldAction K hK f g + fieldAction K hK h g := by
  apply ContinuousMap.ext
  intro x
  change (∫ q : T6, K q ((f + h) (x - firstTorusDisplacement q))
    (g (x - secondTorusDisplacement q))) = _
  simp only [ContinuousMap.add_apply, map_add, add_apply]
  exact integral_add (integrable_action_integrand K f g x hK f.continuous g.continuous)
    (integrable_action_integrand K h g x hK h.continuous g.continuous)

theorem fieldAction_smul_left (K : T6 → Op) (hK : Integrable K) (a : ℂ) (f g : Field) :
    fieldAction K hK (a • f) g = a • fieldAction K hK f g := by
  apply ContinuousMap.ext
  intro x
  change (∫ q : T6, K q ((a • f) (x - firstTorusDisplacement q))
    (g (x - secondTorusDisplacement q))) = _
  simp only [ContinuousMap.smul_apply, map_smul, smul_apply]
  exact integral_smul a _

theorem fieldAction_add_right (K : T6 → Op) (hK : Integrable K) (f g h : Field) :
    fieldAction K hK f (g + h) = fieldAction K hK f g + fieldAction K hK f h := by
  apply ContinuousMap.ext
  intro x
  change (∫ q : T6, K q (f (x - firstTorusDisplacement q))
    ((g + h) (x - secondTorusDisplacement q))) = _
  simp only [ContinuousMap.add_apply, map_add]
  exact integral_add (integrable_action_integrand K f g x hK f.continuous g.continuous)
    (integrable_action_integrand K f h x hK f.continuous h.continuous)

theorem fieldAction_smul_right (K : T6 → Op) (hK : Integrable K) (a : ℂ) (f g : Field) :
    fieldAction K hK f (a • g) = a • fieldAction K hK f g := by
  apply ContinuousMap.ext
  intro x
  change (∫ q : T6, K q (f (x - firstTorusDisplacement q))
    ((a • g) (x - secondTorusDisplacement q))) = _
  simp only [ContinuousMap.smul_apply, map_smul]
  exact integral_smul a _

def linearAction (K : T6 → Op) (hK : Integrable K) : Field →ₗ[ℂ] Field →ₗ[ℂ] Field :=
  LinearMap.mk₂ ℂ (fieldAction K hK) (fieldAction_add_left K hK)
    (fieldAction_smul_left K hK) (fieldAction_add_right K hK) (fieldAction_smul_right K hK)

theorem norm_linearAction_le (K : T6 → Op) (hK : Integrable K) (f g : Field) :
    ‖linearAction K hK f g‖ ≤ (∫ q : T6, ‖K q‖) * ‖f‖ * ‖g‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  exact norm_kernelAction_le K hK f g x

def bilinearAction (K : T6 → Op) (hK : Integrable K) : Field →L[ℂ] Field →L[ℂ] Field :=
  (linearAction K hK).mkContinuous₂ (∫ q : T6, ‖K q‖) (norm_linearAction_le K hK)

@[simp] theorem bilinearAction_apply (K : T6 → Op) (hK : Integrable K) (f g : Field) (x : T3) :
    bilinearAction K hK f g x = kernelAction K f g x := rfl

theorem norm_bilinearAction_le (K : T6 → Op) (hK : Integrable K) :
    ‖bilinearAction K hK‖ ≤ ∫ q : T6, ‖K q‖ :=
  LinearMap.mkContinuous₂_norm_le _ (integral_nonneg (fun _ ↦ norm_nonneg _)) _

theorem bilinearAction_congr_ae (K L : T6 → Op) (hK : Integrable K) (hL : Integrable L)
    (h : K =ᵐ[volume] L) : bilinearAction K hK = bilinearAction L hL := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro g
  apply ContinuousMap.ext
  intro x
  apply integral_congr_ae
  filter_upwards [h] with q hq
  rw [hq]

theorem bilinearAction_sub_kernel (K L : T6 → Op) (hK : Integrable K) (hL : Integrable L) :
    bilinearAction (fun q ↦ K q - L q) (hK.sub hL) = bilinearAction K hK - bilinearAction L hL := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro g
  apply ContinuousMap.ext
  intro x
  change (∫ q : T6, (K q - L q) (f (x - firstTorusDisplacement q))
    (g (x - secondTorusDisplacement q))) = _
  simp only [sub_apply]
  exact integral_sub (integrable_action_integrand K f g x hK f.continuous g.continuous)
    (integrable_action_integrand L f g x hL f.continuous g.continuous)

end Mettapedia.FluidDynamics.NavierStokes.PressureContinuousBilinearAction
