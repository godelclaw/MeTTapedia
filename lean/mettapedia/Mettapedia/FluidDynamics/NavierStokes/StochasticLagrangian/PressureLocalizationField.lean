import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureIntegrableKernelAction
import Mettapedia.Analysis.ContinuousFieldMinkowski

/-!
# Integrable continuous-field pressure localization

The parameter is allowed to have a merely integrable operator kernel.
Spatial continuity and integrability in the continuous-field norm are
proved before applying the finite-family Minkowski inequality. The coarse
supremum bound below proves existence of the Bochner integral only; the
spatial localization estimate can retain its sharper first-moment budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationField

open MeasureTheory Filter PancakeBilinearPeriodization
open PressureKernelAction (kernelAction)
open PressureIntegrableKernelAction
open Mettapedia.Analysis.BilinearKernelLocalization

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def localizationField (f g : C(T3, C3)) (c d : C(T3, ℂ)) (q : T6) (B : Op) : C(T3, C3) :=
  ⟨fun x ↦ (c x * d x) • B (f (x - firstTorusDisplacement q)) (g (x - secondTorusDisplacement q)) -
    B (c (x - firstTorusDisplacement q) • f (x - firstTorusDisplacement q))
      (d (x - secondTorusDisplacement q) • g (x - secondTorusDisplacement q)), by fun_prop⟩

theorem continuous_localizationField (f g : C(T3, C3)) (c d : C(T3, ℂ)) :
    Continuous (fun z : T6 × Op ↦ localizationField f g c d z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry _
  simp only [localizationField, Function.uncurry_def, ContinuousMap.coe_mk]
  fun_prop

theorem norm_localizationField_le (f g : C(T3, C3)) (c d : C(T3, ℂ)) (q : T6) (B : Op) :
    ‖localizationField f g c d q B‖ ≤ ‖B‖ * (2 * ‖c‖ * ‖d‖ * ‖f‖ * ‖g‖) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖(c x * d x) • B _ _ - B _ _‖ ≤ _
  rw [smul_sub_apply_smul, norm_smul]
  have hs : ‖c x * d x - c (x - firstTorusDisplacement q) * d (x - secondTorusDisplacement q)‖ ≤
      2 * ‖c‖ * ‖d‖ := by
    calc
      _ ≤ ‖c x * d x‖ + ‖c (x - firstTorusDisplacement q) * d (x - secondTorusDisplacement q)‖ :=
        norm_sub_le _ _
      _ ≤ ‖c‖ * ‖d‖ + ‖c‖ * ‖d‖ := by
        simp only [norm_mul]
        gcongr <;> exact ContinuousMap.norm_coe_le_norm _ _
      _ = _ := by ring
  have hb := B.le_of_opNorm₂_le_of_le le_rfl
    (f.norm_coe_le_norm (x - firstTorusDisplacement q)) (g.norm_coe_le_norm (x - secondTorusDisplacement q))
  exact (mul_le_mul hs hb (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem aestronglyMeasurable_localizationField (K : T6 → Op)
    (hK : AEStronglyMeasurable K) (f g : C(T3, C3)) (c d : C(T3, ℂ)) :
    AEStronglyMeasurable (fun q : T6 ↦ localizationField f g c d q (K q)) := by
  have hid : AEStronglyMeasurable (id : T6 → T6) (volume : Measure T6) :=
    continuous_id.aestronglyMeasurable
  have h := (continuous_localizationField f g c d).comp_aestronglyMeasurable (hid.prodMk hK)
  simpa only [Function.comp_def, id_eq] using h

theorem integrable_localizationField (K : T6 → Op) (hK : Integrable K)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) :
    Integrable (fun q : T6 ↦ localizationField f g c d q (K q)) := by
  have hm := aestronglyMeasurable_localizationField K hK.aestronglyMeasurable f g c d
  exact (hK.norm.mul_const (2 * ‖c‖ * ‖d‖ * ‖f‖ * ‖g‖)).mono' hm
    (Eventually.of_forall (fun q ↦ norm_localizationField_le f g c d q (K q)))

theorem integral_localizationField_apply (K : T6 → Op) (hK : Integrable K)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) (x : T3) :
    (∫ q : T6, localizationField f g c d q (K q)) x =
      (c x * d x) • kernelAction K f g x -
        kernelAction K (fun y ↦ c y • f y) (fun y ↦ d y • g y) x := by
  rw [ContinuousMap.integral_apply (integrable_localizationField K hK f g c d)]
  change (∫ q : T6, (c x * d x) • K q _ _ - K q _ _) = _
  have hs : Integrable (fun q : T6 ↦ (c x * d x) • K q
      (f (x - firstTorusDisplacement q)) (g (x - secondTorusDisplacement q))) :=
    (integrable_action_integrand K f g x hK f.continuous g.continuous).smul (c x * d x)
  rw [integral_sub hs
    (integrable_action_integrand K (fun y ↦ c y • f y) (fun y ↦ d y • g y) x hK
      (c.continuous.smul f.continuous) (d.continuous.smul g.continuous)),
    integral_smul]
  rfl

theorem finite_localization_spatial_norm_le {ι : Type*} [Fintype ι]
    (K : ι → T6 → Op) (hK : ∀ i, Integrable (K i))
    (f g : C(T3, C3)) (c d : ι → C(T3, ℂ)) :
    Real.sqrt (∫ x : T3, ∑ i,
      ‖(c i x * d i x) • kernelAction (K i) f g x -
        kernelAction (K i) (fun y ↦ c i y • f y) (fun y ↦ d i y • g y) x‖ ^ 2) ≤
      ∫ q : T6, Real.sqrt (∫ x : T3, ∑ i, ‖localizationField f g (c i) (d i) q (K i q) x‖ ^ 2) := by
  have h := Mettapedia.Analysis.ContinuousFieldMinkowski.integral_finite_spatial_norm_le
    (volume : Measure T3) (fun q i ↦ localizationField f g (c i) (d i) q (K i q))
    (fun i ↦ integrable_localizationField (K i) (hK i) f g (c i) (d i))
  have he (i : ι) (x : T3) : (∫ q : T6, localizationField f g (c i) (d i) q (K i q) x) =
      (c i x * d i x) • kernelAction (K i) f g x -
        kernelAction (K i) (fun y ↦ c i y • f y) (fun y ↦ d i y • g y) x := by
    rw [← ContinuousMap.integral_apply (integrable_localizationField (K i) (hK i) f g (c i) (d i))]
    exact integral_localizationField_apply (K i) (hK i) f g (c i) (d i) x
  simpa only [he] using h

end Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationField
