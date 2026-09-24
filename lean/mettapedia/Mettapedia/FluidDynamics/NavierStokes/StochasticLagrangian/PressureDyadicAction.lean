import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPeriodization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureIntegrableKernelAction

/-!
# Exact-partition pressure acting on continuous full fields

Each periodic band acts on arbitrary continuous complex fields. Operator-norm
mass summability gives absolute convergence in the continuous-field supremum
norm. Localization retains the two weighted input differences; monomials
recover the exact low-output pressure coefficient.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction

open MeasureTheory Filter PeriodicFourierTriad FourierPressureCommutator PancakeBilinearPeriodization
open PressureKernelAction (kernelAction)
open PressureIntegrableKernelAction
open PressureDyadicPeriodization PressureBilinearOperator
open PressureLowOutputSymbol (pairEquiv)
open PressureDyadicPhysicalKernel (physicalCutoff)
open PressureLowOutputDyadicBudget (dyadicParameter)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
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

def action (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (f g : C(T3, C3)) : C(T3, C3) :=
  ⟨kernelAction (periodicKernel N hN t e) f g,
    continuous_kernelAction _ (integrable_periodicKernel N hN t e) _ _ f.continuous g.continuous⟩

@[simp] theorem action_apply (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3)
    (f g : C(T3, C3)) (x : T3) :
    action N hN t e f g x = kernelAction (periodicKernel N hN t e) f g x := rfl

theorem norm_action_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (f g : C(T3, C3)) :
    ‖action N hN t e f g‖ ≤ (∫ q : T6, ‖periodicKernel N hN t e q‖) * ‖f‖ * ‖g‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  exact norm_kernelAction_le _ (integrable_periodicKernel N hN t e) f g x

theorem exists_uniform_action_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 → ∀ f g : C(T3, C3),
      Summable (fun n ↦ ‖action N hN (dyadicParameter n) e f g‖) ∧
      (∑' n, ‖action N hN (dyadicParameter n) e f g‖) ≤ C * ‖f‖ * ‖g‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_mass_budget
  refine ⟨C, hC, ?_⟩
  intro N hN e he f g
  obtain ⟨hmass, hbound⟩ := hb N hN e he
  have hs := (hmass.mul_right ‖f‖).mul_right ‖g‖
  have hle (n : ℕ) := norm_action_le N hN (dyadicParameter n) e f g
  have hsum := Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hle hs
  refine ⟨hsum, ?_⟩
  have h := hsum.tsum_le_tsum hle hs
  simp only [tsum_mul_right] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg f)) (norm_nonneg g))

theorem summable_action (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1) (f g : C(T3, C3)) :
    Summable (fun n : ℕ ↦ action N hN (dyadicParameter n) e f g) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_action_budget
  exact (hb N hN e he f g).1.of_norm

def sumAction (N : ℝ) (hN : 0 < N) (e : R3) (f g : C(T3, C3)) : C(T3, C3) :=
  ∑' n : ℕ, action N hN (dyadicParameter n) e f g

theorem exists_uniform_sumAction_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 → ∀ f g : C(T3, C3),
      ‖sumAction N hN e f g‖ ≤ C * ‖f‖ * ‖g‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_action_budget
  refine ⟨C, hC, ?_⟩
  intro N hN e he f g
  exact (norm_tsum_le_tsum_norm (hb N hN e he f g).1).trans (hb N hN e he f g).2

theorem hasSum_action_apply (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1)
    (f g : C(T3, C3)) (x : T3) :
    HasSum (fun n : ℕ ↦ kernelAction (periodicKernel N hN (dyadicParameter n) e) f g x)
      (sumAction N hN e f g x) :=
  (ContinuousMap.evalCLM ℂ x).hasSum (summable_action N hN e he f g).hasSum

theorem action_localization (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) (x : T3) :
    (c x * d x) • action N hN t e f g x - action N hN t e (c • f) (d • g) x =
      ∫ q : T6, (c x * d x - c (x - firstTorusDisplacement q) * d (x - secondTorusDisplacement q)) •
        periodicKernel N hN t e q (f (x - firstTorusDisplacement q))
          (g (x - secondTorusDisplacement q)) :=
  kernelAction_localization _ _ _ _ _ x (integrable_periodicKernel N hN t e)
    f.continuous g.continuous c.continuous d.continuous

/-- The full output-band sum preserves the exact two-input localization identity. -/
theorem hasSum_localization (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1)
    (f g : C(T3, C3)) (c d : C(T3, ℂ)) (x : T3) :
    HasSum (fun n : ℕ ↦ ∫ q : T6,
      (c x * d x - c (x - firstTorusDisplacement q) * d (x - secondTorusDisplacement q)) •
        periodicKernel N hN (dyadicParameter n) e q (f (x - firstTorusDisplacement q))
          (g (x - secondTorusDisplacement q)))
      ((c x * d x) • sumAction N hN e f g x - sumAction N hN e (c • f) (d • g) x) := by
  have h := ((hasSum_action_apply N hN e he f g x).const_smul (c x * d x)).sub
    (hasSum_action_apply N hN e he (c • f) (d • g) x)
  apply h.congr
  intro S
  apply Finset.sum_congr rfl
  intro n hn
  exact action_localization N hN (dyadicParameter n) e f g c d x

theorem kernelAction_monomials (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) (u v : C3) (x : T3) :
    kernelAction (periodicKernel N hN t e) (fun y ↦ UnitAddTorus.mFourier k y • u)
      (fun y ↦ UnitAddTorus.mFourier p y • v) x =
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier p x) •
        ((physicalCutoff t (N⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) : ℂ) •
          pressurePairOperator e he k p u v) := by
  rw [PressureIntegrableKernelAction.kernelAction_monomials _ (integrable_periodicKernel N hN t e),
    mFourierCoeff_periodicKernel]
  rfl

theorem hasSum_kernelAction_monomials (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) (hsmall : ‖realFrequency k + realFrequency p‖ ≤ N / 256)
    (u v : C3) (x : T3) :
    HasSum (fun n : ℕ ↦ kernelAction (periodicKernel N hN (dyadicParameter n) e)
      (fun y ↦ UnitAddTorus.mFourier k y • u) (fun y ↦ UnitAddTorus.mFourier p y • v) x)
      ((UnitAddTorus.mFourier k x * UnitAddTorus.mFourier p x) •
        ((Mettapedia.Analysis.DyadicAnnulus.normalizedCutoff (N⁻¹ • realFrequency k) : ℂ) •
          pressurePairOperator e he k p u v)) := by
  have h := hasSum_mFourierCoeff_periodicKernel N hN e he k p hsmall
  have hv := (ContinuousLinearMap.apply ℂ C3 v).hasSum
    ((ContinuousLinearMap.apply ℂ (C3 →L[ℂ] C3) u).hasSum h)
  have hs := hv.const_smul (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier p x)
  simpa only [PressureIntegrableKernelAction.kernelAction_monomials _
    (integrable_periodicKernel N hN _ e), ContinuousLinearMap.apply_apply,
    smul_apply] using hs

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction
