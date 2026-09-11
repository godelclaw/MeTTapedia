import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentChannelEnvelopeBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureIntegrableKernelAction

/-!
# Coherent pressure channels acting on continuous complex fields

The constructed periodic kernels act on arbitrary continuous fields.
Their matched input/output band sums converge absolutely in the field
supremum norm, uniformly over band-dependent unit directions and channel
choices. The exact two-input localization identity remains available.
No divergence-free hypothesis on either localized input is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelAction

open MeasureTheory PancakeBilinearPeriodization
open PressureKernelAction (kernelAction)
open PressureIntegrableKernelAction
open PressureCoherentDivergenceChannel (Factor)
open PressureCoherentChannelPeriodization
open PressureCoherentChannelEnvelopeBudget (exists_uniform_matched_envelope_budget)
open PressureFixedOutputSymbol (inputScale inputScale_pos)
open PressureLowOutputDyadicBudget (dyadicParameter)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
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

def action (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor)
    (f g : C(T3, C3)) : C(T3, C3) :=
  ⟨kernelAction (periodicKernel N hN t e c) f g,
    continuous_kernelAction _ (integrable_periodicKernel N hN t e c) _ _ f.continuous g.continuous⟩

@[simp] theorem action_apply (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor)
    (f g : C(T3, C3)) (x : T3) :
    action N hN t e c f g x = kernelAction (periodicKernel N hN t e c) f g x := rfl

theorem norm_action_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor)
    (f g : C(T3, C3)) :
    ‖action N hN t e c f g‖ ≤ (∫ q : T6, ‖periodicKernel N hN t e c q‖) * ‖f‖ * ‖g‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  exact norm_kernelAction_le _ (integrable_periodicKernel N hN t e c) f g x

def matchedAction (N : ℝ) (hN : 0 < N) (j m : ℕ) (e : R3) (c : Factor)
    (f g : C(T3, C3)) : C(T3, C3) :=
  action (inputScale N j) (inputScale_pos N hN j) (dyadicParameter (j + m)) e c f g

theorem exists_uniform_action_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ,
      ∀ e : ℕ → ℕ → R3, (∀ j m, ‖e j m‖ = 1) → ∀ c : ℕ → ℕ → Factor,
      ∀ f g : C(T3, C3),
        (∀ j, Summable (fun m ↦ ‖matchedAction N hN (J + j) m (e (J + j) m) (c (J + j) m) f g‖)) ∧
        Summable (fun j ↦ ∑' m, ‖matchedAction N hN (J + j) m (e (J + j) m) (c (J + j) m) f g‖) ∧
        (∑' j, ∑' m, ‖matchedAction N hN (J + j) m (e (J + j) m) (c (J + j) m) f g‖) ≤
          C * (1 / 2 : ℝ) ^ J * ‖f‖ * ‖g‖ := by
  obtain ⟨C0, C1, hC0, _, M, hb⟩ := exists_uniform_matched_envelope_budget
  refine ⟨C0, hC0, fun N hN J e he c f g ↦ ?_⟩
  obtain ⟨h, hae, hbudget⟩ := hb N hN
  obtain ⟨hinner, houter, hbound⟩ := (hbudget J).1
  have hle (j m : ℕ) :
      ‖matchedAction N hN (J + j) m (e (J + j) m) (c (J + j) m) f g‖ ≤
        (∫ q : T6, M N hN (J + j) m q) * ‖f‖ * ‖g‖ := by
    apply (norm_action_le _ _ _ _ _ f g).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
    apply integral_mono_ae (integrable_periodicKernel _ _ _ _ _).norm (h (J + j) m).2.2.1
    filter_upwards [hae] with q hq
    exact hq (J + j) m (e (J + j) m) (he (J + j) m) (c (J + j) m)
  have hi (j : ℕ) := Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) (hle j)
    (((hinner j).mul_right ‖f‖).mul_right ‖g‖)
  have hj (j : ℕ) : (∑' m, ‖matchedAction N hN (J + j) m (e (J + j) m) (c (J + j) m) f g‖) ≤
      (∑' m, ∫ q : T6, M N hN (J + j) m q) * ‖f‖ * ‖g‖ := by
    simpa only [tsum_mul_right] using (hi j).tsum_le_tsum (hle j)
      (((hinner j).mul_right ‖f‖).mul_right ‖g‖)
  have hs := (houter.mul_right ‖f‖).mul_right ‖g‖
  have ho := Summable.of_nonneg_of_le (fun j ↦ tsum_nonneg (fun m ↦ norm_nonneg _)) hj hs
  refine ⟨hi, ho, ?_⟩
  have ht := ho.tsum_le_tsum hj hs
  simp only [tsum_mul_right] at ht
  exact ht.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg f)) (norm_nonneg g))

theorem summable_matchedAction (N : ℝ) (hN : 0 < N) (J : ℕ) (e : ℕ → ℕ → R3)
    (he : ∀ j m, ‖e j m‖ = 1) (c : ℕ → ℕ → Factor) (f g : C(T3, C3)) :
    (∀ j, Summable (fun m ↦ matchedAction N hN (J + j) m (e (J + j) m) (c (J + j) m) f g)) ∧
      Summable (fun j ↦ ∑' m, matchedAction N hN (J + j) m (e (J + j) m) (c (J + j) m) f g) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_action_budget
  obtain ⟨hi, ho, _⟩ := hb N hN J e he c f g
  exact ⟨fun j ↦ (hi j).of_norm, (Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _)
    (fun j ↦ norm_tsum_le_tsum_norm (hi j)) ho).of_norm⟩

def sumAction (N : ℝ) (hN : 0 < N) (J : ℕ) (e : ℕ → ℕ → R3) (c : ℕ → ℕ → Factor)
    (f g : C(T3, C3)) : C(T3, C3) :=
  ∑' j, ∑' m, matchedAction N hN (J + j) m (e (J + j) m) (c (J + j) m) f g

theorem exists_uniform_sumAction_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ,
      ∀ e : ℕ → ℕ → R3, (∀ j m, ‖e j m‖ = 1) → ∀ c : ℕ → ℕ → Factor,
      ∀ f g : C(T3, C3), ‖sumAction N hN J e c f g‖ ≤ C * (1 / 2 : ℝ) ^ J * ‖f‖ * ‖g‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_action_budget
  refine ⟨C, hC, fun N hN J e he c f g ↦ ?_⟩
  obtain ⟨hi, ho, hbound⟩ := hb N hN J e he c f g
  have hj (j : ℕ) := norm_tsum_le_tsum_norm (hi j)
  have hs := Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) hj ho
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hj ho).trans hbound)

theorem action_localization (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor)
    (f g : C(T3, C3)) (a b : C(T3, ℂ)) (x : T3) :
    (a x * b x) • action N hN t e c f g x - action N hN t e c (a • f) (b • g) x =
      ∫ q : T6, (a x * b x - a (x - firstTorusDisplacement q) * b (x - secondTorusDisplacement q)) •
        periodicKernel N hN t e c q (f (x - firstTorusDisplacement q))
          (g (x - secondTorusDisplacement q)) :=
  kernelAction_localization _ _ _ _ _ x (integrable_periodicKernel N hN t e c)
    f.continuous g.continuous a.continuous b.continuous

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelAction
