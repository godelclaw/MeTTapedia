import Mettapedia.Analysis.BilinearTranslatedKernel
import Mathlib.Analysis.Normed.Operator.Mul

/-! Checks for weighted integral energy and translated L² kernel actions. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearTranslatedKernelTests

open MeasureTheory WeightedIntegralEnergy BilinearTranslatedKernel

local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

example : (∫ _x : ℝ, (3 : ℝ) * 4 ∂Measure.dirac 0) ^ 2 =
    (∫ _x : ℝ, (3 : ℝ) ∂Measure.dirac 0) * ∫ _x : ℝ, (3 : ℝ) * 4 ^ 2 ∂Measure.dirac 0 := by
  norm_num

example (a : ℝ → ℝ) (ha : AEStronglyMeasurable a) (ha0 : ∀ x, 0 ≤ a x) :
    Integrable (fun x ↦ (0 : ℝ) * a x) ∧
      (∫ x, (0 : ℝ) * a x) ^ 2 ≤ (∫ _x : ℝ, (0 : ℝ)) * ∫ x, (0 : ℝ) * a x ^ 2 :=
  weighted_cauchy_schwarz (fun _ ↦ 0) a (by simp) (fun _ ↦ le_rfl) ha ha0 (by simp)

example (x : ℝ) :
    action (μ := Measure.dirac (0 : ℝ)) (fun _ : ℝ ↦ (3 : ℝ) • ContinuousLinearMap.mul ℝ ℝ)
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (2 : ℝ)) (fun y : ℝ ↦ y) (fun _ ↦ (4 : ℝ)) x =
        12 * (x - 1) := by
  simp [action]
  ring

example (f : ℝ → ℝ) (hf : MemLp f 2) :
    MemLp (action (μ := Measure.dirac (0 : ℝ))
      (fun _ : ℝ ↦ (3 : ℝ) • ContinuousLinearMap.mul ℝ ℝ)
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (2 : ℝ)) f (fun _ ↦ (4 : ℝ))) 2 :=
  (action_memLp_two_and_energy_le _ (by simp) _ _ measurable_const measurable_const
    f _ hf aestronglyMeasurable_const (by norm_num : (0 : ℝ) ≤ 4) (fun _ ↦ by norm_num)).2.1

example (f : ℝ → ℝ) (hf : MemLp f 2) :
    (∫ x : ℝ, ‖action (μ := Measure.dirac (0 : ℝ))
      (fun _ : ℝ ↦ (3 : ℝ) • ContinuousLinearMap.mul ℝ ℝ)
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (2 : ℝ)) f (fun _ ↦ (4 : ℝ)) x‖ ^ 2) ≤
        144 * ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have h := (action_memLp_two_and_energy_le
    (fun _ : ℝ ↦ (3 : ℝ) • ContinuousLinearMap.mul ℝ ℝ) (by simp)
    (fun _ ↦ (1 : ℝ)) (fun _ ↦ (2 : ℝ)) measurable_const measurable_const
    f (fun _ ↦ (4 : ℝ)) hf aestronglyMeasurable_const
    (by norm_num : (0 : ℝ) ≤ 4) (fun _ ↦ by norm_num)
    (μ := Measure.dirac (0 : ℝ))).2.2
  norm_num [norm_smul, ContinuousLinearMap.opNorm_mul] at h ⊢
  exact h

example (K : ℝ → ℝ →L[ℝ] ℝ →L[ℝ] ℝ) (f f' g : ℝ → ℝ) (hf : f =ᵐ[volume] f') :
    action (μ := volume) K (fun q ↦ q) (fun q ↦ -q) f g =ᵐ[volume]
      action (μ := volume) K (fun q ↦ q) (fun q ↦ -q) f' g :=
  action_congr_ae K K Filter.EventuallyEq.rfl _ _ measurable_id measurable_neg
    f f' g g hf Filter.EventuallyEq.rfl

end Mettapedia.Analysis.BilinearTranslatedKernelTests

#print axioms Mettapedia.Analysis.WeightedIntegralEnergy.weighted_cauchy_schwarz
#print axioms Mettapedia.Analysis.WeightedIntegralEnergy.integrable_and_norm_integral_sq_le
#print axioms Mettapedia.Analysis.BilinearTranslatedKernel.measurePreserving_skew_sub
#print axioms Mettapedia.Analysis.BilinearTranslatedKernel.integral_weighted_translate
#print axioms Mettapedia.Analysis.BilinearTranslatedKernel.action_memLp_two_and_energy_le
#print axioms Mettapedia.Analysis.BilinearTranslatedKernel.action_memLp_two_and_energy_le_right
#print axioms Mettapedia.Analysis.BilinearTranslatedKernel.action_congr_ae
#print axioms Mettapedia.Analysis.BilinearTranslatedKernel.action_sub_left_ae
#print axioms Mettapedia.Analysis.BilinearTranslatedKernel.action_sub_left_energy_le
