import Mettapedia.Analysis.BilinearTranslatedFamilyEnergy
import Mathlib.Analysis.Normed.Operator.Mul

/-! Nonzero family energy and shifted-weight normalization checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearTranslatedFamilyEnergyTests

open MeasureTheory BilinearTranslatedKernel BilinearTranslatedFamilyEnergy

local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

/-- The number of inputs does not multiply the common kernel constant. -/
example {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (hf : ∀ i, MemLp (f i) 2) (d : ι → ℝ) :
    (∫ x : ℝ, ∑ i, ‖action (μ := Measure.dirac (0 : ℝ))
      (fun _ : ℝ ↦ (3 : ℝ) • ContinuousLinearMap.mul ℝ ℝ)
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (2 : ℝ)) (f i) (fun _ ↦ d i) x‖ ^ 2) ≤
        9 * ∫ x : ℝ, ∑ i, (‖f i (x - 1)‖ * ‖d i‖) ^ 2 := by
  have h := integral_sum_action_energy_le
    (fun _ : ι ↦ fun _ : ℝ ↦ (3 : ℝ) • ContinuousLinearMap.mul ℝ ℝ) (fun _ ↦ by simp)
    (fun _ : ℝ ↦ (3 : ℝ)) (by simp) (fun _ ↦ by norm_num)
    (Filter.Eventually.of_forall (fun _ _ ↦ by norm_num [norm_smul, ContinuousLinearMap.opNorm_mul]))
    (fun _ ↦ (1 : ℝ)) (fun _ ↦ (2 : ℝ)) measurable_const measurable_const
    f (fun i _ ↦ d i) hf (fun _ ↦ aestronglyMeasurable_const) (fun i ↦ ‖d i‖)
    (fun _ ↦ norm_nonneg _) (fun _ _ ↦ le_rfl) (μ := Measure.dirac (0 : ℝ))
  norm_num [integral_const_mul, ← mul_assoc] at h ⊢
  exact h

/-- The right-input theorem retains the second displacement, not the first. -/
example {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (hf : ∀ i, MemLp (f i) 2) (d : ι → ℝ) :
    (∫ x : ℝ, ∑ i, ‖action (μ := Measure.dirac (0 : ℝ))
      (fun _ : ℝ ↦ (3 : ℝ) • ContinuousLinearMap.mul ℝ ℝ)
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (2 : ℝ)) (fun _ ↦ d i) (f i) x‖ ^ 2) ≤
        9 * ∫ x : ℝ, ∑ i, (‖f i (x - 2)‖ * ‖d i‖) ^ 2 := by
  have h := integral_sum_action_energy_le_right
    (fun _ : ι ↦ fun _ : ℝ ↦ (3 : ℝ) • ContinuousLinearMap.mul ℝ ℝ) (fun _ ↦ by simp)
    (fun _ : ℝ ↦ (3 : ℝ)) (by simp) (fun _ ↦ by norm_num)
    (Filter.Eventually.of_forall (fun _ _ ↦ by norm_num [norm_smul, ContinuousLinearMap.opNorm_mul]))
    (fun _ ↦ (1 : ℝ)) (fun _ ↦ (2 : ℝ)) measurable_const measurable_const
    (fun i _ ↦ d i) f hf (fun _ ↦ aestronglyMeasurable_const) (fun i ↦ ‖d i‖)
    (fun _ ↦ norm_nonneg _) (fun _ _ ↦ le_rfl) (μ := Measure.dirac (0 : ℝ))
  norm_num [integral_const_mul, ← mul_assoc] at h ⊢
  exact h

/-- Algebraic check only: normalization of squared root weights at each
point does not justify replacing shifted weights by same-point weights.
This does not assert a counterexample for a root field or a PDE solution. -/
example :
    let a : Fin 2 → ℝ := ![3 / 5, 4 / 5]
    let b : Fin 2 → ℝ := ![4 / 5, 3 / 5]
    let d : Fin 2 → ℝ := ![1, 0]
    (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
      (∑ i, a i ^ 2) = 1 ∧ (∑ i, b i ^ 2) = 1 ∧
      (∑ i, a i * d i ^ 2) < ∑ i, b i * d i ^ 2 := by
  norm_num [Fin.sum_univ_two, Fin.forall_fin_two]

end Mettapedia.Analysis.BilinearTranslatedFamilyEnergyTests

#print axioms Mettapedia.Analysis.BilinearTranslatedFamilyEnergy.integrable_weighted_input_product
#print axioms Mettapedia.Analysis.BilinearTranslatedFamilyEnergy.ae_action_energy_le
#print axioms Mettapedia.Analysis.BilinearTranslatedFamilyEnergy.integral_sum_action_energy_le
#print axioms Mettapedia.Analysis.BilinearTranslatedFamilyEnergy.integral_sum_action_energy_le_right
