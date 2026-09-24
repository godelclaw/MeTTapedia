import Mettapedia.Analysis.BilinearKernelIntegrability
import Mettapedia.Analysis.BilinearCoefficientSums
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Discontinuous kernels and actual bilinear integrals under the bounded-input interface. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearKernelIntegrabilityTests

open MeasureTheory Set Filter BilinearKernelIntegrability
open scoped ENNReal

local notation "Op" => ℝ →L[ℝ] ℝ →L[ℝ] ℝ
local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup

private def stepKernel : ℝ → Op := (Icc (0 : ℝ) 1).indicator (fun _ ↦ ContinuousLinearMap.mul ℝ ℝ)

private theorem integrable_stepKernel : Integrable stepKernel := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact integrableOn_const (C := ContinuousLinearMap.mul ℝ ℝ)
    (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞)

example : Integrable (fun x : ℝ ↦ stepKernel x 2 3) :=
  integrable_bilinear_apply_bounded stepKernel (fun _ ↦ 2) (fun _ ↦ 3) integrable_stepKernel
    aestronglyMeasurable_const aestronglyMeasurable_const
    (Eventually.of_forall (fun _ ↦ le_rfl)) (Eventually.of_forall (fun _ ↦ le_rfl))

/-- A discontinuous operator-valued step has an explicitly nonzero action. -/
example : (∫ x : ℝ, stepKernel x 2 3) = 6 := by
  have he : (fun x : ℝ ↦ stepKernel x 2 3) = (Icc (0 : ℝ) 1).indicator (fun _ ↦ (6 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> norm_num [stepKernel, indicator, hx]
  rw [he]
  simp [integral_indicator_const, measurableSet_Icc]

/-- The example cannot be routed through an assumption of kernel continuity. -/
example : ¬Continuous stepKernel := by
  intro h
  have hc : Continuous (fun x : ℝ ↦ stepKernel x 2 3) :=
    (h.clm_apply continuous_const).clm_apply continuous_const
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := 0)) 1 (by norm_num)
  have hd : dist (-δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith)]
    linarith
  have hn : -δ / 2 ∉ Icc (0 : ℝ) 1 := by
    intro hx
    have hh := hx.1
    linarith
  have hh := hb hd
  norm_num [stepKernel, indicator, hn, Real.dist_eq] at hh

/-- A zero kernel has zero localization density for arbitrary continuous inputs. -/
example {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) (u v a b : α → ℝ) (c d : ℝ)
    (hu : Continuous u) (hv : Continuous v) (ha : Continuous a) (hb : Continuous b) :
    Integrable (fun q ↦ ‖(0 : Op)‖ * (‖d‖ * (‖c - a q‖ * ‖u q‖) * ‖v q‖ +
      ‖a q‖ * ‖u q‖ * (‖d - b q‖ * ‖v q‖))) μ :=
  integrable_localization_density (fun _ ↦ (0 : Op)) u v a b c d
    (integrable_zero _ _ _) hu hv ha hb

end Mettapedia.Analysis.BilinearKernelIntegrabilityTests

#print axioms Mettapedia.Analysis.BilinearKernelIntegrability.integrable_clm_apply_bounded
#print axioms Mettapedia.Analysis.BilinearKernelIntegrability.integrable_bilinear_apply_bounded
#print axioms Mettapedia.Analysis.BilinearKernelIntegrability.integrable_bilinear_apply_continuous
#print axioms Mettapedia.Analysis.BilinearKernelIntegrability.integrable_norm_kernel_mul_continuous
#print axioms Mettapedia.Analysis.BilinearKernelIntegrability.integrable_localization_density
#print axioms Mettapedia.Analysis.EuclideanBilinearCoordinates.hasSum_reconstruct
