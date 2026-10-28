import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledGaps
import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledTolerance
import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledFiberRecoding
import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledOutput

/-!
# Regression wrappers for coupled, anti-coupled, and deterministic Bool recoding blockers.
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem coupled_forward_gap_product_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω)) :
    countIndependentWithinForwardGap (Ω := Ω) C E F =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  exact countIndependentWithinForwardGap_coupled C E F hcouple

theorem anticoupled_backward_gap_product_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω)) :
    countIndependentWithinBackwardGap (Ω := Ω) C E F =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  exact countIndependentWithinBackwardGap_anticoupled C E F hanti

theorem coupled_nonconstant_forward_gap_positive_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < countIndependentWithinForwardGap (Ω := Ω) C E F := by
  exact
    countIndependentWithinForwardGap_pos_of_coupled_nonconstant_on_condition
      C E F hcouple hpos hneg

theorem anticoupled_nonconstant_backward_gap_positive_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < countIndependentWithinBackwardGap (Ω := Ω) C E F := by
  exact
    countIndependentWithinBackwardGap_pos_of_anticoupled_nonconstant_on_condition
      C E F hanti hpos hneg

theorem nonconstant_source_fiber_product_positive_regression
    {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    0 < conditionedSourceFiberProduct (Ω := Ω) C E := by
  exact conditionedSourceFiberProduct_pos_of_nonconstant_on_condition C E hpos hneg

theorem lower_bounds_multiply_into_source_fiber_product_regression
    {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    loTrue * loFalse ≤ conditionedSourceFiberProduct (Ω := Ω) C E := by
  exact lowerBounds_mul_le_conditionedSourceFiberProduct
    C E loTrue loFalse htrue hfalse

theorem coupled_product_tolerance_blocks_approx_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  exact
    not_countIndependentWithinTolerance_of_coupled_product_gt
      C E F τ hcouple htol

theorem anticoupled_product_tolerance_blocks_approx_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  exact
    not_countIndependentWithinTolerance_of_anticoupled_product_gt
      C E F τ hanti htol

theorem coupled_approx_certificate_forces_product_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_coupled
      C E F τ hcouple happrox

theorem coupled_lower_bounds_force_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinTolerance_coupled
      C E F τ loTrue loFalse hcouple htrue hfalse happrox

theorem coupled_lower_bounds_block_smaller_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  exact
    not_countIndependentWithinTolerance_of_coupled_lowerBounds_mul_gt
      C E F τ loTrue loFalse hcouple htrue hfalse htol

theorem anticoupled_approx_certificate_forces_product_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_anticoupled
      C E F τ hanti happrox

theorem anticoupled_lower_bounds_force_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E F τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinTolerance_anticoupled
      C E F τ loTrue loFalse hanti htrue hfalse happrox

theorem anticoupled_lower_bounds_block_smaller_tolerance_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ loTrue loFalse : Nat)
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F τ := by
  exact
    not_countIndependentWithinTolerance_of_anticoupled_lowerBounds_mul_gt
      C E F τ loTrue loFalse hanti htrue hfalse htol

theorem bool_to_any_recoding_true_side_fiber_forward_gap_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (ht : r true = y) (hf : r false ≠ y) :
    countIndependentWithinForwardGap (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  exact
    countIndependentWithinForwardGap_boolToAnyRecoding_fiber_true_false
      C E r y ht hf

theorem bool_to_any_recoding_false_side_fiber_backward_gap_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (ht : r true ≠ y) (hf : r false = y) :
    countIndependentWithinBackwardGap (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  exact
    countIndependentWithinBackwardGap_boolToAnyRecoding_fiber_false_true
      C E r y ht hf

theorem bool_to_any_recoding_true_side_fiber_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (ht : r true = y) (hf : r false ≠ y)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  exact
    not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_true_false_product_gt
      C E r y τ ht hf htol

theorem bool_to_any_recoding_false_side_fiber_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (ht : r true ≠ y) (hf : r false = y)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  exact
    not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_false_true_product_gt
      C E r y τ ht hf htol

theorem bool_to_any_recoding_distinguishing_fiber_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  exact
    not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_product_gt
      C E r y τ hdistinguish htol

theorem bool_to_any_recoding_distinguishing_fiber_approx_forces_product_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
      C E r y τ hdistinguish happrox

theorem bool_to_any_recoding_distinguishing_fiber_lower_bounds_force_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ loTrue loFalse : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinTolerance_boolToAnyRecoding_fiber_distinguishes
      C E r y τ loTrue loFalse hdistinguish htrue hfalse happrox

theorem bool_to_any_recoding_distinguishing_fiber_lower_bounds_block_smaller_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) (τ loTrue loFalse : Nat)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) τ := by
  exact
    not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_lowerBounds_mul_gt
      C E r y τ loTrue loFalse hdistinguish htrue hfalse htol

theorem bool_to_any_recoding_output_approx_forces_product_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ : Nat)
    (hnonconst : r true ≠ r false)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ) :
    conditionedSourceFiberProduct (Ω := Ω) C E ≤ τ := by
  exact
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
      C E r τ hnonconst happrox

theorem bool_to_any_recoding_output_lower_bounds_force_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ loTrue loFalse : Nat)
    (hnonconst : r true ≠ r false)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ) :
    loTrue * loFalse ≤ τ := by
  exact
    lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_boolToAnyRecoding_nonconstant
      C E r τ loTrue loFalse hnonconst htrue hfalse happrox

theorem bool_to_any_recoding_output_product_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ : Nat)
    (hnonconst : r true ≠ r false)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_boolToAnyRecoding_nonconstant_product_gt
      C E r τ hnonconst htol

theorem bool_to_any_recoding_output_lower_bounds_block_smaller_tolerance_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (τ loTrue loFalse : Nat)
    (hnonconst : r true ≠ r false)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_boolToAnyRecoding_nonconstant_lowerBounds_mul_gt
      C E r τ loTrue loFalse hnonconst htrue hfalse htol

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
