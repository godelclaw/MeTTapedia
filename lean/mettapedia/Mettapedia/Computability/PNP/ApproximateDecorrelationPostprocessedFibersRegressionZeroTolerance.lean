import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersTrue
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersFalse
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseProduct
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseSourceBounds
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseSourceStrict
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersZeroTolerance

/-!
# Zero-tolerance fiber regression wrappers
-/

namespace Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression

open Mettapedia.Computability.PNP

theorem coupled_nonconstant_zero_tolerance_blocks_approx_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F 0 := by
  exact
    not_countIndependentWithinTolerance_zero_of_coupled_nonconstant_on_condition
      C E F hcouple hpos hneg

theorem anticoupled_nonconstant_zero_tolerance_blocks_approx_regression
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F 0 := by
  exact
    not_countIndependentWithinTolerance_zero_of_anticoupled_nonconstant_on_condition
      C E F hanti hpos hneg

theorem bool_to_any_recoding_distinguishing_fiber_zero_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) 0 := by
  exact
    not_countIndependentWithinTolerance_zero_of_boolToAnyRecoding_fiber_distinguishes
      C E r y hdistinguish hpos hneg

theorem bool_to_any_recoding_output_zero_tolerance_blocks_approx_regression
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hnonconst : r true ≠ r false)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_boolToAnyRecoding_nonconstant
      C E r hnonconst hpos hneg

theorem coinwise_true_fiber_output_zero_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (hpos : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hneg : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber
      C E r y htrue hfalse hpos hneg

theorem coinwise_false_fiber_output_zero_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (hpos : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hneg : 0 < finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber
      C E r y htrue hfalse hpos hneg

theorem coinwise_true_fiber_source_nonconstant_zero_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber_sourceNonconstant
      C E r y htrue hfalse hpos hneg

theorem coinwise_false_fiber_source_nonconstant_zero_tolerance_blocks_approx_regression
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  exact
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber_sourceNonconstant
      C E r y htrue hfalse hpos hneg

end Mettapedia.Computability.PNP.ApproximateDecorrelationObstructionRegression
