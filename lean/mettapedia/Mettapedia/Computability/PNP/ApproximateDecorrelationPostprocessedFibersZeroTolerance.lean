import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseProduct
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseSourceBounds
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseSourceStrict

/-!
# Zero-tolerance postprocessed fiber obstructions
-/

namespace Mettapedia.Computability.PNP

/-- The zero-tolerance approximate repair is already blocked by nondegenerate
coupled conditioning. -/
theorem not_countIndependentWithinTolerance_zero_of_coupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F 0 := by
  apply not_countIndependentWithinTolerance_of_coupled_product_gt C E F 0 hcouple
  simpa using Nat.mul_pos hpos hneg

/-- The zero-tolerance approximate repair is already blocked by nondegenerate
anti-coupled conditioning. -/
theorem not_countIndependentWithinTolerance_zero_of_anticoupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E F 0 := by
  apply not_countIndependentWithinTolerance_of_anticoupled_product_gt C E F 0 hanti
  simpa using Nat.mul_pos hpos hneg

/-- A distinguishing arbitrary-codomain deterministic output fiber is blocked
at zero tolerance whenever the conditioned source bit is nondegenerate. -/
theorem not_countIndependentWithinTolerance_zero_of_boolToAnyRecoding_fiber_distinguishes
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinTolerance (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) 0 := by
  apply
    not_countIndependentWithinTolerance_of_boolToAnyRecoding_fiber_distinguishes_product_gt
      C E r y 0 hdistinguish
  simpa using Nat.mul_pos hpos hneg

/-- A nonconstant deterministic output variable is blocked at zero tolerance
whenever the conditioned source bit is nondegenerate. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_boolToAnyRecoding_nonconstant
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hnonconst : r true ≠ r false)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω) C E
      (fun ω => r (decide (E ω))) 0 := by
  apply
    not_countIndependentWithinToleranceOutput_of_boolToAnyRecoding_nonconstant_product_gt
      C E r 0 hnonconst
  simpa using Nat.mul_pos hpos hneg

/-- A finite-coin randomized recoding with a uniform true-side distinguishing
output fiber is blocked at zero tolerance when the lifted conditioned source
bit is nondegenerate. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber
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
  apply
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_product_gt
      C E r y 0 htrue hfalse
  simpa using Nat.mul_pos hpos hneg

/-- A finite-coin randomized recoding with a uniform false-side distinguishing
output fiber is blocked at zero tolerance when the lifted conditioned source
bit is nondegenerate. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber
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
  apply
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_product_gt
      C E r y 0 htrue hfalse
  simpa using Nat.mul_pos hpos hneg

/-- Source-side nondegeneracy blocks a uniform true-side finite-coin
distinguishing fiber at zero tolerance whenever the coin space is nonempty. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber_sourceNonconstant
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
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber
      C E r y htrue hfalse
      (finiteEventCount_fst_lift_pos_of_pos (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω) hpos)
      (finiteEventCount_fst_lift_pos_of_pos (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ ¬ E ω) hneg)

/-- Source-side nondegeneracy blocks a uniform false-side finite-coin
distinguishing fiber at zero tolerance whenever the coin space is nonempty. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber_sourceNonconstant
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
    not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber
      C E r y htrue hfalse
      (finiteEventCount_fst_lift_pos_of_pos (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω) hpos)
      (finiteEventCount_fst_lift_pos_of_pos (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ ¬ E ω) hneg)


end Mettapedia.Computability.PNP
