import Mettapedia.Computability.PNP.PNPv13CruxLedgerBoolProductCore

/-!
# PNP v13 crux ledger: Boolean-square sequential product model

The four-point Boolean square separates a valid sequential half-success
interface from correlated reuse of the same half-mass event.
-/

namespace Mettapedia.Computability.PNP

/-- Count the number of points of `Bool × Bool` satisfying an event.  This is
the denominator-free numerator for the four-point uniform sample space. -/
def boolPairEventCount (E : Bool × Bool → Prop) [DecidablePred E] : Nat :=
  (if E (false, false) then 1 else 0) +
  (if E (false, true) then 1 else 0) +
  (if E (true, false) then 1 else 0) +
  (if E (true, true) then 1 else 0)

/-- Count simultaneous satisfaction on the four-point Boolean square. -/
def boolPairJointEventCount (E F : Bool × Bool → Prop)
    [DecidablePred E] [DecidablePred F] : Nat :=
  boolPairEventCount (fun ω => E ω ∧ F ω)

/-- Denominator-free sequential half-success on `Bool × Bool`: the first event
has mass at most `1/2`, and the second has conditional mass at most `1/2`
inside the first event. -/
def SequentialHalfOnBoolPair (E F : Bool × Bool → Prop)
    [DecidablePred E] [DecidablePred F] : Prop :=
  2 * boolPairEventCount E ≤ 4 ∧
    2 * boolPairJointEventCount E F ≤ boolPairEventCount E

/-- Sequential conditional half-success implies the two-step product bound.
This is the positive interface the v13 product-small-success step must supply,
in contrast to the unconditional marginal countermodel above. -/
theorem boolPair_product_bound_of_sequentialHalf
    (E F : Bool × Bool → Prop) [DecidablePred E] [DecidablePred F]
    (h : SequentialHalfOnBoolPair E F) :
    4 * boolPairJointEventCount E F ≤ 4 := by
  rcases h with ⟨hE, hF⟩
  have hmul := Nat.mul_le_mul_left 2 hF
  calc
    4 * boolPairJointEventCount E F =
        2 * (2 * boolPairJointEventCount E F) := by
          rw [show (4 : Nat) = 2 * 2 by rfl, Nat.mul_assoc]
    _ ≤ 2 * boolPairEventCount E := hmul
    _ ≤ 4 := hE

/-- First-coordinate success on the Boolean square. -/
def boolPairFirstSuccess (ω : Bool × Bool) : Prop :=
  ω.1 = true

/-- Second-coordinate success on the Boolean square. -/
def boolPairSecondSuccess (ω : Bool × Bool) : Prop :=
  ω.2 = true

instance boolPairFirstSuccess_decidablePred :
    DecidablePred boolPairFirstSuccess := by
  intro ω
  cases ω with
  | mk a b =>
      cases a <;> cases b <;> unfold boolPairFirstSuccess <;> infer_instance

instance boolPairSecondSuccess_decidablePred :
    DecidablePred boolPairSecondSuccess := by
  intro ω
  cases ω with
  | mk a b =>
      cases a <;> cases b <;> unfold boolPairSecondSuccess <;> infer_instance

/-- Each coordinate-success event has numerator `2` over the four-point square. -/
theorem boolPairFirstSuccess_count :
    boolPairEventCount boolPairFirstSuccess = 2 := by
  rfl

/-- Each coordinate-success event has numerator `2` over the four-point square. -/
theorem boolPairSecondSuccess_count :
    boolPairEventCount boolPairSecondSuccess = 2 := by
  rfl

/-- Independent coordinate-success events have numerator `1` intersection over
the four-point square. -/
theorem boolPairFirstSecondSuccess_joint_count :
    boolPairJointEventCount boolPairFirstSuccess boolPairSecondSuccess = 1 := by
  rfl

/-- Coordinate-success events satisfy the sequential half-success interface. -/
theorem boolPairFirstSecondSuccess_sequentialHalf :
    SequentialHalfOnBoolPair boolPairFirstSuccess boolPairSecondSuccess := by
  constructor <;> decide

/-- The positive interface gives the expected denominator-free product bound on
the independent-coordinate finite model. -/
theorem boolPairFirstSecondSuccess_product_bound :
    4 * boolPairJointEventCount boolPairFirstSuccess boolPairSecondSuccess ≤ 4 := by
  exact boolPair_product_bound_of_sequentialHalf _ _
    boolPairFirstSecondSuccess_sequentialHalf

/-- Reusing the same coordinate twice gives half-mass marginals but violates the
quarter-product bound on the four-point square. -/
theorem boolPair_correlated_half_marginals_violate_product_bound :
    boolPairEventCount boolPairFirstSuccess = 2 ∧
      boolPairEventCount boolPairFirstSuccess = 2 ∧
      ¬ 4 * boolPairJointEventCount boolPairFirstSuccess boolPairFirstSuccess ≤ 4 := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- The correlated finite model fails exactly the second, conditional half-step:
inside the first event, the repeated event has conditional mass `1`, not
`1/2`. -/
theorem boolPair_correlated_marginals_fail_sequentialHalf :
    ¬ SequentialHalfOnBoolPair boolPairFirstSuccess boolPairFirstSuccess := by
  intro h
  exact
    (by
      decide :
        ¬ 2 * boolPairJointEventCount boolPairFirstSuccess boolPairFirstSuccess ≤
          boolPairEventCount boolPairFirstSuccess) h.2

end Mettapedia.Computability.PNP
