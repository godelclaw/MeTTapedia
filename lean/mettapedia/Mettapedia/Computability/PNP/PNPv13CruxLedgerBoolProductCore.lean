/-!
# PNP v13 crux ledger: one-bit product obstruction

A single half-mass event reused against itself is not a product-small-success
argument.
-/

namespace Mettapedia.Computability.PNP

/-- Count the number of points of `Bool` satisfying an event.  This is a
two-point finite probability numerator, avoiding any probability-library
infrastructure for the product crux test. -/
def boolEventCount (E : Bool → Prop) [DecidablePred E] : Nat :=
  (if E false then 1 else 0) + (if E true then 1 else 0)

/-- Count the number of points of `Bool` satisfying two events simultaneously. -/
def boolJointEventCount (E F : Bool → Prop)
    [DecidablePred E] [DecidablePred F] : Nat :=
  boolEventCount (fun ω => E ω ∧ F ω)

/-- The one-bit event used in the smallest product-success obstruction. -/
def boolSuccessEvent (ω : Bool) : Prop :=
  ω = true

/-- The one-bit success event is decidable by case analysis on the sample
point. -/
instance boolSuccessEvent_decidablePred : DecidablePred boolSuccessEvent := by
  intro ω
  cases ω <;> unfold boolSuccessEvent <;> infer_instance

/-- The event `ω = true` has uniform mass `1/2`, represented by numerator `1`
over the two-point sample space. -/
theorem boolSuccessEvent_count :
    boolEventCount boolSuccessEvent = 1 := by
  rfl

/-- Two identical copies of the same half-mass event still have joint mass
`1/2`, not `1/4`. -/
theorem boolSuccessEvent_joint_count :
    boolJointEventCount boolSuccessEvent boolSuccessEvent = 1 := by
  rfl

/-- Finite obstruction to a naive product-small-success step.  Both one-step
success events have numerator `1` over a two-point space, but the joint event
also has numerator `1`.  In denominator-free form, the false quarter-product
bound would require `4 * joint_count ≤ 2`. -/
theorem correlated_half_marginals_violate_quarter_product_bound :
    boolEventCount boolSuccessEvent = 1 ∧
      boolEventCount boolSuccessEvent = 1 ∧
      ¬ 4 * boolJointEventCount boolSuccessEvent boolSuccessEvent ≤ 2 := by
  refine ⟨rfl, rfl, ?_⟩
  decide

end Mettapedia.Computability.PNP
