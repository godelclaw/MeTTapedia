import Mathlib.Tactic

/-!
# Cardinality-only consumers and visible collection bindings

The source observer receives an ordinary list. A separate target observer can
receive a list or an internal cardinality carrier. Replacing the list preserves
all expressions made from counts, literals and ordered pairs. A surrounding
observer which also reads the bound collection distinguishes the replacement.

Admission therefore checks both the local consumer and the outer observation.
The native free-variable inventory, alias/privacy analysis, producer effects
and arithmetic bounds remain concrete correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CollectionDemand

inductive Consumer where
  | literal (value : Nat)
  | count
  | collection
  | pair (first second : Consumer)
  deriving DecidableEq, Repr

inductive Observation (A : Type) where
  | natural (value : Nat)
  | rows (values : List A)
  | internalCount (value : Nat)
  | pair (first second : Observation A)
  deriving DecidableEq, Repr

inductive Representation (A : Type) where
  | rows (values : List A)
  | counted (value : Nat)

variable {A : Type}

def source (values : List A) : Consumer → Observation A
  | .literal value => .natural value
  | .count => .natural values.length
  | .collection => .rows values
  | .pair first second => .pair (source values first) (source values second)

def target (representation : Representation A) : Consumer → Observation A
  | .literal value => .natural value
  | .count => .natural (match representation with
      | .rows values => values.length
      | .counted value => value)
  | .collection => match representation with
      | .rows values => .rows values
      | .counted value => .internalCount value
  | .pair first second => .pair (target representation first) (target representation second)

def countOnly : Consumer → Bool
  | .literal _ | .count => true
  | .collection => false
  | .pair first second => countOnly first && countOnly second

def observe (visible : Bool) (body : Consumer) : Consumer :=
  if visible then .pair body .collection else body

def admit (visible : Bool) (body : Consumer) : Bool := !visible && countOnly body

/-- Materialized target evaluation agrees for every consumer, including list reads. -/
theorem materialized_refines (values : List A) (body : Consumer) :
    target (.rows values) body = source values body := by
  induction body with
  | literal value => rfl
  | count => rfl
  | collection => rfl
  | pair first second ihFirst ihSecond => simp [target, source, ihFirst, ihSecond]

/-- Count-only syntax is a sufficient observation theorem, proved structurally. -/
theorem cardinality_refines (values : List A) (body : Consumer)
    (onlyCounts : countOnly body = true) :
    target (.counted values.length) body = source values body := by
  induction body with
  | literal value => rfl
  | count => rfl
  | collection => simp [countOnly] at onlyCounts
  | pair first second ihFirst ihSecond =>
      simp only [countOnly, Bool.and_eq_true] at onlyCounts
      simp [target, source, ihFirst onlyCounts.1, ihSecond onlyCounts.2]

/-- The outer observation participates in admission, not only the let body. -/
theorem admitted_preserves_readout (values : List A) (visible : Bool) (body : Consumer)
    (admitted : admit visible body = true) :
    target (.counted values.length) (observe visible body) =
      source values (observe visible body) := by
  cases visible with
  | false =>
      simp only [admit, Bool.not_false, Bool.true_and] at admitted
      simpa [observe] using cardinality_refines values body admitted
  | true => simp [admit] at admitted

/-- Even a locally count-only body cannot hide an outer read of the list. -/
theorem visible_binding_refutes_fusion (values : List A) (body : Consumer) :
    target (.counted values.length) (observe true body) ≠
      source values (observe true body) := by
  simp [observe, target, source]

namespace Controls

theorem root_visible_counterexample :
    source [1, 2] (observe true .count) = .pair (.natural 2) (.rows [1, 2]) ∧
    target (.counted 2) (observe true .count) =
      (.pair (.natural 2) (.internalCount 2) : Observation Nat) := by decide

theorem repeated_private_counts :
    target (.counted 3) (.pair .count (.pair (.literal 7) .count)) =
      source [4, 4, 9] (.pair .count (.pair (.literal 7) .count)) := by decide

end Controls
end Mettapedia.Machines.CollectionDemand

#print axioms Mettapedia.Machines.CollectionDemand.materialized_refines
#print axioms Mettapedia.Machines.CollectionDemand.cardinality_refines
#print axioms Mettapedia.Machines.CollectionDemand.admitted_preserves_readout
#print axioms Mettapedia.Machines.CollectionDemand.visible_binding_refutes_fusion
#print axioms Mettapedia.Machines.CollectionDemand.Controls.root_visible_counterexample
#print axioms Mettapedia.Machines.CollectionDemand.Controls.repeated_private_counts
