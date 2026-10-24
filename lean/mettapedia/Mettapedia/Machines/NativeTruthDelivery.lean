import Mathlib.Data.List.Basic

/-!
# Dialect truth at a completed native boundary

Native truth and the PeTTa truth symbols have the same Boolean meaning but
are different runtime constructors. Delivery must establish the dialect's
representation before an ordinary constructor matcher consumes the value.
The conversion is shallow: expression-valued data is never interpreted.
This models the value protocol, not native handler or C memory conformance.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeTruthDelivery

inductive Name where
  | truth | falsity | other (name : String)
  deriving DecidableEq

inductive Value where
  | nativeTruth (value : Bool)
  | symbol (name : Name)
  | number (value : Int)
  | text (value : String)
  | expression (children : List Value)

inductive Dialect where | petta | he
  deriving DecidableEq

def truthSymbol (value : Bool) : Value :=
  .symbol (if value then .truth else .falsity)

def finalize (dialect : Dialect) : Value → Value
  | .nativeTruth value => if dialect = .petta then truthSymbol value else .nativeTruth value
  | value => value

def truthMeaning : Value → Option Bool
  | .nativeTruth value => some value
  | .symbol .truth => some true
  | .symbol .falsity => some false
  | _ => none

/-- The ordinary constructor consumer does not equate two runtime tags. -/
def symbolCase : Value → Option Bool
  | .symbol .truth => some true
  | .symbol .falsity => some false
  | _ => none

theorem finalization_idempotent (dialect : Dialect) (value : Value) :
    finalize dialect (finalize dialect value) = finalize dialect value := by
  cases dialect <;> cases value <;> simp [finalize, truthSymbol]

theorem truth_meaning_preserved (dialect : Dialect) (value : Value) :
    truthMeaning (finalize dialect value) = truthMeaning value := by
  cases value with
  | nativeTruth truth => cases dialect <;> cases truth <;> rfl
  | symbol name => rfl
  | number value => rfl
  | text value => rfl
  | expression children => rfl

theorem petta_native_truth_consumed (value : Bool) :
    symbolCase (finalize .petta (.nativeTruth value)) = some value := by
  cases value <;> rfl

theorem native_truth_is_not_a_symbol (value : Bool) :
    symbolCase (.nativeTruth value) = none := rfl

theorem completed_expression_unchanged (dialect : Dialect) (children : List Value) :
    finalize dialect (.expression children) = .expression children := rfl

theorem text_unchanged (dialect : Dialect) (text : String) :
    finalize dialect (.text text) = .text text := rfl

inductive Form where | completed | expression | frontier
  deriving DecidableEq

/-- The prepared seam accepts explicit completed data and legacy atomic
native scalars; an expression result or frontier requires its own consumer. -/
def deliver (dialect : Dialect) (form : Form) (value : Value) : Option Value :=
  match form, value with
  | .completed, value => some (finalize dialect value)
  | .expression, .nativeTruth truth => some (finalize dialect (.nativeTruth truth))
  | .expression, .number number => some (.number number)
  | .expression, .text text => some (.text text)
  | _, _ => none

theorem both_truth_forms_agree (dialect : Dialect) (truth : Bool) :
    deliver dialect .completed (.nativeTruth truth) =
      deliver dialect .expression (.nativeTruth truth) := rfl

theorem delivery_truth_meaning (dialect : Dialect) (form : Form)
    (value result : Value) (delivered : deliver dialect form value = some result) :
    truthMeaning result = truthMeaning value := by
  cases form with
  | completed =>
      simp only [deliver, Option.some.injEq] at delivered
      subst result
      exact truth_meaning_preserved dialect value
  | expression =>
      cases value with
      | nativeTruth truth =>
          simp only [deliver, Option.some.injEq] at delivered
          subst result
          exact truth_meaning_preserved dialect (.nativeTruth truth)
      | symbol name => simp [deliver] at delivered
      | number number =>
          simp only [deliver, Option.some.injEq] at delivered
          subst result
          rfl
      | text text =>
          simp only [deliver, Option.some.injEq] at delivered
          subst result
          rfl
      | expression children => simp [deliver] at delivered
  | frontier => cases value <;> simp [deliver] at delivered

theorem legacy_expression_refused (dialect : Dialect) (children : List Value) :
    deliver dialect .expression (.expression children) = none := rfl

theorem frontier_refused (dialect : Dialect) (value : Value) :
    deliver dialect .frontier value = none := by cases value <;> rfl

namespace Controls

theorem true_pattern_repaired :
    symbolCase (.nativeTruth true) ≠
      symbolCase (finalize .petta (.nativeTruth true)) := by decide

theorem boolean_looking_string_remains_string :
    symbolCase (finalize .petta (.text "True")) = none := rfl

theorem completed_call_shaped_data_remains_data :
    deliver .petta .completed
      (.expression [.symbol (.other "function"), .nativeTruth true]) =
      some (.expression [.symbol (.other "function"), .nativeTruth true]) := rfl

end Controls
end Mettapedia.Machines.NativeTruthDelivery
