import Mettapedia.Languages.Datalog.Comparisons

/-! Integer guard controls exercise the shared guard evaluator. This component
does not select or qualify a native Souffle comparison profile. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.Comparisons.Controls

def integerRelation (operator : ComparisonOperator) (left right : Value) : Prop :=
  match left, right with
  | .number first, .number second =>
      match operator with
      | .equal => first = second
      | .different => first ≠ second
      | .less => first < second
      | .lessEqual => first ≤ second
      | .greater => second < first
      | .greaterEqual => second ≤ first
  | _, _ => False

def integerCheck (operator : ComparisonOperator) (left right : Value) : Bool :=
  match left, right with
  | .number first, .number second =>
      match operator with
      | .equal => decide (first = second)
      | .different => decide (first ≠ second)
      | .less => decide (first < second)
      | .lessEqual => decide (first ≤ second)
      | .greater => decide (second < first)
      | .greaterEqual => decide (second ≤ first)
  | _, _ => false

def integerPolicy : Policy where
  Holds := integerRelation
  check := integerCheck
  exact := by
    intro operator left right
    cases left <;> cases right <;> cases operator <;> simp [integerRelation, integerCheck]

def guard : Comparison := ⟨.less, .var "X", .literal (.number 3)⟩

theorem missing_is_not_false : eval? integerPolicy [] guard = none := by decide +kernel

theorem true_guard : eval? integerPolicy [("X", .number 2)] guard = some true := by decide +kernel

theorem false_guard : eval? integerPolicy [("X", .number 4)] guard = some false := by decide +kernel

theorem repeated_variable_equality :
    eval? integerPolicy [("X", .number (-7))] ⟨.equal, .var "X", .var "X"⟩ = some true := by
  decide +kernel

theorem no_binding_from_a_guard :
    eval? integerPolicy [] ⟨.equal, .var "X", .literal (.number 1)⟩ = none := by decide +kernel

theorem guards_keep_their_common_environment :
    all? integerPolicy [("X", .number 2)]
        [⟨.greater, .var "X", .literal (.number 0)⟩, guard] = some true ∧
      all? integerPolicy [("X", .number 4)]
        [⟨.greater, .var "X", .literal (.number 0)⟩, guard] = some false := by decide +kernel

theorem empty_guards_succeed : all? integerPolicy [] [] = some true := by decide +kernel

#print axioms integerPolicy
#print axioms missing_is_not_false
#print axioms guards_keep_their_common_environment

end Mettapedia.Languages.Datalog.Comparisons.Controls
