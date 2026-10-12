import Mettapedia.Languages.C11.ExpressionPlanConstruction

/-!
# Source-generated plans for located integer expressions

The syntax retains canonical values and elaborated whole-object lvalues.
Compilation constructs occurrence identities, primitive memory operations,
data dependencies and source sequencing for arbitrary nesting. Assignment
conversion is computed once before a separate store and returned-value
occurrence. Postfix results name the original load while retaining the update;
prefix results name the converted new value. Comma includes all prior effects
in its sequence-point boundary.

This located syntax is an integer-expression component of C execution.
Ordinary source elaboration, general lvalues, branch-dependent expression
construction, calls and non-integer operators remain additional components.
The graph's kernel memory events are distinct from committed host effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.LocatedExpressions

open ObjectAccessMemory IntegerMemoryModel ExpressionEvents
open ExpressionPlanConstruction Sequencing

structure Destination where
  location : Lvalue
  type : IntegerType IntegerExtension
  formed : location.view.type = .scalar (.integer type)
  deriving DecidableEq, Repr

def destination (location : Lvalue) : Option Destination := do
  match found : integerView location.view.type with
  | none => none
  | some type => some ⟨location, type, (integerView_iff _ _).mp found⟩

theorem destination_complete (selected : Destination) : destination selected.location = some selected := by
  cases selected with
  | mk location type formed =>
      have found := (integerView_iff _ _).mpr formed
      unfold destination
      split
      · rename_i missing
        rw [found] at missing
        cases missing
      · rename_i actual observed
        have same : actual = type := Option.some.inj (observed.symm.trans found)
        cases same
        rfl

inductive Expression (model : Model) where
  | value (scalar : IntegerScalar.Value model.parameters)
  | load (location : Destination)
  | arithmetic (operator : IntegerBinaryOperator) (first second : Expression model)
  | cast (type : IntegerType IntegerExtension) (operand : Expression model)
  | assignment (location : Destination) (operand : Expression model)
  | update (location : Destination) (increment isPrefix : Bool)
  | comma (first second : Expression model)
  deriving DecidableEq, Repr

abbrev UpdateIndex := (((Fin 1 ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 2

abbrev Index {model : Model} : Expression model → Type
  | .value _ | .load _ => Fin 1
  | .arithmetic _ first second | .comma first second => (Index first ⊕ Index second) ⊕ Fin 1
  | .cast _ operand => Index operand ⊕ Fin 1
  | .assignment _ operand => (Index operand ⊕ Fin 1) ⊕ Fin 2
  | .update _ _ _ => UpdateIndex

private def indexDecEq {model : Model} (expression : Expression model) : DecidableEq (Index expression) :=
  match expression with
  | .value _ | .load _ | .update _ _ _ => inferInstance
  | .arithmetic _ first second | .comma first second =>
      letI := indexDecEq first
      letI := indexDecEq second
      inferInstance
  | .cast _ operand | .assignment _ operand =>
      letI := indexDecEq operand
      inferInstance

instance {model : Model} (expression : Expression model) : DecidableEq (Index expression) := indexDecEq expression

def updatePlan (model : Model) (location : Destination) (increment isPrefix : Bool) : Plan UpdateIndex model :=
  let old := ExpressionPlanConstruction.load (model := model) location.location
  let one := constant (IntegerScalar.logicalValue model.parameters true)
  let updated := arithmetic old one (if increment then .add else .subtract)
  let converted := ExpressionPlanConstruction.cast updated location.type
  let assigned := storeResult converted location.location
  { assigned with component := {assigned.component with
      result := if isPrefix then .inr 1 else .inl (.inl (.inl (.inl 0)))} }

def compile {model : Model} (expression : Expression model) : Plan (Index expression) model :=
  match expression with
  | .value scalar => constant scalar
  | .load location => ExpressionPlanConstruction.load location.location
  | .arithmetic operator first second => arithmetic (compile first) (compile second) operator
  | .cast type operand => ExpressionPlanConstruction.cast (compile operand) type
  | .assignment location operand =>
      storeResult (ExpressionPlanConstruction.cast (compile operand) location.type) location.location
  | .update location increment isPrefix => updatePlan model location increment isPrefix
  | .comma first second => ExpressionPlanConstruction.comma (compile first) (compile second)

/-- Source occurrence selected as the expression's value, independently of
the chronological position of its pending modifications. -/
def result {model : Model} : (expression : Expression model) → Index expression
  | .value _ | .load _ => 0
  | .arithmetic _ _ _ | .cast _ _ | .comma _ _ => .inr 0
  | .assignment _ _ => .inr 1
  | .update _ _ isPrefix => if isPrefix then .inr 1 else .inl (.inl (.inl (.inl 0)))

theorem compiled_result {model : Model} (expression : Expression model) :
    (compile expression).component.result = result expression := by
  cases expression <;> rfl

theorem compiled_inputs_ordered {model : Model} (expression : Expression model) :
    (compile expression).InputsOrdered := by
  induction expression with
  | value scalar => exact constant_inputs_ordered scalar
  | load location => exact load_inputs_ordered location.location
  | arithmetic operator first second firstIH secondIH =>
      exact arithmetic_inputs_ordered (compile first) (compile second) firstIH secondIH operator
  | cast type operand ih => exact cast_inputs_ordered (compile operand) ih type
  | assignment location operand ih =>
      exact storeResult_inputs_ordered _ (cast_inputs_ordered (compile operand) ih location.type) location.location
  | update location increment isPrefix =>
      exact storeResult_inputs_ordered _
        (cast_inputs_ordered _ (arithmetic_inputs_ordered _ _
          (load_inputs_ordered location.location)
          (constant_inputs_ordered (IntegerScalar.logicalValue model.parameters true))
          (if increment then .add else .subtract)) location.type) location.location
  | comma first second firstIH secondIH => exact comma_inputs_ordered _ _ firstIH secondIH

theorem compiled_source_valid {model : Model} (expression : Expression model) :
    (compile expression).component.evaluation.order.Valid := (compile expression).component.valid

theorem compiled_access {model : Model} (expression : Expression model) (index : Index expression) :
    (compile expression).component.evaluation.access index = ((compile expression).operation index).access :=
  (compile expression).access index

theorem compiled_occurrences_unique {model : Model} (expression : Expression model) :
    (compile expression).component.enumeration.items.Nodup := by
  induction expression with
  | value scalar => exact enumeration_fin_unique 1
  | load location => exact enumeration_fin_unique 1
  | arithmetic operator first second firstIH secondIH =>
      exact enumeration_sum_unique _ _ (enumeration_sum_unique _ _ firstIH secondIH) (enumeration_fin_unique 1)
  | cast type operand ih => exact enumeration_sum_unique _ _ ih (enumeration_fin_unique 1)
  | assignment location operand ih =>
      exact enumeration_sum_unique _ _ (enumeration_sum_unique _ _ ih (enumeration_fin_unique 1))
        (enumeration_fin_unique 2)
  | update location increment isPrefix =>
      exact enumeration_sum_unique _ _
        (enumeration_sum_unique _ _
          (enumeration_sum_unique _ _
            (enumeration_sum_unique _ _ (enumeration_fin_unique 1) (enumeration_fin_unique 1))
            (enumeration_fin_unique 1))
          (enumeration_fin_unique 1))
        (enumeration_fin_unique 2)
  | comma first second firstIH secondIH =>
      exact enumeration_sum_unique _ _ (enumeration_sum_unique _ _ firstIH secondIH) (enumeration_fin_unique 1)

theorem assignment_store_result_unsequenced {model : Model} (location : Destination) (operand : Expression model) :
    (compile (.assignment location operand)).component.evaluation.Unsequenced (.inr 0) (.inr 1) :=
  store_result_unsequenced _ _

theorem comma_orders_all {model : Model} (first second : Expression model)
    (left : Index first) (right : Index second) :
    (compile (.comma first second)).component.evaluation.order.Precedes
      (.inl (.inl left)) (.inl (.inr right)) := ExpressionPlanConstruction.comma_orders_all _ _ _ _

end Mettapedia.Languages.C11.LocatedExpressions
