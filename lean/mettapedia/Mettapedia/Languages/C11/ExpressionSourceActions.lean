import Mettapedia.Languages.C11.ExpressionSourceOrder

/-!
# Source rules for located integer-expression occurrences

The inductive action rules retain each operand's occurrence identity and
identify newly constructed value, conversion and memory operations. The
compiler's action map is sound and complete for those rules for arbitrary
expression depth. Update rules keep the old read, promoted arithmetic,
destination conversion, store and returned-value occurrence distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ExpressionSourceActions

open IntegerMemoryModel LocatedExpressions ExpressionEvents

variable {model : Model}

abbrev oldRead : UpdateIndex := .inl (.inl (.inl (.inl 0)))
abbrev oneValue : UpdateIndex := .inl (.inl (.inl (.inr 0)))
abbrev updateValue : UpdateIndex := .inl (.inl (.inr 0))
abbrev convertedUpdate : UpdateIndex := .inl (.inr 0)

inductive UpdateAction (model : Model) (location : Destination) (increment : Bool) :
    UpdateIndex → Operation UpdateIndex model → Prop where
  | read : UpdateAction model location increment oldRead (.load location.location)
  | one : UpdateAction model location increment oneValue (.constant (IntegerScalar.logicalValue model.parameters true))
  | arithmetic : UpdateAction model location increment updateValue
      (.binary (if increment then .add else .subtract) oldRead oneValue)
  | conversion : UpdateAction model location increment convertedUpdate (.cast location.type updateValue)
  | store : UpdateAction model location increment (.inr 0) (.store location.location convertedUpdate)
  | value : UpdateAction model location increment (.inr 1) (.copy convertedUpdate)

inductive Action : (expression : Expression model) → Index expression → Operation (Index expression) model → Prop where
  | value (scalar : IntegerScalar.Value model.parameters) : Action (.value scalar) 0 (.constant scalar)
  | load (location : Destination) : Action (.load location) 0 (.load location.location)
  | arithmeticLeft (operator : IntegerBinaryOperator) (first second : Expression model)
      (index : Index first) (operation : Operation (Index first) model) (child : Action first index operation) :
      Action (.arithmetic operator first second) (.inl (.inl index)) (operation.map (Sum.inl ∘ Sum.inl))
  | arithmeticRight (operator : IntegerBinaryOperator) (first second : Expression model)
      (index : Index second) (operation : Operation (Index second) model) (child : Action second index operation) :
      Action (.arithmetic operator first second) (.inl (.inr index)) (operation.map (Sum.inl ∘ Sum.inr))
  | arithmeticResult (operator : IntegerBinaryOperator) (first second : Expression model) :
      Action (.arithmetic operator first second) (.inr 0)
        (.binary operator (.inl (.inl (result first))) (.inl (.inr (result second))))
  | castChild (type : IntegerType IntegerExtension) (operand : Expression model)
      (index : Index operand) (operation : Operation (Index operand) model) (child : Action operand index operation) :
      Action (.cast type operand) (.inl index) (operation.map Sum.inl)
  | castResult (type : IntegerType IntegerExtension) (operand : Expression model) :
      Action (.cast type operand) (.inr 0) (.cast type (.inl (result operand)))
  | assignmentChild (location : Destination) (operand : Expression model)
      (index : Index operand) (operation : Operation (Index operand) model) (child : Action operand index operation) :
      Action (.assignment location operand) (.inl (.inl index)) (operation.map (Sum.inl ∘ Sum.inl))
  | assignmentConversion (location : Destination) (operand : Expression model) :
      Action (.assignment location operand) (.inl (.inr 0)) (.cast location.type (.inl (.inl (result operand))))
  | assignmentStore (location : Destination) (operand : Expression model) :
      Action (.assignment location operand) (.inr 0) (.store location.location (.inl (.inr 0)))
  | assignmentValue (location : Destination) (operand : Expression model) :
      Action (.assignment location operand) (.inr 1) (.copy (.inl (.inr 0)))
  | update (location : Destination) (increment isPrefix : Bool) (index : UpdateIndex)
      (operation : Operation UpdateIndex model) (rule : UpdateAction model location increment index operation) :
      Action (.update location increment isPrefix) index operation
  | commaLeft (first second : Expression model) (index : Index first)
      (operation : Operation (Index first) model) (child : Action first index operation) :
      Action (.comma first second) (.inl (.inl index)) (operation.map (Sum.inl ∘ Sum.inl))
  | commaRight (first second : Expression model) (index : Index second)
      (operation : Operation (Index second) model) (child : Action second index operation) :
      Action (.comma first second) (.inl (.inr index)) (operation.map (Sum.inl ∘ Sum.inr))
  | commaValue (first second : Expression model) :
      Action (.comma first second) (.inr 0) (.copy (.inl (.inr (result second))))

private theorem map_map {First Second Third : Type} (operation : Operation First model)
    (first : First → Second) (second : Second → Third) :
    (operation.map first).map second = operation.map (second ∘ first) := by
  cases operation <;> rfl

private theorem update_actions (model : Model) (location : Destination) (increment isPrefix : Bool)
    (index : UpdateIndex) : UpdateAction model location increment index ((updatePlan model location increment isPrefix).operation index) := by
  cases index with
  | inl index =>
      cases index with
      | inl index =>
          cases index with
          | inl index =>
              cases index with
              | inl index => have same : index = 0 := Fin.eq_zero index; subst index; exact .read
              | inr index => have same : index = 0 := Fin.eq_zero index; subst index; exact .one
          | inr index => have same : index = 0 := Fin.eq_zero index; subst index; exact .arithmetic
      | inr index => have same : index = 0 := Fin.eq_zero index; subst index; exact .conversion
  | inr index =>
      by_cases zero : index.val = 0
      · have same : index = 0 := Fin.ext zero; subst index; exact .store
      · have same : index = 1 := Fin.ext (by omega); subst index; exact .value

theorem compiled_action (expression : Expression model) (index : Index expression) :
    Action expression index ((compile expression).operation index) := by
  induction expression with
  | value scalar => have same : index = 0 := Fin.eq_zero index; subst index; exact .value scalar
  | load location => have same : index = 0 := Fin.eq_zero index; subst index; exact .load location
  | arithmetic operator first second firstIH secondIH =>
      cases index with
      | inl index =>
          cases index with
          | inl index => exact .arithmeticLeft _ _ _ _ _ (firstIH index)
          | inr index => exact .arithmeticRight _ _ _ _ _ (secondIH index)
      | inr index =>
          have same : index = 0 := Fin.eq_zero index
          subst index
          simpa only [compile, ExpressionPlanConstruction.arithmetic, compiled_result] using
            Action.arithmeticResult (model := model) operator first second
  | cast type operand ih =>
      cases index with
      | inl index => exact .castChild _ _ _ _ (ih index)
      | inr index =>
          have same : index = 0 := Fin.eq_zero index
          subst index
          simpa only [compile, ExpressionPlanConstruction.cast, compiled_result] using Action.castResult (model := model) type operand
  | assignment location operand ih =>
      cases index with
      | inl index =>
          cases index with
          | inl index =>
              simpa only [compile, ExpressionPlanConstruction.storeResult, ExpressionPlanConstruction.cast, map_map] using
                Action.assignmentChild location operand index ((compile operand).operation index) (ih index)
          | inr index =>
              have same : index = 0 := Fin.eq_zero index
              subst index
              simpa only [compile, ExpressionPlanConstruction.storeResult, ExpressionPlanConstruction.cast,
                Operation.map, compiled_result] using Action.assignmentConversion (model := model) location operand
      | inr index =>
          by_cases zero : index.val = 0
          · have same : index = 0 := Fin.ext zero; subst index; exact .assignmentStore _ _
          · have same : index = 1 := Fin.ext (by omega); subst index; exact .assignmentValue _ _
  | update location increment isPrefix => exact .update _ _ _ _ _ (update_actions model location increment isPrefix index)
  | comma first second firstIH secondIH =>
      cases index with
      | inl index =>
          cases index with
          | inl index => exact .commaLeft _ _ _ _ (firstIH index)
          | inr index => exact .commaRight _ _ _ _ (secondIH index)
      | inr index =>
          have same : index = 0 := Fin.eq_zero index
          subst index
          simpa only [compile, ExpressionPlanConstruction.comma, compiled_result] using Action.commaValue (model := model) first second

theorem update_complete (location : Destination) (increment isPrefix : Bool) (index : UpdateIndex)
    (operation : Operation UpdateIndex model) (rule : UpdateAction model location increment index operation) :
    (updatePlan model location increment isPrefix).operation index = operation := by
  cases rule <;> rfl

theorem action_complete (expression : Expression model) (index : Index expression)
    (operation : Operation (Index expression) model) (rule : Action expression index operation) :
    (compile expression).operation index = operation := by
  induction rule with
  | value scalar => rfl
  | load location => rfl
  | arithmeticLeft operator first second index operation child ih =>
      exact congrArg (Operation.map (Sum.inl ∘ Sum.inl)) ih
  | arithmeticRight operator first second index operation child ih =>
      exact congrArg (Operation.map (Sum.inl ∘ Sum.inr)) ih
  | arithmeticResult operator first second => simp only [compile, ExpressionPlanConstruction.arithmetic, compiled_result]
  | castChild type operand index operation child ih => exact congrArg (Operation.map Sum.inl) ih
  | castResult type operand => simp only [compile, ExpressionPlanConstruction.cast, compiled_result]
  | assignmentChild location operand index operation child ih =>
      simp only [compile, ExpressionPlanConstruction.storeResult, ExpressionPlanConstruction.cast, map_map, ih]
  | assignmentConversion location operand =>
      simp only [compile, ExpressionPlanConstruction.storeResult, ExpressionPlanConstruction.cast, Operation.map, compiled_result]
  | assignmentStore location operand => rfl
  | assignmentValue location operand => rfl
  | update location increment isPrefix index operation rule => exact update_complete _ _ _ _ _ rule
  | commaLeft first second index operation child ih => exact congrArg (Operation.map (Sum.inl ∘ Sum.inl)) ih
  | commaRight first second index operation child ih => exact congrArg (Operation.map (Sum.inl ∘ Sum.inr)) ih
  | commaValue first second => simp only [compile, ExpressionPlanConstruction.comma, compiled_result]

theorem compiled_action_iff (expression : Expression model) (index : Index expression)
    (operation : Operation (Index expression) model) :
    (compile expression).operation index = operation ↔ Action expression index operation := by
  constructor
  · rintro rfl; exact compiled_action expression index
  · exact action_complete expression index operation

end Mettapedia.Languages.C11.ExpressionSourceActions
