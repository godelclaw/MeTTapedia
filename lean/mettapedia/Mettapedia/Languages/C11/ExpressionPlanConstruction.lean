import Mettapedia.Languages.C11.ExpressionEvents

/-!
# Constructed occurrence plans for located integer expressions

These constructors retain every operand occurrence and its existing source
sequencing. Pure operator results follow operand values, while an assignment
store and returned value are distinct occurrences following one conversion.
The comma constructor orders all occurrences of its first operand before
its second operand. Renaming preserves operation inputs and object identity.

Every data dependency in these plans is a sequencing predecessor. The
constructors do not order unrelated operand modifications. In particular,
choosing a chronological schedule cannot remove a source-level conflict.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ExpressionPlanConstruction

open ObjectAccessMemory IntegerMemoryModel ExpressionEvents ValueSequencing Sequencing

variable {First Second : Type} {model : Model}

theorem enumeration_sum_unique (first : Enumeration First) (second : Enumeration Second)
    (firstUnique : first.items.Nodup) (secondUnique : second.items.Nodup) :
    (first.sum second).items.Nodup := by
  apply List.nodup_append.mpr
  refine ⟨firstUnique.map Sum.inl_injective, secondUnique.map Sum.inr_injective, ?_⟩
  intro left leftPresent right rightPresent
  obtain ⟨originalLeft, _, rfl⟩ := List.mem_map.mp leftPresent
  obtain ⟨originalRight, _, rfl⟩ := List.mem_map.mp rightPresent
  intro same
  cases same

theorem enumeration_fin_unique (count : Nat) : (Enumeration.fin count).items.Nodup := by
  exact List.nodup_finRange count

def constant (scalar : IntegerScalar.Value model.parameters) : Plan (Fin 1) model where
  component := leaf .other
  operation _ := .constant scalar
  access _ := rfl

def load (location : Lvalue) : Plan (Fin 1) model where
  component := leaf location.readEvent
  operation _ := .load location
  access _ := rfl

def cast [DecidableEq First] (operand : Plan First model) (type : IntegerType IntegerExtension) :
    Plan (First ⊕ Fin 1) model where
  component := unary operand.component .other
  operation
    | .inl index => (operand.operation index).map Sum.inl
    | .inr _ => .cast type (.inl operand.component.result)
  access := by
    intro index
    cases index with
    | inl index => simpa only [unary, Sum.elim_inl, Operation.map_access] using operand.access index
    | inr index => rfl

def arithmetic [DecidableEq First] [DecidableEq Second]
    (first : Plan First model) (second : Plan Second model) (operator : IntegerBinaryOperator) :
    Plan ((First ⊕ Second) ⊕ Fin 1) model where
  component := binary first.component second.component
  operation
    | .inl (.inl index) => (first.operation index).map (Sum.inl ∘ Sum.inl)
    | .inl (.inr index) => (second.operation index).map (Sum.inl ∘ Sum.inr)
    | .inr _ => .binary operator (.inl (.inl first.component.result)) (.inl (.inr second.component.result))
  access := by
    intro index
    cases index with
    | inl index =>
        cases index with
        | inl index => simpa only [binary, Sum.elim_inl, Operation.map_access] using first.access index
        | inr index => simpa only [binary, Sum.elim_inl, Sum.elim_inr, Operation.map_access] using second.access index
    | inr index => rfl

/-- The input already has its destination type. Conversion is a predecessor
shared by the separate store and returned-value occurrences. -/
def storeResult [DecidableEq First] (operand : Plan First model) (location : Lvalue) :
    Plan (First ⊕ Fin 2) model where
  component := {
    indexEq := inferInstance
    enumeration := operand.component.enumeration.sum (.fin 2)
    evaluation := ⟨afterRoots (Fin 2) operand.component.evaluation.order [operand.component.result],
      Sum.elim operand.component.evaluation.access (fun index => if index.val = 0 then location.writeEvent else .other)⟩
    valid := afterRoots_valid _ _ _ operand.component.valid
    result := .inr 1
  }
  operation
    | .inl index => (operand.operation index).map Sum.inl
    | .inr index => if index.val = 0 then .store location (.inl operand.component.result)
      else .copy (.inl operand.component.result)
  access := by
    intro index
    cases index with
    | inl index => simpa only [Sum.elim_inl, Operation.map_access] using operand.access index
    | inr index =>
        simp only [Sum.elim_inr]
        split <;> simp_all [Operation.access]

def comma [DecidableEq First] [DecidableEq Second]
    (first : Plan First model) (second : Plan Second model) :
    Plan ((First ⊕ Second) ⊕ Fin 1) model where
  component := sequencePoint first.component second.component
  operation
    | .inl (.inl index) => (first.operation index).map (Sum.inl ∘ Sum.inl)
    | .inl (.inr index) => (second.operation index).map (Sum.inl ∘ Sum.inr)
    | .inr _ => .copy (.inl (.inr second.component.result))
  access := by
    intro index
    cases index with
    | inl index =>
        cases index with
        | inl index => simpa only [sequencePoint, Sum.elim_inl, Operation.map_access] using first.access index
        | inr index => simpa only [sequencePoint, Sum.elim_inl, Sum.elim_inr, Operation.map_access] using second.access index
    | inr index => rfl

theorem constant_inputs_ordered (scalar : IntegerScalar.Value model.parameters) :
    (constant scalar).InputsOrdered := by
  intro index source present
  cases present

theorem load_inputs_ordered (location : Lvalue) : (load (model := model) location).InputsOrdered := by
  intro index source present
  cases present

theorem cast_inputs_ordered [DecidableEq First] (operand : Plan First model)
    (ordered : operand.InputsOrdered) (type : IntegerType IntegerExtension) :
    (cast operand type).InputsOrdered := by
  intro index source present
  cases index with
  | inl index =>
      simp only [cast, Operation.map_inputs, List.mem_map] at present
      obtain ⟨original, present, rfl⟩ := present
      exact ordered index original present
  | inr index =>
      simp only [cast, Operation.inputs, List.mem_singleton] at present
      subst source
      simp [cast, unary, Order.Precedes, afterRoots, predecessors]

theorem arithmetic_inputs_ordered [DecidableEq First] [DecidableEq Second]
    (first : Plan First model) (second : Plan Second model)
    (orderedFirst : first.InputsOrdered) (orderedSecond : second.InputsOrdered)
    (operator : IntegerBinaryOperator) : (arithmetic first second operator).InputsOrdered := by
  intro index source present
  cases index with
  | inl index =>
      cases index with
      | inl index =>
          simp only [arithmetic, Operation.map_inputs, List.mem_map] at present
          obtain ⟨original, present, rfl⟩ := present
          exact orderedFirst index original present
      | inr index =>
          simp only [arithmetic, Operation.map_inputs, List.mem_map] at present
          obtain ⟨original, present, rfl⟩ := present
          exact orderedSecond index original present
  | inr index =>
      simp only [arithmetic, Operation.inputs, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl
      all_goals simp [arithmetic, binary, Order.Precedes, afterRoots, predecessors]

theorem storeResult_inputs_ordered [DecidableEq First] (operand : Plan First model)
    (ordered : operand.InputsOrdered) (location : Lvalue) : (storeResult operand location).InputsOrdered := by
  intro index source present
  cases index with
  | inl index =>
      simp only [storeResult, Operation.map_inputs, List.mem_map] at present
      obtain ⟨original, present, rfl⟩ := present
      exact ordered index original present
  | inr index =>
      simp only [storeResult] at present
      split at present <;> simp only [Operation.inputs, List.mem_singleton] at present
      all_goals
        subst source
        simp [storeResult, Order.Precedes, afterRoots, predecessors]

theorem comma_inputs_ordered [DecidableEq First] [DecidableEq Second]
    (first : Plan First model) (second : Plan Second model)
    (orderedFirst : first.InputsOrdered) (orderedSecond : second.InputsOrdered) :
    (comma first second).InputsOrdered := by
  intro index source present
  cases index with
  | inl index =>
      cases index with
      | inl index =>
          simp only [comma, Operation.map_inputs, List.mem_map] at present
          obtain ⟨original, present, rfl⟩ := present
          exact orderedFirst index original present
      | inr index =>
          simp only [comma, Operation.map_inputs, List.mem_map] at present
          obtain ⟨original, present, rfl⟩ := present
          exact orderedSecond index original present
  | inr index =>
      simp only [comma, Operation.inputs, List.mem_singleton] at present
      subst source
      simp [comma, sequencePoint, Order.Precedes, afterRoots, predecessors]

theorem store_result_unsequenced [DecidableEq First] (operand : Plan First model) (location : Lvalue) :
    (storeResult operand location).component.evaluation.Unsequenced (.inr 0) (.inr 1) := by
  simp [Evaluation.Unsequenced, storeResult, Order.Precedes, afterRoots]

theorem arithmetic_operands_unsequenced [DecidableEq First] [DecidableEq Second]
    (first : Plan First model) (second : Plan Second model) (operator : IntegerBinaryOperator)
    (left : First) (right : Second) :
    (arithmetic first second operator).component.evaluation.Unsequenced
      (.inl (.inl left)) (.inl (.inr right)) := by
  simp [Evaluation.Unsequenced, arithmetic, binary, Order.Precedes, afterRoots, Order.parallel]

theorem comma_orders_all [DecidableEq First] [DecidableEq Second]
    (first : Plan First model) (second : Plan Second model) (left : First) (right : Second) :
    (comma first second).component.evaluation.order.Precedes (.inl (.inl left)) (.inl (.inr right)) := rfl

end Mettapedia.Languages.C11.ExpressionPlanConstruction
