import Mettapedia.Languages.C11.LocatedExpressions

/-!
# Independent source sequencing for located integer expressions

The source rules below describe operand-internal sequencing, parallel
operands, sequence-point boundaries and results after operand values. They
are inductive propositions, independent of the executable Boolean tables.
Compilation is sound and complete for these rules at every expression depth.

An assignment's converted value is a shared predecessor of its modification
and returned value, without ordering those two occurrences. A postfix update
returns the original read; its modification remains an occurrence of the
same evaluation. Conflicts concern the retained source order, not the order
in which a scheduler happened to execute the nodes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ExpressionSourceOrder

open Sequencing ValueSequencing IntegerMemoryModel LocatedExpressions

inductive Parallel {First Second : Type} (first : First → First → Prop)
    (second : Second → Second → Prop) : First ⊕ Second → First ⊕ Second → Prop where
  | left (before after : First) (ordered : first before after) : Parallel first second (.inl before) (.inl after)
  | right (before after : Second) (ordered : second before after) : Parallel first second (.inr before) (.inr after)

inductive Sequence {First Second : Type} (first : First → First → Prop)
    (second : Second → Second → Prop) : First ⊕ Second → First ⊕ Second → Prop where
  | left (before after : First) (ordered : first before after) : Sequence first second (.inl before) (.inl after)
  | right (before after : Second) (ordered : second before after) : Sequence first second (.inr before) (.inr after)
  | boundary (before : First) (after : Second) : Sequence first second (.inl before) (.inr after)

inductive After {Index : Type} (before : Index → Index → Prop) (roots : List Index) (New : Type) :
    Index ⊕ New → Index ⊕ New → Prop where
  | internal (first second : Index) (ordered : before first second) : After before roots New (.inl first) (.inl second)
  | root (root : Index) (selected : root ∈ roots) (next : New) : After before roots New (.inl root) (.inr next)
  | predecessor (first root : Index) (selected : root ∈ roots) (ordered : before first root) (next : New) :
      After before roots New (.inl first) (.inr next)

theorem parallel_iff {First Second : Type} (first : Order First) (second : Order Second)
    (sourceFirst : First → First → Prop) (sourceSecond : Second → Second → Prop)
    (firstCorresponds : ∀ before after, first.Precedes before after ↔ sourceFirst before after)
    (secondCorresponds : ∀ before after, second.Precedes before after ↔ sourceSecond before after)
    (before after : First ⊕ Second) :
    (first.parallel second).Precedes before after ↔ Parallel sourceFirst sourceSecond before after := by
  cases before with
  | inl before =>
      cases after with
      | inl after =>
          constructor
          · exact fun ordered => .left _ _ ((firstCorresponds _ _).mp ordered)
          · intro ordered; cases ordered with
            | left _ _ relation => exact (firstCorresponds _ _).mpr relation
      | inr after =>
          constructor
          · intro impossible; cases impossible
          · intro impossible; cases impossible
  | inr before =>
      cases after with
      | inl after =>
          constructor
          · intro impossible; cases impossible
          · intro impossible; cases impossible
      | inr after =>
          constructor
          · exact fun ordered => .right _ _ ((secondCorresponds _ _).mp ordered)
          · intro ordered; cases ordered with
            | right _ _ relation => exact (secondCorresponds _ _).mpr relation

theorem sequence_iff {First Second : Type} (first : Order First) (second : Order Second)
    (sourceFirst : First → First → Prop) (sourceSecond : Second → Second → Prop)
    (firstCorresponds : ∀ before after, first.Precedes before after ↔ sourceFirst before after)
    (secondCorresponds : ∀ before after, second.Precedes before after ↔ sourceSecond before after)
    (before after : First ⊕ Second) :
    (first.sequence second).Precedes before after ↔ Sequence sourceFirst sourceSecond before after := by
  cases before with
  | inl before =>
      cases after with
      | inl after =>
          constructor
          · exact fun ordered => .left _ _ ((firstCorresponds _ _).mp ordered)
          · intro ordered; cases ordered with
            | left _ _ relation => exact (firstCorresponds _ _).mpr relation
      | inr after => exact ⟨fun _ => .boundary before after, fun _ => rfl⟩
  | inr before =>
      cases after with
      | inl after =>
          constructor
          · intro impossible; cases impossible
          · intro impossible; cases impossible
      | inr after =>
          constructor
          · exact fun ordered => .right _ _ ((secondCorresponds _ _).mp ordered)
          · intro ordered; cases ordered with
            | right _ _ relation => exact (secondCorresponds _ _).mpr relation

theorem after_iff {Index : Type} [DecidableEq Index] (order : Order Index)
    (source : Index → Index → Prop) (corresponds : ∀ before after, order.Precedes before after ↔ source before after)
    (roots : List Index) (New : Type) (before after : Index ⊕ New) :
    (afterRoots New order roots).Precedes before after ↔ After source roots New before after := by
  cases before with
  | inl before =>
      cases after with
      | inl after =>
          constructor
          · exact fun ordered => .internal _ _ ((corresponds _ _).mp ordered)
          · intro ordered; cases ordered with
            | internal _ _ relation => exact (corresponds _ _).mpr relation
      | inr after =>
          constructor
          · intro ordered
            obtain ⟨root, selected, same | predecessor⟩ := (predecessors_iff order roots before).mp ordered
            · subst root; exact .root before selected after
            · exact .predecessor before root selected ((corresponds _ _).mp predecessor) after
          · intro ordered
            cases ordered with
            | root => exact (predecessors_iff order roots _).mpr ⟨_, by assumption, Or.inl rfl⟩
            | predecessor =>
                exact (predecessors_iff order roots _).mpr
                  ⟨_, by assumption, Or.inr ((corresponds _ _).mpr (by assumption))⟩
  | inr before =>
      cases after <;> constructor
      all_goals intro impossible; cases impossible

def updateOrder : UpdateIndex → UpdateIndex → Prop :=
  After (After (After (Parallel (fun (_ _ : Fin 1) => False) (fun (_ _ : Fin 1) => False))
    [.inl 0, .inr 0] (Fin 1)) [.inr 0] (Fin 1)) [.inr 0] (Fin 2)

def Before {model : Model} : (expression : Expression model) → Index expression → Index expression → Prop
  | .value _, _, _ | .load _, _, _ => False
  | .arithmetic _ first second, before, after =>
      After (Parallel (Before first) (Before second)) [.inl (result first), .inr (result second)] (Fin 1) before after
  | .cast _ operand, before, after => After (Before operand) [result operand] (Fin 1) before after
  | .assignment _ operand, before, after =>
      After (After (Before operand) [result operand] (Fin 1)) [.inr 0] (Fin 2) before after
  | .update _ _ _, before, after => updateOrder before after
  | .comma first second, before, after =>
      After (Sequence (Before first) (Before second)) [.inr (result second)] (Fin 1) before after

private theorem leaf_corresponds (access : Access ObjectAccessMemory.Identity) (first second : Fin 1) :
    (leaf access).evaluation.order.Precedes first second ↔ False := by
  simp [leaf, Order.Precedes]

private theorem update_corresponds (model : Model) (location : Destination) (increment isPrefix : Bool)
    (before after : UpdateIndex) :
    (updatePlan model location increment isPrefix).component.evaluation.order.Precedes before after ↔ updateOrder before after := by
  unfold updatePlan ExpressionPlanConstruction.storeResult ExpressionPlanConstruction.cast
    ExpressionPlanConstruction.arithmetic unary binary updateOrder
  apply after_iff
  intro first second
  apply after_iff
  intro first second
  apply after_iff
  intro first second
  apply parallel_iff
  · exact leaf_corresponds _
  · exact leaf_corresponds _

theorem compiled_order_iff {model : Model} (expression : Expression model) (before after : Index expression) :
    (compile expression).component.evaluation.order.Precedes before after ↔ Before expression before after := by
  induction expression with
  | value scalar => exact leaf_corresponds _ _ _
  | load location => exact leaf_corresponds _ _ _
  | arithmetic operator first second firstIH secondIH =>
      change (afterRoots (Fin 1) ((compile first).component.evaluation.order.parallel
        (compile second).component.evaluation.order)
        [.inl (compile first).component.result, .inr (compile second).component.result]).Precedes before after ↔ _
      simp only [compiled_result]
      apply after_iff
      exact parallel_iff _ _ _ _ firstIH secondIH
  | cast type operand ih =>
      change (afterRoots (Fin 1) (compile operand).component.evaluation.order [(compile operand).component.result]).Precedes before after ↔ _
      simp only [compiled_result]
      exact after_iff _ _ ih _ _ before after
  | assignment location operand ih =>
      change (afterRoots (Fin 2) (afterRoots (Fin 1) (compile operand).component.evaluation.order
        [(compile operand).component.result]) [.inr 0]).Precedes before after ↔ _
      simp only [compiled_result]
      apply after_iff
      exact after_iff _ _ ih _ _
  | update location increment isPrefix => exact update_corresponds _ _ _ _ before after
  | comma first second firstIH secondIH =>
      change (afterRoots (Fin 1) ((compile first).component.evaluation.order.sequence
        (compile second).component.evaluation.order) [.inr (compile second).component.result]).Precedes before after ↔ _
      simp only [compiled_result]
      apply after_iff
      exact sequence_iff _ _ _ _ firstIH secondIH

theorem source_irreflexive {model : Model} (expression : Expression model) (index : Index expression) :
    ¬ Before expression index index := by
  intro ordered
  exact (compile expression).component.valid.1 index ((compiled_order_iff _ _ _).mpr ordered)

theorem source_transitive {model : Model} (expression : Expression model)
    (first second third : Index expression) (earlier : Before expression first second) (later : Before expression second third) :
    Before expression first third :=
  (compiled_order_iff _ _ _).mp ((compile expression).component.valid.2 _ _ _
    ((compiled_order_iff _ _ _).mpr earlier) ((compiled_order_iff _ _ _).mpr later))

end Mettapedia.Languages.C11.ExpressionSourceOrder
