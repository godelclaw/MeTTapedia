import Mettapedia.Languages.C11.Sequencing

/-!
# Constructed sequencing around C operand value computations

Completing an operand's value computation does not order every side effect
of that operand before its parent's result. This construction adds fresh
occurrences after the selected operand-value occurrences and their existing
predecessors, leaving unrelated side effects unordered. All constructed
tables are proved strict and transitive.

The components implement the sequencing clauses for ordinary unary/binary
results, lvalue reads, postfix/prefix updates, assignment and a sequence
point followed by a selected continuation. Assignment's value result and
modification are separate occurrences with the same operand-value
predecessors. Postfix modification follows its returned old-value read.
Scalar object identity must come from the source object/lvalue adapter.

These are event-order components, not a whole expression evaluator. A
source execution must still construct its object identities, computed
values, evaluated branches and primitive memory transitions. The completed
source/Cesta representation connection is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ValueSequencing

open Sequencing

universe u v w x

def predecessors {Index : Type v} [DecidableEq Index] (order : Order Index)
    (roots : List Index) (index : Index) : Bool :=
  roots.any (fun root => decide (index = root) || order.before index root)

theorem predecessors_iff {Index : Type v} [DecidableEq Index] (order : Order Index)
    (roots : List Index) (index : Index) :
    predecessors order roots index = true ↔
      ∃ root ∈ roots, index = root ∨ order.Precedes index root := by
  simp only [predecessors, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq, Order.Precedes]

theorem predecessors_closed {Index : Type v} [DecidableEq Index] (order : Order Index)
    (valid : order.Valid) (roots : List Index) (first second : Index)
    (before : order.Precedes first second) (selected : predecessors order roots second = true) :
    predecessors order roots first = true := by
  obtain ⟨root, present, same | following⟩ := (predecessors_iff order roots second).mp selected
  · subst root
    exact (predecessors_iff order roots first).mpr ⟨second, present, Or.inr before⟩
  · exact (predecessors_iff order roots first).mpr
      ⟨root, present, Or.inr (valid.2 first second root before following)⟩

def afterRoots {Index : Type v} [DecidableEq Index] (New : Type w)
    (order : Order Index) (roots : List Index) : Order (Index ⊕ New) where
  before
    | .inl first, .inl second => order.before first second
    | .inl first, .inr _ => predecessors order roots first
    | .inr _, _ => false

theorem afterRoots_valid {Index : Type v} [DecidableEq Index] (New : Type w)
    (order : Order Index) (roots : List Index) (valid : order.Valid) :
    (afterRoots New order roots).Valid := by
  constructor
  · intro index
    cases index with
    | inl index => exact valid.1 index
    | inr index => simp [Order.Precedes, afterRoots]
  · intro first second third beforeFirst beforeSecond
    cases first <;> cases second <;> cases third <;>
      simp [Order.Precedes, afterRoots] at beforeFirst beforeSecond ⊢
    · exact valid.2 _ _ _ beforeFirst beforeSecond
    · exact predecessors_closed order valid roots _ _ beforeFirst beforeSecond

theorem afterRoots_internal {Index : Type v} [DecidableEq Index] (New : Type w)
    (order : Order Index) (roots : List Index) (first second : Index) :
    (afterRoots New order roots).Precedes (.inl first) (.inl second) ↔ order.Precedes first second := Iff.rfl

theorem afterRoots_follows {Index : Type v} [DecidableEq Index] (New : Type w)
    (order : Order Index) (roots : List Index) (first : Index) (second : New) :
    (afterRoots New order roots).Precedes (.inl first) (.inr second) ↔
      ∃ root ∈ roots, first = root ∨ order.Precedes first root := predecessors_iff order roots first

theorem afterRoots_new_unordered {Index : Type v} [DecidableEq Index] (New : Type w)
    (order : Order Index) (roots : List Index) (first second : New) :
    ¬ (afterRoots New order roots).Precedes (.inr first) (.inr second) := by
  simp [Order.Precedes, afterRoots]

structure Component (Index : Type v) (Object : Type u) where
  indexEq : DecidableEq Index
  enumeration : Enumeration Index
  evaluation : Evaluation Index Object
  valid : evaluation.order.Valid
  result : Index

def leaf {Object : Type u} (access : Access Object) : Component (Fin 1) Object where
  indexEq := inferInstance
  enumeration := .fin 1
  evaluation := ⟨⟨fun _ _ => false⟩, fun _ => access⟩
  valid := by constructor <;> simp [Order.Precedes]
  result := 0

/-- A new read or pure value computation follows its operand value. -/
def unary {Index : Type v} {Object : Type u} [DecidableEq Index]
    (operand : Component Index Object) (access : Access Object) : Component (Index ⊕ Fin 1) Object where
  indexEq := inferInstance
  enumeration := operand.enumeration.sum (.fin 1)
  evaluation := ⟨afterRoots (Fin 1) operand.evaluation.order [operand.result],
    Sum.elim operand.evaluation.access (fun _ => access)⟩
  valid := afterRoots_valid _ _ _ operand.valid
  result := .inr 0

def binary {First : Type v} {Second : Type w} {Object : Type u}
    [DecidableEq First] [DecidableEq Second]
    (first : Component First Object) (second : Component Second Object) :
    Component ((First ⊕ Second) ⊕ Fin 1) Object where
  indexEq := inferInstance
  enumeration := (first.enumeration.sum second.enumeration).sum (.fin 1)
  evaluation := ⟨afterRoots (Fin 1) (first.evaluation.order.parallel second.evaluation.order)
    [.inl first.result, .inr second.result],
    Sum.elim (Sum.elim first.evaluation.access second.evaluation.access) (fun _ => .other)⟩
  valid := afterRoots_valid _ _ _ (Order.parallel_valid _ _ first.valid second.valid)
  result := .inr 0

/-- The assignment store and its computed result share value predecessors.
Neither acquires an edge from unrelated operand modifications. -/
def assignment {First : Type v} {Second : Type w} {Object : Type u}
    [DecidableEq First] [DecidableEq Second]
    (place : Component First Object) (operand : Component Second Object) (object : Object) :
    Component ((First ⊕ Second) ⊕ Fin 2) Object where
  indexEq := inferInstance
  enumeration := (place.enumeration.sum operand.enumeration).sum (.fin 2)
  evaluation := ⟨afterRoots (Fin 2) (place.evaluation.order.parallel operand.evaluation.order)
    [.inl place.result, .inr operand.result],
    Sum.elim (Sum.elim place.evaluation.access operand.evaluation.access)
      (fun index => if index.val = 0 then .modify object else .other)⟩
  valid := afterRoots_valid _ _ _ (Order.parallel_valid _ _ place.valid operand.valid)
  result := .inr 1

def postUpdate {Index : Type v} {Object : Type u} [DecidableEq Index]
    (place : Component Index Object) (object : Object) : Component ((Index ⊕ Fin 1) ⊕ Fin 1) Object :=
  let read := unary place (.readValue object)
  let updated := unary read (.modify object)
  { updated with result := .inl read.result }

def preUpdate {Index : Type v} {Object : Type u} [DecidableEq Index]
    (place : Component Index Object) (object : Object) : Component ((Index ⊕ Fin 1) ⊕ Fin 2) Object :=
  let read := unary place (.readValue object)
  {
    indexEq := inferInstance
    enumeration := read.enumeration.sum (.fin 2)
    evaluation := ⟨afterRoots (Fin 2) read.evaluation.order [read.result],
      Sum.elim read.evaluation.access (fun index => if index.val = 0 then .modify object else .other)⟩
    valid := afterRoots_valid _ _ _ read.valid
    result := .inr 1
  }

/-- A sequence point orders all earlier effects before the selected child.
Only the actual evaluated child belongs in this component. -/
def sequencePoint {First : Type v} {Second : Type w} {Object : Type u}
    [DecidableEq First] [DecidableEq Second]
    (first : Component First Object) (selected : Component Second Object) :
    Component ((First ⊕ Second) ⊕ Fin 1) Object where
  indexEq := inferInstance
  enumeration := (first.enumeration.sum selected.enumeration).sum (.fin 1)
  evaluation := ⟨afterRoots (Fin 1) (first.evaluation.order.sequence selected.evaluation.order)
    [.inr selected.result],
    Sum.elim (Sum.elim first.evaluation.access selected.evaluation.access) (fun _ => .other)⟩
  valid := afterRoots_valid _ _ _ (Order.sequence_valid _ _ first.valid selected.valid)
  result := .inr 0

theorem binary_operand_values_before_result {First : Type v} {Second : Type w} {Object : Type u}
    [DecidableEq First] [DecidableEq Second]
    (first : Component First Object) (second : Component Second Object) :
    (binary first second).evaluation.order.Precedes (.inl (.inl first.result)) (.inr 0) ∧
      (binary first second).evaluation.order.Precedes (.inl (.inr second.result)) (.inr 0) := by
  simp [binary, Order.Precedes, afterRoots, predecessors]

theorem postfix_read_before_update {Index : Type v} {Object : Type u} [DecidableEq Index]
    (place : Component Index Object) (object : Object) :
    (postUpdate place object).evaluation.order.Precedes (.inl (.inr 0)) (.inr 0) := by
  simp [postUpdate, unary, Order.Precedes, afterRoots, predecessors]

theorem assignment_operand_values_before_store {First : Type v} {Second : Type w} {Object : Type u}
    [DecidableEq First] [DecidableEq Second]
    (place : Component First Object) (operand : Component Second Object) (object : Object) :
    (assignment place operand object).evaluation.order.Precedes (.inl (.inl place.result)) (.inr 0) ∧
      (assignment place operand object).evaluation.order.Precedes (.inl (.inr operand.result)) (.inr 0) := by
  simp [assignment, Order.Precedes, afterRoots, predecessors]

theorem assignment_preserves_operand_conflict {First : Type v} {Second : Type w} {Object : Type u}
    [DecidableEq First] [DecidableEq Second]
    (place : Component First Object) (operand : Component Second Object) (object : Object)
    (first second : Second) (bad : operand.evaluation.BadPair first second) :
    (assignment place operand object).evaluation.BadPair (.inl (.inr first)) (.inl (.inr second)) := by
  simpa [Evaluation.BadPair, Evaluation.Unsequenced, assignment, Order.Precedes, afterRoots, Order.parallel] using bad

theorem binary_preserves_cross_conflict {First : Type v} {Second : Type w} {Object : Type u}
    [DecidableEq First] [DecidableEq Second]
    (first : Component First Object) (second : Component Second Object) (left : First) (right : Second)
    (conflict : Conflict (first.evaluation.access left) (second.evaluation.access right)) :
    (binary first second).evaluation.BadPair (.inl (.inl left)) (.inl (.inr right)) := by
  simpa [Evaluation.BadPair, Evaluation.Unsequenced, binary, Order.Precedes, afterRoots, Order.parallel] using conflict

end Mettapedia.Languages.C11.ValueSequencing
