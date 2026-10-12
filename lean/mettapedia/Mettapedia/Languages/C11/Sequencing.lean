import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Lean.Elab.Tactic.Omega

/-!
# Finite C evaluation occurrences and sequencing conflicts

Occurrences retain object-value reads, modifications and designation-only
computations separately. The independently stated conflict judgment is the
ordinary scalar read/modification part of C11 6.5 paragraph 2. Object identity
is supplied by the source object layer: two aliases must identify the same
scalar object. This module does not infer identity from variable spelling or
from array-view identifiers.

A sequencing table contains the complete strict relation, not merely the
edges of a graph and not the chronological order selected by an executor.
Its executable validator checks irreflexivity and transitivity. Constructed
parallel and sequential combinations preserve these laws. Indeterminate
sequencing is represented by alternative sequential combinations, rather
than by an unsequenced combination with a convenient chosen schedule.

The executable conflict finder returns the actual two occurrence identities.
It is proved sound and complete for the independent conflict judgment.
Checking a family of permitted evaluation orders rejects a conflict in any
member of the family, even if another member is conflict-free. Empty order
families and invalid tables are model refusals, not classifications of C
undefined behavior. Atomic, volatile, signal and cross-thread accesses need
their additional source and interaction rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.Sequencing

universe u v w

inductive Access (Object : Type u) where
  | designate (object : Object)
  | readValue (object : Object)
  | modify (object : Object)
  | other
  deriving DecidableEq, Repr

/-- Designating an object does not by itself use its stored value. -/
inductive Conflict {Object : Type u} : Access Object → Access Object → Prop where
  | modifyModify (object : Object) : Conflict (.modify object) (.modify object)
  | modifyRead (object : Object) : Conflict (.modify object) (.readValue object)
  | readModify (object : Object) : Conflict (.readValue object) (.modify object)

def conflicts {Object : Type u} [DecidableEq Object] : Access Object → Access Object → Bool
  | .modify first, .modify second => first == second
  | .modify first, .readValue second => first == second
  | .readValue first, .modify second => first == second
  | _, _ => false

theorem conflicts_iff {Object : Type u} [DecidableEq Object] (first second : Access Object) :
    conflicts first second = true ↔ Conflict first second := by
  cases first <;> cases second <;> simp only [conflicts, beq_iff_eq]
  all_goals constructor
  all_goals first | (intro equal; subst equal; constructor) | (intro impossible; cases impossible)
  all_goals rfl

theorem Conflict.symm {Object : Type u} {first second : Access Object}
    (conflict : Conflict first second) : Conflict second first := by
  cases conflict <;> constructor

structure Order (Index : Type v) where
  before : Index → Index → Bool

/-- Finite occurrence enumeration is supplied as executable data. -/
structure Enumeration (Index : Type v) where
  items : List Index
  complete : ∀ index, index ∈ items

def Enumeration.fin (count : Nat) : Enumeration (Fin count) :=
  ⟨List.finRange count, by intro index; simp⟩

def Enumeration.sum {First : Type v} {Second : Type w}
    (first : Enumeration First) (second : Enumeration Second) : Enumeration (First ⊕ Second) :=
  ⟨first.items.map Sum.inl ++ second.items.map Sum.inr, by
    intro index
    cases index with
    | inl index => simp [first.complete index]
    | inr index => simp [second.complete index]⟩

def Enumeration.product {First : Type v} {Second : Type w}
    (first : Enumeration First) (second : Enumeration Second) : Enumeration (First × Second) :=
  ⟨first.items.flatMap (fun left => second.items.map (fun right => (left, right))), by
    rintro ⟨left, right⟩
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨left, first.complete left, right, second.complete right, rfl⟩⟩

def Order.Precedes {Index : Type v} (order : Order Index) (first second : Index) : Prop :=
  order.before first second = true

def Order.Valid {Index : Type v} (order : Order Index) : Prop :=
  (∀ index, ¬ order.Precedes index index) ∧
    (∀ first middle last, order.Precedes first middle → order.Precedes middle last →
      order.Precedes first last)

def Order.check {Index : Type v} (enumeration : Enumeration Index) (order : Order Index) : Bool :=
  (enumeration.items.all fun index => decide (order.before index index ≠ true)) &&
    (enumeration.items.all fun first => enumeration.items.all fun middle =>
      enumeration.items.all fun last =>
        decide (order.before first middle = true → order.before middle last = true →
          order.before first last = true))

theorem Order.check_iff {Index : Type v} (enumeration : Enumeration Index) (order : Order Index) :
    order.check enumeration = true ↔ order.Valid := by
  simp only [Order.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨irrefl, trans⟩
    exact ⟨fun index => irrefl index (enumeration.complete index),
      fun first middle last => trans first (enumeration.complete first)
        middle (enumeration.complete middle) last (enumeration.complete last)⟩
  · rintro ⟨irrefl, trans⟩
    exact ⟨fun index _ => irrefl index, fun first _ middle _ last _ => trans first middle last⟩

theorem Order.Valid.asymmetric {Index : Type v} {order : Order Index}
    (valid : order.Valid) (first second : Index) (forward : order.Precedes first second) :
    ¬ order.Precedes second first := by
  intro backward
  exact valid.1 first (valid.2 first second first forward backward)

def Order.parallel {First : Type v} {Second : Type w}
    (first : Order First) (second : Order Second) : Order (First ⊕ Second) where
  before
    | .inl left, .inl right => first.before left right
    | .inr left, .inr right => second.before left right
    | _, _ => false

def Order.sequence {First : Type v} {Second : Type w}
    (first : Order First) (second : Order Second) : Order (First ⊕ Second) where
  before
    | .inl left, .inl right => first.before left right
    | .inr left, .inr right => second.before left right
    | .inl _, .inr _ => true
    | .inr _, .inl _ => false

def Order.sequenceRight {First : Type v} {Second : Type w}
    (first : Order First) (second : Order Second) : Order (First ⊕ Second) where
  before
    | .inl left, .inl right => first.before left right
    | .inr left, .inr right => second.before left right
    | .inr _, .inl _ => true
    | .inl _, .inr _ => false

theorem Order.parallel_valid {First : Type v} {Second : Type w}
    (first : Order First) (second : Order Second) (validFirst : first.Valid) (validSecond : second.Valid) :
    (first.parallel second).Valid := by
  constructor
  · intro index
    cases index with
    | inl index => exact validFirst.1 index
    | inr index => exact validSecond.1 index
  · intro left middle right beforeLeft beforeRight
    cases left <;> cases middle <;> cases right <;>
      simp [Order.Precedes, Order.parallel] at beforeLeft beforeRight ⊢
    · exact validFirst.2 _ _ _ beforeLeft beforeRight
    · exact validSecond.2 _ _ _ beforeLeft beforeRight

theorem Order.sequence_valid {First : Type v} {Second : Type w}
    (first : Order First) (second : Order Second) (validFirst : first.Valid) (validSecond : second.Valid) :
    (first.sequence second).Valid := by
  constructor
  · intro index
    cases index with
    | inl index => exact validFirst.1 index
    | inr index => exact validSecond.1 index
  · intro left middle right beforeLeft beforeRight
    cases left <;> cases middle <;> cases right <;>
      simp [Order.Precedes, Order.sequence] at beforeLeft beforeRight ⊢
    · exact validFirst.2 _ _ _ beforeLeft beforeRight
    · exact validSecond.2 _ _ _ beforeLeft beforeRight

theorem Order.sequenceRight_valid {First : Type v} {Second : Type w}
    (first : Order First) (second : Order Second) (validFirst : first.Valid) (validSecond : second.Valid) :
    (first.sequenceRight second).Valid := by
  constructor
  · intro index
    cases index with
    | inl index => exact validFirst.1 index
    | inr index => exact validSecond.1 index
  · intro left middle right beforeLeft beforeRight
    cases left <;> cases middle <;> cases right <;>
      simp [Order.Precedes, Order.sequenceRight] at beforeLeft beforeRight ⊢
    · exact validFirst.2 _ _ _ beforeLeft beforeRight
    · exact validSecond.2 _ _ _ beforeLeft beforeRight

structure Evaluation (Index : Type v) (Object : Type u) where
  order : Order Index
  access : Index → Access Object

def Evaluation.Unsequenced {Index : Type v} {Object : Type u}
    (evaluation : Evaluation Index Object) (first second : Index) : Prop :=
  first ≠ second ∧ ¬ evaluation.order.Precedes first second ∧
    ¬ evaluation.order.Precedes second first

def Evaluation.BadPair {Index : Type v} {Object : Type u}
    (evaluation : Evaluation Index Object) (first second : Index) : Prop :=
  evaluation.Unsequenced first second ∧ Conflict (evaluation.access first) (evaluation.access second)

def Evaluation.Undefined {Index : Type v} {Object : Type u}
    (evaluation : Evaluation Index Object) : Prop := ∃ first second, evaluation.BadPair first second

def Evaluation.badPair {Index : Type v} {Object : Type u}
    [DecidableEq Index] [DecidableEq Object] (evaluation : Evaluation Index Object)
    (pair : Index × Index) : Bool :=
  decide (pair.1 ≠ pair.2 ∧ evaluation.order.before pair.1 pair.2 ≠ true ∧
    evaluation.order.before pair.2 pair.1 ≠ true) && conflicts (evaluation.access pair.1) (evaluation.access pair.2)

theorem Evaluation.badPair_iff {Index : Type v} {Object : Type u}
    [DecidableEq Index] [DecidableEq Object] (evaluation : Evaluation Index Object) (pair : Index × Index) :
    evaluation.badPair pair = true ↔ evaluation.BadPair pair.1 pair.2 := by
  simp only [badPair, Bool.and_eq_true, decide_eq_true_eq,
    conflicts_iff, BadPair, Unsequenced, Order.Precedes]

def Evaluation.findConflict {Index : Type v} {Object : Type u}
    [DecidableEq Index] [DecidableEq Object] (enumeration : Enumeration Index)
    (evaluation : Evaluation Index Object) : Option (Index × Index) :=
  (enumeration.product enumeration).items.find? evaluation.badPair

theorem Evaluation.findConflict_sound {Index : Type v} {Object : Type u}
    [DecidableEq Index] [DecidableEq Object] (enumeration : Enumeration Index)
    (evaluation : Evaluation Index Object) (pair : Index × Index)
    (found : evaluation.findConflict enumeration = some pair) : evaluation.BadPair pair.1 pair.2 := by
  exact (evaluation.badPair_iff pair).mp (List.find?_some found)

theorem Evaluation.findConflict_none_iff {Index : Type v} {Object : Type u}
    [DecidableEq Index] [DecidableEq Object] (enumeration : Enumeration Index)
    (evaluation : Evaluation Index Object) : evaluation.findConflict enumeration = none ↔ ¬ evaluation.Undefined := by
  simp only [findConflict, List.find?_eq_none]
  constructor
  · intro clean ⟨first, second, conflict⟩
    have present := (evaluation.badPair_iff (first, second)).mpr conflict
    exact clean (first, second) ((enumeration.product enumeration).complete (first, second)) present
  · intro clean pair _ present
    exact clean ⟨pair.1, pair.2, (evaluation.badPair_iff pair).mp present⟩

def Evaluation.parallel {First : Type v} {Second : Type w} {Object : Type u}
    (first : Evaluation First Object) (second : Evaluation Second Object) : Evaluation (First ⊕ Second) Object :=
  ⟨first.order.parallel second.order, Sum.elim first.access second.access⟩

def Evaluation.sequence {First : Type v} {Second : Type w} {Object : Type u}
    (first : Evaluation First Object) (second : Evaluation Second Object) : Evaluation (First ⊕ Second) Object :=
  ⟨first.order.sequence second.order, Sum.elim first.access second.access⟩

theorem Evaluation.parallel_cross_iff {First : Type v} {Second : Type w} {Object : Type u}
    (first : Evaluation First Object) (second : Evaluation Second Object) (left : First) (right : Second) :
    (first.parallel second).BadPair (.inl left) (.inr right) ↔ Conflict (first.access left) (second.access right) := by
  simp [BadPair, Unsequenced, parallel, Order.parallel, Order.Precedes]

theorem Evaluation.sequence_no_cross {First : Type v} {Second : Type w} {Object : Type u}
    (first : Evaluation First Object) (second : Evaluation Second Object) (left : First) (right : Second) :
    ¬ (first.sequence second).BadPair (.inl left) (.inr right) := by
  simp [BadPair, Unsequenced, sequence, Order.sequence, Order.Precedes]

theorem Evaluation.parallel_undefined_iff {First : Type v} {Second : Type w} {Object : Type u}
    (first : Evaluation First Object) (second : Evaluation Second Object) :
    (first.parallel second).Undefined ↔ first.Undefined ∨ second.Undefined ∨
      ∃ left right, Conflict (first.access left) (second.access right) := by
  constructor
  · rintro ⟨left, right, bad⟩
    cases left with
    | inl left =>
        cases right with
        | inl right => exact Or.inl ⟨left, right, by simpa [BadPair, Unsequenced, parallel, Order.parallel, Order.Precedes] using bad⟩
        | inr right => exact Or.inr (Or.inr ⟨left, right, (parallel_cross_iff first second left right).mp bad⟩)
    | inr left =>
        cases right with
        | inl right =>
            have conflicting : Conflict (second.access left) (first.access right) := bad.2
            exact Or.inr (Or.inr ⟨right, left, conflicting.symm⟩)
        | inr right => exact Or.inr (Or.inl ⟨left, right, by simpa [BadPair, Unsequenced, parallel, Order.parallel, Order.Precedes] using bad⟩)
  · rintro (⟨left, right, bad⟩ | ⟨left, right, bad⟩ | ⟨left, right, conflict⟩)
    · exact ⟨.inl left, .inl right, by simpa [BadPair, Unsequenced, parallel, Order.parallel, Order.Precedes] using bad⟩
    · exact ⟨.inr left, .inr right, by simpa [BadPair, Unsequenced, parallel, Order.parallel, Order.Precedes] using bad⟩
    · exact ⟨.inl left, .inr right, (parallel_cross_iff first second left right).mpr conflict⟩

theorem Evaluation.sequence_undefined_iff {First : Type v} {Second : Type w} {Object : Type u}
    (first : Evaluation First Object) (second : Evaluation Second Object) :
    (first.sequence second).Undefined ↔ first.Undefined ∨ second.Undefined := by
  constructor
  · rintro ⟨left, right, bad⟩
    cases left with
    | inl left =>
        cases right with
        | inl right => exact Or.inl ⟨left, right, by simpa [BadPair, Unsequenced, sequence, Order.sequence, Order.Precedes] using bad⟩
        | inr right => exact False.elim (sequence_no_cross first second left right bad)
    | inr left =>
        cases right with
        | inl right =>
            exact False.elim (bad.1.2.2 (by rfl))
        | inr right => exact Or.inr ⟨left, right, by simpa [BadPair, Unsequenced, sequence, Order.sequence, Order.Precedes] using bad⟩
  · rintro (⟨left, right, bad⟩ | ⟨left, right, bad⟩)
    · exact ⟨.inl left, .inl right, by simpa [BadPair, Unsequenced, sequence, Order.sequence, Order.Precedes] using bad⟩
    · exact ⟨.inr left, .inr right, by simpa [BadPair, Unsequenced, sequence, Order.sequence, Order.Precedes] using bad⟩

def Evaluation.sequenceRight {First : Type v} {Second : Type w} {Object : Type u}
    (first : Evaluation First Object) (second : Evaluation Second Object) : Evaluation (First ⊕ Second) Object :=
  ⟨first.order.sequenceRight second.order, Sum.elim first.access second.access⟩

theorem Evaluation.sequenceRight_undefined_iff {First : Type v} {Second : Type w} {Object : Type u}
    (first : Evaluation First Object) (second : Evaluation Second Object) :
    (first.sequenceRight second).Undefined ↔ first.Undefined ∨ second.Undefined := by
  constructor
  · rintro ⟨left, right, bad⟩
    cases left with
    | inl left =>
        cases right with
        | inl right => exact Or.inl ⟨left, right, by simpa [BadPair, Unsequenced, sequenceRight, Order.sequenceRight, Order.Precedes] using bad⟩
        | inr right => exact False.elim (bad.1.2.2 (by rfl))
    | inr left =>
        cases right with
        | inl right => exact False.elim (bad.1.2.1 (by rfl))
        | inr right => exact Or.inr ⟨left, right, by simpa [BadPair, Unsequenced, sequenceRight, Order.sequenceRight, Order.Precedes] using bad⟩
  · rintro (⟨left, right, bad⟩ | ⟨left, right, bad⟩)
    · exact ⟨.inl left, .inl right, by simpa [BadPair, Unsequenced, sequenceRight, Order.sequenceRight, Order.Precedes] using bad⟩
    · exact ⟨.inr left, .inr right, by simpa [BadPair, Unsequenced, sequenceRight, Order.sequenceRight, Order.Precedes] using bad⟩

def Evaluation.indeterminate {First : Type v} {Second : Type w} {Object : Type u}
    (first : Evaluation First Object) (second : Evaluation Second Object) :
    List (Evaluation (First ⊕ Second) Object) := [first.sequence second, first.sequenceRight second]

theorem Evaluation.indeterminate_undefined_iff {First : Type v} {Second : Type w} {Object : Type u}
    (first : Evaluation First Object) (second : Evaluation Second Object) :
    (∃ evaluation ∈ first.indeterminate second, evaluation.Undefined) ↔ first.Undefined ∨ second.Undefined := by
  simp [indeterminate, sequence_undefined_iff, sequenceRight_undefined_iff]

inductive CheckResult (Index : Type v) where
  | emptyAlternatives
  | safe
  | invalidOrder (alternative : Nat)
  | unsequencedConflict (alternative : Nat) (first second : Index)
  deriving DecidableEq, Repr

def checkOrders {Index : Type v} {Object : Type u} [DecidableEq Index] [DecidableEq Object]
    (enumeration : Enumeration Index) (start : Nat) : List (Evaluation Index Object) → CheckResult Index
  | [] => .safe
  | evaluation :: rest =>
      if evaluation.order.check enumeration then
        match evaluation.findConflict enumeration with
        | none => checkOrders enumeration (start + 1) rest
        | some (first, second) => .unsequencedConflict start first second
      else .invalidOrder start

theorem checkOrders_safe_iff {Index : Type v} {Object : Type u} [DecidableEq Index] [DecidableEq Object]
    (enumeration : Enumeration Index) (start : Nat) (orders : List (Evaluation Index Object)) :
    checkOrders enumeration start orders = .safe ↔
      ∀ evaluation ∈ orders, evaluation.order.Valid ∧ ¬ evaluation.Undefined := by
  induction orders generalizing start with
  | nil => simp [checkOrders]
  | cons evaluation rest ih =>
      by_cases valid : evaluation.order.check enumeration = true
      · cases found : evaluation.findConflict enumeration with
        | none =>
            have clean := (evaluation.findConflict_none_iff enumeration).mp found
            have validOrder := (evaluation.order.check_iff enumeration).mp valid
            simp [checkOrders, valid, found, ih, validOrder, clean]
        | some pair =>
            have bad : evaluation.Undefined := ⟨pair.1, pair.2,
              evaluation.findConflict_sound enumeration pair found⟩
            simp [checkOrders, valid, found, bad]
      · have invalid : ¬ evaluation.order.Valid := fun proof => valid ((evaluation.order.check_iff enumeration).mpr proof)
        simp [checkOrders, valid, invalid]

theorem checkOrders_rejects_any_conflict {Index : Type v} {Object : Type u}
    [DecidableEq Index] [DecidableEq Object] (enumeration : Enumeration Index) (start : Nat)
    (orders : List (Evaluation Index Object)) (evaluation : Evaluation Index Object)
    (permitted : evaluation ∈ orders) (bad : evaluation.Undefined) :
    checkOrders enumeration start orders ≠ .safe := by
  intro accepted
  exact ((checkOrders_safe_iff enumeration start orders).mp accepted evaluation permitted).2 bad

def checkFamily {Index : Type v} {Object : Type u} [DecidableEq Index] [DecidableEq Object]
    (enumeration : Enumeration Index) (orders : List (Evaluation Index Object)) : CheckResult Index :=
  match orders with
  | [] => .emptyAlternatives
  | _ :: _ => checkOrders enumeration 0 orders

theorem checkFamily_safe_iff {Index : Type v} {Object : Type u} [DecidableEq Index] [DecidableEq Object]
    (enumeration : Enumeration Index) (orders : List (Evaluation Index Object)) :
    checkFamily enumeration orders = .safe ↔
      orders ≠ [] ∧ ∀ evaluation ∈ orders, evaluation.order.Valid ∧ ¬ evaluation.Undefined := by
  cases orders with
  | nil => simp [checkFamily]
  | cons head tail => simp [checkFamily, checkOrders_safe_iff]

end Mettapedia.Languages.C11.Sequencing
