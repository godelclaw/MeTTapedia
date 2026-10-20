import Mathlib.Data.List.Basic

/-!
# Finite open list spines

The spine of a first-order list can end in nil, an unbound variable, or an
improper terminal. Elements are opaque: discovering arity does not require
them to be ground. This is the finite spine view; heap aliases, cycles and
attributed-variable propagation are not identified with this syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.ListSpine

inductive Spine (Element Variable : Type*) where
  | nil
  | slot (name : Variable)
  | atom (value : Element)
  | cons (head : Element) (tail : Spine Element Variable)
  deriving DecidableEq

variable {Element Variable : Type*}

inductive EndsInVariable : Spine Element Variable → Variable → Prop where
  | slot (name : Variable) : EndsInVariable (.slot name) name
  | cons (head : Element) {tail : Spine Element Variable} {name : Variable}
      (rest : EndsInVariable tail name) : EndsInVariable (.cons head tail) name

inductive OpenTail : Spine Element Variable → Variable → Prop where
  | cons (head : Element) {tail : Spine Element Variable} {name : Variable}
      (rest : EndsInVariable tail name) : OpenTail (.cons head tail) name

def tailVariable : Spine Element Variable → Option Variable
  | .slot name => some name
  | .cons _ tail => tailVariable tail
  | _ => none

/-- A free input alone is not recognized as a list constructor. -/
def openTail : Spine Element Variable → Option Variable
  | .cons _ tail => tailVariable tail
  | _ => none

theorem tailVariable_exact (spine : Spine Element Variable) (name : Variable) :
    tailVariable spine = some name ↔ EndsInVariable spine name := by
  induction spine with
  | nil => constructor <;> intro impossible <;> cases impossible
  | atom value => constructor <;> intro impossible <;> cases impossible
  | slot slot =>
      constructor
      · intro equal
        have same : slot = name := Option.some.inj equal
        subst name
        exact .slot slot
      · intro endAt
        cases endAt
        rfl
  | cons head tail ih =>
      constructor
      · intro found; exact .cons head (ih.mp found)
      · intro endAt
        cases endAt with
        | cons _ rest => exact ih.mpr rest

theorem openTail_exact (spine : Spine Element Variable) (name : Variable) :
    openTail spine = some name ↔ OpenTail spine name := by
  cases spine with
  | nil => constructor <;> intro impossible <;> cases impossible
  | atom value => constructor <;> intro impossible <;> cases impossible
  | slot slot => constructor <;> intro impossible <;> cases impossible
  | cons head tail =>
      constructor
      · intro found; exact .cons head ((tailVariable_exact tail name).mp found)
      · intro endAt
        cases endAt with
        | cons _ rest => exact (tailVariable_exact tail name).mpr rest

inductive Length : Spine Element Variable → Nat → Prop where
  | nil : Length .nil 0
  | cons (head : Element) {tail : Spine Element Variable} {size : Nat}
      (rest : Length tail size) : Length (.cons head tail) (size + 1)

theorem variable_end_has_no_length {spine : Spine Element Variable} {name : Variable}
    (openEnd : EndsInVariable spine name) (size : Nat) : ¬ Length spine size := by
  induction openEnd generalizing size with
  | slot name => intro impossible; cases impossible
  | cons head rest ih =>
      intro length
      cases length with
      | cons _ remaining => exact ih _ remaining

theorem openTail_has_no_length (spine : Spine Element Variable) (name : Variable)
    (found : openTail spine = some name) (size : Nat) : ¬ Length spine size := by
  cases (openTail_exact spine name).mp found with
  | cons head rest =>
      intro length
      cases length with
      | cons _ remaining => exact variable_end_has_no_length rest _ remaining

def prepend (heads : List Element) (tail : Spine Element Variable) : Spine Element Variable :=
  heads.foldr Spine.cons tail

theorem tailVariable_prefix (heads : List Element) (tail : Spine Element Variable) :
    tailVariable (prepend heads tail) = tailVariable tail := by
  induction heads with
  | nil => rfl
  | cons head rest ih => exact ih

/-- Replacing an open tail by another segment observes the new segment's
tail. The old wake-up does not establish that the arity is now known. -/
theorem openTail_segment (head : Element) (rest : List Element)
    (segment : Spine Element Variable) :
    openTail (prepend (head :: rest) segment) = tailVariable segment :=
  tailVariable_prefix rest segment

theorem closed_prefix_length (heads : List Element) :
    Length (prepend heads (.nil : Spine Element Variable)) heads.length := by
  induction heads with
  | nil => exact .nil
  | cons head rest ih => exact .cons head ih

namespace Controls

example : openTail (.slot 0 : Spine Nat Nat) = none := rfl
example : openTail (.cons 3 (.slot 0) : Spine Nat Nat) = some 0 := rfl
example : openTail (.cons 3 (.cons 4 (.slot 1)) : Spine Nat Nat) = some 1 := rfl
example : Length (prepend [3,4] (.nil : Spine Nat Nat)) 2 := closed_prefix_length [3,4]

/-- Absence of an open tail alone does not certify a proper list. -/
theorem improper_is_not_a_closed_list :
    openTail (.cons 3 (.atom 4) : Spine Nat Nat) = none ∧
      ∀ size, ¬ Length (.cons 3 (.atom 4) : Spine Nat Nat) size := by
  refine ⟨rfl, ?_⟩
  intro size length
  cases length with
  | cons _ rest => cases rest

end Controls

#print axioms openTail_exact
#print axioms openTail_has_no_length
#print axioms openTail_segment
#print axioms closed_prefix_length

end Mettapedia.Logic.LP.ListSpine
