import Mettapedia.Machines.AnswerCardinality

/-!
# Checked answer bounds for a finite relational control language

The semantics counts answer occurrences, including equal values. Analysis
reconstructs bounds from syntax; foreign operations have no inferred bound.
Explicit commitment is a constructor. Determinism metadata does not insert it.
The theorem concerns completed finite executions, not termination or effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CheckedCardinality

open Mettapedia.Machines.AnswerCardinality

inductive Expr (A F : Type*) where
  | ret (value : A)
  | failure
  | alternatives (left right : Expr A F)
  | sequence (first : Expr A F) (rest : A → Expr A F)
  | constrain (body : Expr A F) (accept : A → Bool)
  | commit (body : Expr A F)
  | foreign (operation : F)

def evaluate {A F : Type*} (world : F → List A) : Expr A F → List A
  | .ret value => [value]
  | .failure => []
  | .alternatives left right => evaluate world left ++ evaluate world right
  | .sequence first rest => (evaluate world first).flatMap fun value => evaluate world (rest value)
  | .constrain body accept => (evaluate world body).filter accept
  | .commit body => (evaluate world body).take 1
  | .foreign operation => world operation

/-- A finite analysis certificate chooses one common bound for the reachable
continuations. Its witnesses are recursive syntax judgments, not declarations. -/
inductive Inferred {A F : Type*} : Expr A F → Grade → Prop where
  | ret (value : A) : Inferred (.ret value) .one
  | failure : Inferred .failure .zero
  | alternatives {left right : Expr A F} {a b : Grade} :
      Inferred left a → Inferred right b → Inferred (.alternatives left right) (choice a b)
  | sequence {first : Expr A F} {rest : A → Expr A F} {a b : Grade} :
      Inferred first a → (∀ value, Inferred (rest value) b) →
      Inferred (.sequence first rest) (seq a b)
  | constrain {body : Expr A F} {a : Grade} (accept : A → Bool) :
      Inferred body a → Inferred (.constrain body accept) (constrained a)
  | commit {body : Expr A F} {a : Grade} :
      Inferred body a → Inferred (.commit body) (once a)
  | weaken {body : Expr A F} {a b : Grade} :
      Inferred body a → Refines a b → Inferred body b

theorem inferred_sound {A F : Type*} {body : Expr A F} {grade : Grade}
    (inferred : Inferred body grade) (world : F → List A) :
    Allows grade (evaluate world body).length := by
  induction inferred with
  | ret value => rfl
  | failure => rfl
  | alternatives left right ihLeft ihRight =>
      exact append_sound _ _ _ _ ihLeft ihRight
  | sequence first rest ihFirst ihRest =>
      exact bind_sound _ _ _ _ ihFirst (fun value _ => ihRest value)
  | constrain accept body ih => exact filter_sound _ _ accept ih
  | commit body ih => exact take_one_sound _ _ ih
  | weaken body refinement ih => exact refinement _ ih

inductive Declaration where
  | det | semidet | multi | nondet | failure
  deriving DecidableEq, Repr

def Declaration.grade : Declaration → Grade
  | .det => .one
  | .semidet => .optional
  | .multi => .nonempty
  | .nondet => .any
  | .failure => .zero

/-- Validation tests interval inclusion on its three complete probes. -/
def validates (inferred : Grade) (declared : Declaration) : Bool :=
  [0,1,2].all fun count => !(decide (Allows inferred count)) || decide (Allows declared.grade count)

theorem validates_iff (grade : Grade) (declared : Declaration) :
    validates grade declared = true ↔ Refines grade declared.grade := by
  rw [validates, List.all_eq_true, refines_iff_probes]
  apply forall_congr'
  intro count
  apply forall_congr'
  intro _
  simp [Bool.or_eq_true, imp_iff_not_or]

theorem checked_declaration_sound {A F : Type*} {body : Expr A F} {grade : Grade}
    (inferred : Inferred body grade) (declared : Declaration)
    (validated : validates grade declared = true) (world : F → List A) :
    Allows declared.grade (evaluate world body).length :=
  (validates_iff grade declared).mp validated _ (inferred_sound inferred world)

/-- Even an available declaration cannot create a derivation for a foreign
operation. The analyzer must leave that boundary unproved. -/
theorem foreign_unproved {A F : Type*} (operation : F) (grade : Grade) :
    ¬ Inferred (Expr.foreign (A := A) operation) grade := by
  intro inferred
  have excludes {body : Expr A F} {bound : Grade} (proof : Inferred body bound) :
      ∀ foreignOperation, body ≠ Expr.foreign foreignOperation := by
    induction proof with
    | ret _ => intro _ impossible; cases impossible
    | failure => intro _ impossible; cases impossible
    | alternatives _ _ _ _ => intro _ impossible; cases impossible
    | sequence _ _ _ _ => intro _ impossible; cases impossible
    | constrain _ _ _ => intro _ impossible; cases impossible
    | commit _ _ => intro _ impossible; cases impossible
    | weaken _ _ ih => exact ih
  exact excludes inferred operation rfl

namespace Controls

def twoOccurrences : Expr Nat Unit := .alternatives (.ret 7) (.ret 7)

theorem duplicate_values_are_multi : Inferred twoOccurrences .nonempty :=
  .alternatives (.ret 7) (.ret 7)

theorem duplicate_values_are_not_det : validates .nonempty .det = false := by decide

theorem declaration_does_not_commit :
    evaluate (fun (_ : Unit) => []) twoOccurrences = [7,7] ∧
      evaluate (fun (_ : Unit) => []) (.commit twoOccurrences) = [7] := by decide

theorem false_filter_can_remove_every_answer :
    evaluate (fun (_ : Unit) => []) (.constrain twoOccurrences (fun _ => false)) = [] := by decide

end Controls

#print axioms inferred_sound
#print axioms checked_declaration_sound
#print axioms foreign_unproved

end Mettapedia.Languages.MeTTa.PeTTa.CheckedCardinality
