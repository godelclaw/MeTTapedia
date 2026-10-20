import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion

/-!
# Reconstructing a term before a specified scoped substitution

The producer replaces exact images by their original variables and otherwise
traverses the shared term grammar, lifting the substitution beneath binders.
A forbidden constant can occur only inside an image replaced as a whole.
Publication checks the actual substitution equation and absence of that
constant. This is a partial inverse on submitted syntax, not higher-order
unification or reflection of typing through an arbitrary substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedSubstitutionInversion

variable {Head : Type} [DecidableEq Head]

def lookup {n m : Nat} (substitution : Sub Head n m) (term : Tm Head m) : Option (Fin n) :=
  (List.finRange n).find? fun index => substitution index == term

def produce (forbidden : DeclName) : {n m : Nat} → Sub Head n m → Tm Head m → Option (Tm Head n)
  | _, _, substitution, term =>
      match lookup substitution term with
      | some index => some (.var index)
      | none => match term with
        | .var _ => none
        | .head head => some (.head head)
        | .const name => if name = forbidden then none else some (.const name)
        | .pi domain body => do
            return .pi (← produce forbidden substitution domain)
              (← produce forbidden (liftSub substitution) body)
        | .sigma domain body => do
            return .sigma (← produce forbidden substitution domain)
              (← produce forbidden (liftSub substitution) body)
        | .id type left right => do
            return .id (← produce forbidden substitution type)
              (← produce forbidden substitution left) (← produce forbidden substitution right)
        | .lam body => return .lam (← produce forbidden (liftSub substitution) body)
        | .app function argument => do
            return .app (← produce forbidden substitution function)
              (← produce forbidden substitution argument)
        | .pair first second => do
            return .pair (← produce forbidden substitution first)
              (← produce forbidden substitution second)
        | .fst pair => return .fst (← produce forbidden substitution pair)
        | .snd pair => return .snd (← produce forbidden substitution pair)
        | .refl value => return .refl (← produce forbidden substitution value)
termination_by _ _ _ term => sizeOf term

/-- Replay, rather than the producer's internal choices, establishes the
substitution equation. Multiple equal images need not have a unique inverse. -/
def invert (forbidden : DeclName) {n m : Nat} (substitution : Sub Head n m)
    (term : Tm Head m) : Option (Tm Head n) := do
  let candidate ← produce forbidden substitution term
  if subst substitution candidate = term ∧
      forbidden ∉ ConstantExpansion.constantNames candidate then some candidate else none

theorem invert_sound (forbidden : DeclName) {n m : Nat} (substitution : Sub Head n m)
    (term : Tm Head m) (candidate : Tm Head n)
    (accepted : invert forbidden substitution term = some candidate) :
    subst substitution candidate = term ∧
      forbidden ∉ ConstantExpansion.constantNames candidate := by
  cases produced : produce forbidden substitution term with
  | none => simp [invert, produced] at accepted
  | some output =>
      simp only [invert, produced, Option.bind_eq_bind, Option.bind_some] at accepted
      split at accepted
      · rename_i checked
        cases Option.some.inj accepted
        exact checked
      · cases accepted

namespace Controls

def assignment : Sub Unit 2 1 := fun index =>
  if index.val = 0 then .app (.const `f) (.var 0) else .var 0

def direct : Tm Unit 1 := .app (.const `f) (.var 0)
def beneathBinder : Tm Unit 1 := .lam (.app (.const `f) (.var 1))
def capturedCall : Tm Unit 1 := .lam (.app (.const `f) (.var 0))

def verdicts : List (String × Bool) := [
  ("inverse replaces the admitted recursive call", invert `f assignment direct == some (.var 0)),
  ("inverse lifts the recursive call under a binder",
    invert `f assignment beneathBinder == some (.lam (.var 1))),
  ("inverse keeps an ordinary argument", invert `f assignment (.var 0) == some (.var 1)),
  ("inverse refuses a call on a newly bound variable", (invert `f assignment capturedCall).isNone),
  ("inverse refuses the unabstracted recursive constant", (invert `f assignment (.const `f)).isNone)]

theorem all_verdicts : verdicts.all (·.2) = true := by decide +kernel

end Controls
end ScopedSubstitutionInversion
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
