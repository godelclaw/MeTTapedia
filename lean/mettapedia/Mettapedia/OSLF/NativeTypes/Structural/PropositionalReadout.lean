import Mettapedia.OSLF.NativeTypes.Structural.FrontierReadout

open Mettapedia.OSLF.Framework

/-!
# Propositional checking through actual equation-frontier readouts

Top, bottom and structural roots are checked directly. Propositional
operations combine the certified answers without a new predicate oracle.
Modal atoms and decompositions requiring further searches remain unknown
here; the generated modal checker can join their retained answers separately.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

def readBinary (operation : Bool → Bool → Bool) (first second : Option Bool) : Option Bool :=
  match first, second with
  | some left, some right => some (operation left right)
  | _, _ => none

def readNegation (answer : Option Bool) : Option Bool := answer.map Bool.not

/-- Every delivered Boolean has its independent propositional meaning. -/
def ReadoutCorrect (answer : Option Bool) (meaning : Prop) : Prop :=
  ∀ value, answer = some value → (value = true ↔ meaning)

theorem readBinary_conjunction_sound {first second : Option Bool} {p q : Prop}
    (firstSound : ReadoutCorrect first p) (secondSound : ReadoutCorrect second q) :
    ReadoutCorrect (readBinary Bool.and first second) (p ∧ q) := by
  cases first <;> cases second <;>
    simp_all [ReadoutCorrect, readBinary, Bool.and_eq_true]

theorem readBinary_disjunction_sound {first second : Option Bool} {p q : Prop}
    (firstSound : ReadoutCorrect first p) (secondSound : ReadoutCorrect second q) :
    ReadoutCorrect (readBinary Bool.or first second) (p ∨ q) := by
  cases first <;> cases second <;>
    simp_all [ReadoutCorrect, readBinary, Bool.or_eq_true]

theorem readBinary_implication_sound {first second : Option Bool} {p q : Prop}
    (firstSound : ReadoutCorrect first p) (secondSound : ReadoutCorrect second q) :
    ReadoutCorrect (readBinary (fun first second => !first || second) first second) (p → q) := by
  cases first with
  | none => simp [ReadoutCorrect, readBinary]
  | some first =>
      cases second with
      | none => simp [ReadoutCorrect, readBinary]
      | some second =>
          cases first <;> cases second <;> simp_all [ReadoutCorrect, readBinary]

theorem readNegation_sound {answer : Option Bool} {p : Prop}
    (sound : ReadoutCorrect answer p) : ReadoutCorrect (readNegation answer) (¬ p) := by
  cases answer with
  | none => simp [ReadoutCorrect, readNegation]
  | some value => cases value <;> simp_all [ReadoutCorrect, readNegation]

/-- Recursive executable checking of the propositional closure of actual
structural-root answers. Unsupported semantic searches stay unresolved. -/
def readFrontierFormula (request : Request) (state : State request) : Formula → Option Bool
  | .top => some true
  | .bottom => some false
  | .atom _ => none
  | .conj left right => readBinary Bool.and
      (readFrontierFormula request state left) (readFrontierFormula request state right)
  | .disj left right => readBinary Bool.or
      (readFrontierFormula request state left) (readFrontierFormula request state right)
  | .imp left right => readBinary (fun first second => !first || second)
      (readFrontierFormula request state left) (readFrontierFormula request state right)
  | .neg inner => readNegation (readFrontierFormula request state inner)
  | .root index =>
      match request.plan.snapshot.language.terms[index]? with
      | none => none
      | some declaration =>
          if request.expected == .base declaration.category then
            readFrontierStructural request state ⟨index, declaration⟩ else none
  | .split _ _ _ => none
  | .spatial _ _ _ => none

def frontierEquation (request : Request) (expected : TypeExpr) : Pattern → Pattern → Prop :=
  Relation.EqvGen (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation
    request.plan request.bound expected)

/-- This comparison uses the actual executor's equation relation, rather
than an arbitrary decision predicate supplied to the algorithm. -/
theorem readFrontierFormula_sound {request : Request} {state : State request}
    (admitted : Admitted request) (atom : TypeExpr → Nat → Pattern → Prop) (formula : Formula) :
    ReadoutCorrect (readFrontierFormula request state formula)
      (Holds request.plan.snapshot.language request.plan.snapshot.free request.bound
        (frontierEquation request) atom request.expected formula request.root) := by
  induction formula with
  | top => simp [ReadoutCorrect, readFrontierFormula, Holds]
  | bottom => simp [ReadoutCorrect, readFrontierFormula, Holds]
  | atom index => simp [ReadoutCorrect, readFrontierFormula]
  | conj left right first second =>
      exact readBinary_conjunction_sound first second
  | disj left right first second =>
      exact readBinary_disjunction_sound first second
  | imp left right first second =>
      exact readBinary_implication_sound first second
  | neg inner sound => exact readNegation_sound sound
  | split index left right _ _ => simp [ReadoutCorrect, readFrontierFormula]
  | spatial index left right _ _ => simp [ReadoutCorrect, readFrontierFormula]
  | root index =>
      cases lookup : request.plan.snapshot.language.terms[index]? with
      | none => simp [ReadoutCorrect, readFrontierFormula, lookup]
      | some declaration =>
          simp only [readFrontierFormula, lookup]
          split
          · rename_i sort
            have equal : request.expected = .base declaration.category := by simpa using sort
            intro value answer
            cases value with
            | true =>
                have holds := readFrontierStructural_true answer
                simpa [Holds, lookup, equal, frontierEquation] using holds
            | false =>
                have falsehood := readFrontierStructural_false admitted answer
                simpa [Holds, lookup, equal, frontierEquation] using falsehood
          · simp [ReadoutCorrect]

end Mettapedia.OSLF.NativeTypes.Structural
