import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend

/-! # Finite controls for the source-bound array specialization -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef IndexedInductive

def num (value : Int) : Atom := .grounded (.int value)
def array (values : List Int) : Atom := .expression (values.map num)
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def bind (name : String) (value body : Atom) : Atom := call "let" [.var name, value, body]

structure Fixture where
  label : String
  code : Atom
  answers : List Atom

def fixtures : List Fixture := [
  ⟨"ordered", appendCall (array [1, 2]) (array [3, 4]), [array [1, 2, 3, 4]]⟩,
  ⟨"duplicates", appendCall (array [1, 1]) (array [1, 2]), [array [1, 1, 1, 2]]⟩,
  ⟨"empty-left", appendCall (array []) (array [2]), [array [2]]⟩,
  ⟨"empty-right", appendCall (array [1]) (array []), [array [1]]⟩,
  ⟨"empty-both", appendCall (array []) (array []), [array []]⟩,
  ⟨"reused-array", bind "first" (appendCall (array [1]) (array [2]))
    (appendCall (.var "first") (array [3])), [array [1, 2, 3]]⟩,
  ⟨"input-retained", bind "first" (appendCall (array [1]) (array [2]))
    (bind "second" (appendCall (.var "first") (array [3])) (.var "first")), [array [1, 2]]⟩,
  ⟨"length", bind "values" (appendCall (array [1, 1]) (array [2]))
    (call "gslt:inductive:length" [.var "values"]), [num 3]⟩,
  ⟨"length-addition", bind "left" (call "gslt:inductive:length" [array [1, 1]])
    (bind "right" (call "gslt:inductive:length" [array [2]])
      (call "gslt:inductive:add" [.var "left", .var "right"])), [num 3]⟩,
  ⟨"big-natural", call "gslt:inductive:add" [num 340282366920938463463374607431768211456, num 1],
    [num 340282366920938463463374607431768211457]⟩,
  ⟨"big-reused", bind "large" (call "gslt:inductive:add"
      [num 340282366920938463463374607431768211456, num 1])
    (call "gslt:inductive:add" [.var "large", num 2]),
    [num 340282366920938463463374607431768211459]⟩,
  ⟨"big-array-payload", appendCall (array [340282366920938463463374607431768211456])
    (array [340282366920938463463374607431768211456]),
    [array [340282366920938463463374607431768211456, 340282366920938463463374607431768211456]]⟩]

/-- This is outside the qualified native natural-payload profile. It remains
an accepted value in the Lean PeTTa model, making native demand drift visible. -/
def payloadBoundary : Fixture :=
  ⟨"code-payload", appendCall (.expression [call "+" [num 1, num 2]]) (array [4]),
    [.expression [call "+" [num 1, num 2], num 4]]⟩

def naturalPayload (value : Nat) : Atom := num value

def readsNatural : Atom → Bool
  | .grounded (.int (.ofNat _)) => true
  | _ => false

theorem natural_payload_admitted (value : Nat) : readsNatural (naturalPayload value) = true := rfl
theorem code_payload_not_admitted : readsNatural (call "+" [num 1, num 2]) = false := rfl
theorem natural_payload_injective : Function.Injective naturalPayload := by
  intro left right same
  cases same
  rfl

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
open Guest.VectorMeaning Guest.AppendMeaning Guest.AppendTyping

private theorem natural_element : Selected.Typed .nil natTm (sortTm elementLevel) := by
  apply FormationSensitive.Typing.cumul (Selected.constructors.nat_formed .nil)
  change ∀ valuation : Nat → Nat, 0 ≤ valuation 0
  exact fun _ => Nat.zero_le _

/-- A nonempty typed source instance uses faithful natural payloads on both
sides. Repeated values remain repeated array entries. -/
theorem nonempty_typed_join :
    ProgramExecutes
      (Declaration.IndexedFamily.applyArgs Programs.appendTerm
        [natTm, numeral 2, numeral 1,
          VectorArray.quoteArray natTm numeral #[1, 1], VectorArray.quoteArray natTm numeral #[2]])
      (VectorArray.quoteArray natTm numeral #[1, 1, 2]) ∧
    FormationSensitive.Judgment Selected.rules .nil
      (VectorArray.quoteArray natTm numeral #[1, 1, 2])
      (vecApp natTm (Programs.add (numeral 2) (numeral 1))) ∧
    Eval.PureReturns library.runtime [] Effects.empty
      (appendCall (array [1, 1]) (array [2])) Effects.empty (array [1, 1, 2]) := by
  have joined := actual_program_contract Effects.empty natTm numeral naturalPayload
    natural_element (Selected.constructors.numeral_typed .nil) #[1, 1] #[2]
  exact joined.2

def answers? (fuel : Nat) (code : Atom) : Option (List Atom) :=
  match Eval.evaluate library.runtime fuel Effects.empty code with
  | .complete _ answers [] [] => some answers
  | _ => none

def runtimeChecks : Bool := fixtures.all fun fixture => answers? 400 fixture.code == some fixture.answers

theorem runtime_checks : runtimeChecks = true := by decide +kernel

theorem payload_boundary_model :
    answers? 400 payloadBoundary.code = some payloadBoundary.answers := by decide +kernel

def paused : Eval.Outcome := Eval.evaluate library.runtime 2 Effects.empty
  (appendCall (array [1]) (array [2]))

def resumeCheck : Bool := match paused with
  | .exhausted continuation => match Eval.run library.runtime 400 continuation with
    | .complete _ answers [] [] => answers == [array [1, 2]]
    | _ => false
  | _ => false

theorem resumable : resumeCheck = true := by decide +kernel
theorem exhausted_is_not_a_negative_answer :
    answers? 0 (appendCall (array [1]) (array [2])) = none := by decide +kernel

def rejectsChangedSource : Bool :=
  ((AppendSource.changedRules fun rows => rows.map fun row =>
    { row with right := .apply "VNil" [.fvar "A"] }).map supports).getD false == false

theorem rejects_changed_source : rejectsChangedSource = true := by decide +kernel

theorem wrong_packets :
    answers? 400 (appendCall (array [1, 1]) (array [2])) ≠ some [array [1, 2]] ∧
    answers? 400 (appendCall (array [1, 1]) (array [2])) ≠ some [array [1, 1, 2, 2]] ∧
    answers? 400 (appendCall (array [1, 1]) (array [2])) ≠ some [array [2, 1, 1]] ∧
    answers? 400 (appendCall (array [1, 1]) (array [2])) ≠ some [array [1, 1, 2], array [1, 1, 2]] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend.Controls
