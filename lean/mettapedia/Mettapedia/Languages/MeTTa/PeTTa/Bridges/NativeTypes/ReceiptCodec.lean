import Mettapedia.OSLF.NativeTypes.Modal.NativeReceiptRechecking
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentCodec

/-!
# Exact target data for native source receipts

The payload is precisely the descent machine's `StepsAnswer`: declaration
index, matcher trace, captured and completed scoped assignments, ordered
premise history and target. Decoding retains the physical distinction between
symbols, strings, natural numbers and applications. It rejects negative
integers, variables, other grounded values and expressions without a symbol
head.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.ReceiptCodec

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Modal
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MeTTaIL
open PremiseOperationsExecution.GeneralExecution (traceTerm eventsTerm)

mutual
  /-- Decode only the exact physical carrier embedded by `CettaWireAtom.encode`. -/
  def decodeAtom? : Atom → Option Term
    | .symbol name => some (.symbol name)
    | .grounded (.string value) => some (.string value)
    | .grounded (.int (.ofNat value)) => some (.natural value)
    | .expression (.symbol head :: arguments) =>
        Term.application head <$> decodeAtoms? arguments
    | _ => none

  def decodeAtoms? : List Atom → Option (List Term)
    | [] => some []
    | first :: rest => do
        pure ((← decodeAtom? first) :: (← decodeAtoms? rest))
end

mutual
  @[simp] theorem decodeAtom?_encode (term : Term) :
      decodeAtom? (CettaWireAtom.encode term) = some term := by
    cases term with
    | symbol name => rfl
    | string value => rfl
    | natural value => rfl
    | application head arguments =>
        simp only [CettaWireAtom.encode, decodeAtom?, decodeAtoms?_encodeMany]
        rfl

  @[simp] theorem decodeAtoms?_encodeMany (terms : List Term) :
      decodeAtoms? (CettaWireAtom.encodeMany terms) = some terms := by
    cases terms with
    | nil => rfl
    | cons first rest =>
        simp only [CettaWireAtom.encodeMany, decodeAtoms?, decodeAtom?_encode,
          decodeAtoms?_encodeMany]
        rfl
end

mutual
  theorem encode_of_decodeAtom? (atom : Atom) (term : Term)
      (decoded : decodeAtom? atom = some term) : CettaWireAtom.encode term = atom := by
    cases atom with
    | symbol name =>
        cases Option.some.inj decoded
        rfl
    | var name => cases decoded
    | grounded value =>
        cases value with
        | string value =>
            cases Option.some.inj decoded
            rfl
        | int value =>
            cases value with
            | ofNat value =>
                cases Option.some.inj decoded
                rfl
            | negSucc value => cases decoded
        | bool value => cases decoded
        | custom typeName data => cases decoded
    | expression atoms =>
        cases atoms with
        | nil => cases decoded
        | cons first rest =>
            cases first with
            | symbol name =>
                cases tailDecoded : decodeAtoms? rest with
                | none => simp [decodeAtom?, tailDecoded] at decoded
                | some terms =>
                    have same : Term.application name terms = term := by
                      simpa [decodeAtom?, tailDecoded] using decoded
                    rw [← same]
                    simp only [CettaWireAtom.encode]
                    rw [encodeMany_of_decodeAtoms? rest terms tailDecoded]
            | var name => cases decoded
            | grounded value => cases decoded
            | expression elements => cases decoded

  theorem encodeMany_of_decodeAtoms? (atoms : List Atom) (terms : List Term)
      (decoded : decodeAtoms? atoms = some terms) : CettaWireAtom.encodeMany terms = atoms := by
    cases atoms with
    | nil =>
        cases Option.some.inj decoded
        rfl
    | cons first rest =>
        cases firstDecoded : decodeAtom? first with
        | none => simp [decodeAtoms?, firstDecoded] at decoded
        | some term =>
            cases restDecoded : decodeAtoms? rest with
            | none => simp [decodeAtoms?, firstDecoded, restDecoded] at decoded
            | some tail =>
                have same : term :: tail = terms := by
                  simpa [decodeAtoms?, firstDecoded, restDecoded] using decoded
                rw [← same]
                simp only [CettaWireAtom.encodeMany]
                rw [encode_of_decodeAtom? first term firstDecoded,
                  encodeMany_of_decodeAtoms? rest tail restDecoded]
end

theorem decodeAtom?_eq_some_iff (atom : Atom) (term : Term) :
    decodeAtom? atom = some term ↔ atom = CettaWireAtom.encode term := by
  constructor
  · intro decoded
    exact (encode_of_decodeAtom? atom term decoded).symm
  · rintro rfl
    exact decodeAtom?_encode term

/-- Every physical field of a complete source receipt is retained. -/
def encodePayload (payload : NativeReceiptRechecking.Payload) : Term :=
  .application "StepsAnswer" [.natural payload.index, traceTerm payload.trace,
    CompleteExecution.DescentCodec.assignmentTerm payload.captured,
    CompleteExecution.DescentCodec.assignmentTerm payload.completed,
    eventsTerm payload.history, InferenceCettaWire.encodePattern payload.target]

def decodePayload? : Term → Option NativeReceiptRechecking.Payload
  | .application "StepsAnswer" [.natural index, trace, captured, completed, history, target] => do
      pure ⟨index, ← ScopedRuleJobReadoutExecution.decodeTrace? trace,
        ← ScopedRuleJobReadoutExecution.decodeAssignment? captured,
        ← ScopedRuleJobReadoutExecution.decodeAssignment? completed,
        ← ScopedRuleJobReadoutExecution.decodeEvents? history,
        ← InferenceCettaWire.decodePattern target⟩
  | _ => none

@[simp] theorem decodePayload?_encodePayload (payload : NativeReceiptRechecking.Payload) :
    decodePayload? (encodePayload payload) = some payload := by
  cases payload
  simp [encodePayload, decodePayload?, CompleteExecution.DescentCodec.assignmentTerm]

theorem encodePayload_injective : Function.Injective encodePayload := by
  intro first second same
  have decoded := congrArg decodePayload? same
  simpa only [decodePayload?_encodePayload, Option.some.injEq] using decoded

def decodePayloadAtom? (atom : Atom) : Option NativeReceiptRechecking.Payload :=
  decodeAtom? atom >>= decodePayload?

@[simp] theorem decodePayloadAtom?_encodePayload (payload : NativeReceiptRechecking.Payload) :
    decodePayloadAtom? (CettaWireAtom.encode (encodePayload payload)) = some payload := by
  simp [decodePayloadAtom?]

/-- A result from the public scheduled source goal has exactly this payload
encoding; proof fields are erased and no receipt data is erased. -/
theorem answerTerm_eq_encodePayload {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern}
    (result : Scheduled.Result environment (Scheduled.sourceGoal environment bound type source)) :
    CompleteExecution.DescentCodec.answerTerm result =
      encodePayload (NativeReceiptRechecking.read (Scheduled.readReceipt result)) := by
  cases result
  rfl

@[simp] theorem decodePayload?_answerTerm {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern}
    (result : Scheduled.Result environment (Scheduled.sourceGoal environment bound type source)) :
    decodePayload? (CompleteExecution.DescentCodec.answerTerm result) =
      some (NativeReceiptRechecking.read (Scheduled.readReceipt result)) := by
  rw [answerTerm_eq_encodePayload, decodePayload?_encodePayload]

@[simp] theorem decodePayloadAtom?_answerTerm {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern}
    (result : Scheduled.Result environment (Scheduled.sourceGoal environment bound type source)) :
    decodePayloadAtom? (CettaWireAtom.encode (CompleteExecution.DescentCodec.answerTerm result)) =
      some (NativeReceiptRechecking.read (Scheduled.readReceipt result)) := by
  rw [answerTerm_eq_encodePayload, decodePayloadAtom?_encodePayload]

example : decodeAtom? (.grounded (.int (-1))) = none := rfl

example : decodeAtom? (.grounded (.bool true)) = none := rfl

example : decodeAtom? (.expression []) = none := rfl

example : decodeAtom? (.expression [.grounded (.string "head")]) = none := rfl

example : decodeAtom? (.symbol "0") = some (.symbol "0") := rfl

example : decodeAtom? (.grounded (.string "0")) = some (.string "0") := rfl

example : decodeAtom? (.grounded (.int 0)) = some (.natural 0) := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.ReceiptCodec
