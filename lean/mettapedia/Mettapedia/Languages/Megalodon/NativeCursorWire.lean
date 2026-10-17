import Mettapedia.Languages.Megalodon.NativeSyntaxWire
import Mettapedia.Languages.Megalodon.BorrowedProofCursor

/-!
# Ordinary MeTTa data for local Megalodon proof rows

The decoder covers all local inference constructors and every judgment
coordinate. The selected environment is retained by the service, not decoded
from a proof row. Contexts, premise order, repeated edges and source origins
survive a round trip. A parsed row is still untrusted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeCursorWire

open MathdataKernel ProofJudgment BorrowedProofCursor NativeSyntaxWire

def encodeContext (context : Context) : Wire :=
  .application "Megalodon.context" [.natural context.typeDepth,
    .application "types" (context.terms.map encodeTp),
    .application "hypotheses" (context.hypotheses.map encodeTm)]

def decodeContext : Wire → Option Context
  | .application "Megalodon.context" [.natural depth, .application "types" types,
      .application "hypotheses" hypotheses] =>
      return ⟨depth, ← decodeList decodeTp types, ← decodeList decodeTm hypotheses⟩
  | _ => none

@[simp] theorem context_roundtrip (context : Context) :
    decodeContext (encodeContext context) = some context := by
  cases context
  simp [encodeContext, decodeContext, decodeList_map, decodeTp_encode, decodeTm_encode]

def encodeJudgment (judgment : Judgment) : Wire :=
  .application "Megalodon.judgment" [encodeContext judgment.context, encodeTm judgment.proposition]

def decodeJudgment : Wire → Option Judgment
  | .application "Megalodon.judgment" [context, proposition] =>
      return ⟨← decodeContext context, ← decodeTm proposition⟩
  | _ => none

@[simp] theorem judgment_roundtrip (judgment : Judgment) :
    decodeJudgment (encodeJudgment judgment) = some judgment := by
  cases judgment; simp [encodeJudgment, decodeJudgment]

def encodeWitness : Witness → Wire
  | .hyp index => .application "Megalodon.hyp" [.natural index]
  | .known name => .application "Megalodon.known" [.string name]
  | .termApp argument domain body =>
      .application "Megalodon.termApp" [encodeTm argument, encodeTp domain, encodeTm body]
  | .proofApp domain => .application "Megalodon.proofApp" [encodeTm domain]
  | .termLam => .application "Megalodon.termLam" []
  | .proofLam source => .application "Megalodon.proofLam" [encodeTm source]
  | .typeApp type body => .application "Megalodon.typeApp" [encodeTp type, encodeTm body]
  | .typeLam => .application "Megalodon.typeLam" []

def decodeWitness : Wire → Option Witness
  | .application "Megalodon.hyp" [.natural index] => some (.hyp index)
  | .application "Megalodon.known" [.string name] => some (.known name)
  | .application "Megalodon.termApp" [argument, domain, body] =>
      return .termApp (← decodeTm argument) (← decodeTp domain) (← decodeTm body)
  | .application "Megalodon.proofApp" [domain] => return .proofApp (← decodeTm domain)
  | .application "Megalodon.termLam" [] => some .termLam
  | .application "Megalodon.proofLam" [source] => return .proofLam (← decodeTm source)
  | .application "Megalodon.typeApp" [type, body] => return .typeApp (← decodeTp type) (← decodeTm body)
  | .application "Megalodon.typeLam" [] => some .typeLam
  | _ => none

@[simp] theorem witness_roundtrip (witness : Witness) :
    decodeWitness (encodeWitness witness) = some witness := by
  cases witness <;> simp [encodeWitness, decodeWitness]

def encodeNat (n : Nat) : Wire := .natural n

def decodeNat : Wire → Option Nat
  | .natural value => some value
  | _ => none

def encodeNode (node : SourceNode) : Wire :=
  .application "Megalodon.row" [encodeJudgment node.conclusion, encodeWitness node.request,
    .application "parents" (node.parents.map encodeNat), .natural node.origin]

def decodeNode : Wire → Option SourceNode
  | .application "Megalodon.row" [judgment, witness, .application "parents" parents, .natural origin] =>
      return ⟨← decodeJudgment judgment, ← decodeWitness witness, ← decodeList decodeNat parents, origin⟩
  | _ => none

@[simp] theorem node_roundtrip (node : SourceNode) : decodeNode (encodeNode node) = some node := by
  cases node
  simp [encodeNode, decodeNode, decodeList_map encodeNat decodeNat (fun _ => rfl)]

theorem encodeNode_injective : Function.Injective encodeNode := by
  intro first second same
  simpa only [node_roundtrip, Option.some.injEq] using congrArg decodeNode same

/-- No retained authority or pointer is serialized: a decoded row must still
pass the selected inference interface against the actual checked parents. -/
def checkWireRow (environment : Environment) (fuel : Nat) (parents : List Judgment) (wire : Wire) : Bool :=
  match decodeNode wire with
  | none => false
  | some node => (interface environment fuel).isInstance node.request parents node.conclusion

theorem check_encoded_row (environment : Environment) (fuel : Nat)
    (parents : List Judgment) (node : SourceNode) :
    checkWireRow environment fuel parents (encodeNode node) =
      (interface environment fuel).isInstance node.request parents node.conclusion := by
  simp [checkWireRow]

theorem accepted_wire_row_sound {environment : Environment} {fuel : Nat}
    {parents : List Judgment} {wire : Wire} (accepted : checkWireRow environment fuel parents wire = true) :
    ∃ node, decodeNode wire = some node ∧ Rules environment fuel parents node.conclusion := by
  cases decoded : decodeNode wire with
  | none => simp [checkWireRow, decoded] at accepted
  | some node => exact ⟨node, rfl, (interface environment fuel).sound _ _ _
      (by simpa [checkWireRow, decoded] using accepted)⟩

theorem repeated_edges_preserved (judgment : Judgment) (witness : Witness) (origin address : Nat) :
    (decodeNode (encodeNode ⟨judgment, witness, [address, address], origin⟩)).map
      (fun node => node.parents) = some [address, address] := by simp

theorem theorem_text_is_not_a_row : decodeNode (.application "Sealed" [.string "theorem"]) = none := rfl
theorem authority_field_is_not_allowed :
    decodeNode (.application "Megalodon.row" [.natural 0, .natural 0]) = none := rfl
theorem proof_app_wrong_arity : decodeWitness (.application "Megalodon.proofApp" []) = none := rfl

end Mettapedia.Languages.Megalodon.NativeCursorWire
