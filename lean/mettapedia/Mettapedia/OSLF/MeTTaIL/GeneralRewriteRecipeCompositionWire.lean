import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeComposition
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeDAG
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeWire

/-!
# Authored requests for composed rewrite evidence

Literal traces and equation-respecting semantic traces retain their distinct
source observations. These request forms carry the full original authored
snapshot, permissions, caller context, type and endpoints. Every rewrite
recipe is checked against the plan compiled from that same request header.

Reflexive DAG nodes share the same raw-carrier boundary as empty traces.
Every declared DAG node, root and reference is retained without collapsing
repeated reference uses.

Empty traces express reflexivity on the source GSLT's raw `Pattern` carrier.
Their acceptance alone supplies no formation or typing judgment. Nonempty
rewrite nodes retain the original typed occurrence admission. The wire adds
neither a global formation restriction nor a universal-execution claim.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeCompositionWire

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralExecutionAdmission GeneralRewriteRecipeComposition
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.GSLT.LanguageDef

def linkCodec : Codec Link :=
  (Codec.prod GeneralPremiseReceiptWire.patternCodec GeneralRewriteRecipeWire.stepTraceCodec).mapped
    (fun value => (value.next, value.step))
    (fun fields => some ⟨fields.1, fields.2⟩)
    (fun _ => rfl)

def traceCodec : Codec Trace := Codec.list linkCodec

def semanticTraceCodec : Codec SemanticTrace :=
  (Codec.prod GeneralPremiseReceiptWire.patternCodec
    (Codec.prod GeneralPremiseReceiptWire.patternCodec
      (Codec.prod (Codec.list GeneralRewriteRecipeWire.conversionCodec)
        (Codec.prod traceCodec (Codec.list GeneralRewriteRecipeWire.conversionCodec))))).mapped
    (fun value => (value.startRepresentative, value.endRepresentative, value.before, value.trace, value.after))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2⟩)
    (fun _ => rfl)

/-- Literal authored context for every node and join of the submitted trace. -/
structure Header where
  snapshot : Snapshot
  permissions : Permissions
  bound : List TypeExpr
  type : TypeExpr
  source : Pattern
  target : Pattern
  deriving Repr

def headerCodec : Codec Header :=
  (Codec.prod GeneralPremiseReceiptWire.snapshotCodec
    (Codec.prod GeneralPremiseReceiptWire.permissionsCodec
      (Codec.prod (Codec.list BindingSyntax.Wire.typeCodec)
        (Codec.prod BindingSyntax.Wire.typeCodec
          (Codec.prod GeneralPremiseReceiptWire.patternCodec GeneralPremiseReceiptWire.patternCodec))))).mapped
    (fun value => (value.snapshot, value.permissions, value.bound, value.type, value.source, value.target))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      fields.2.2.2.2.1, fields.2.2.2.2.2⟩)
    (fun _ => rfl)

def Header.ofAtomic (request : GeneralRewriteRecipeWire.Request) : Header :=
  ⟨request.snapshot, request.permissions, request.bound, request.type, request.source, request.target⟩

structure TraceRequest where
  header : Header
  trace : Trace
  deriving Repr

structure SemanticRequest where
  header : Header
  evidence : SemanticTrace
  deriving Repr

private def tagged {Value : Type} (tag : String) (payload : Codec Value) : Codec Value :=
  (Codec.prod Codec.string payload).mapped
    (fun value => (tag, value))
    (fun fields => if fields.1 = tag then some fields.2 else none)
    (fun _ => by simp only [ite_true])

def traceRequestTag : String := "gslt-authored-rewrite-trace-v1"
def semanticRequestTag : String := "gslt-authored-semantic-trace-v1"

def traceRequestCodec : Codec TraceRequest := tagged traceRequestTag
  ((Codec.prod headerCodec traceCodec).mapped
    (fun request => (request.header, request.trace))
    (fun fields => some ⟨fields.1, fields.2⟩)
    (fun _ => rfl))

def semanticRequestCodec : Codec SemanticRequest := tagged semanticRequestTag
  ((Codec.prod headerCodec semanticTraceCodec).mapped
    (fun request => (request.header, request.evidence))
    (fun fields => some ⟨fields.1, fields.2⟩)
    (fun _ => rfl))

def TraceRequest.Valid (request : TraceRequest) : Prop :=
  Trace.Valid (compile request.header.snapshot request.header.permissions) request.header.bound request.header.type
    request.trace request.header.source request.header.target

def SemanticRequest.Valid (request : SemanticRequest) : Prop :=
  SemanticTrace.Valid (compile request.header.snapshot request.header.permissions) request.header.bound request.header.type
    request.header.source request.header.target request.evidence

def checkTraceRequest (request : TraceRequest) : Bool :=
  Trace.check (compile request.header.snapshot request.header.permissions) request.header.bound request.header.type
    request.header.source request.header.target request.trace

def checkSemanticRequest (request : SemanticRequest) : Bool :=
  SemanticTrace.check (compile request.header.snapshot request.header.permissions) request.header.bound request.header.type
    request.header.source request.header.target request.evidence

theorem checkTraceRequest_exact (request : TraceRequest) :
    checkTraceRequest request = true ↔ request.Valid := Trace.check_exact _ _ _ _ _ _

theorem checkSemanticRequest_exact (request : SemanticRequest) :
    checkSemanticRequest request = true ↔ request.Valid := SemanticTrace.check_exact _ _ _ _ _ _

/-- The original empty-path rule compares endpoints, without supplying a
separate source formation witness. -/
theorem empty_trace_exact (header : Header) :
    checkTraceRequest ⟨header, []⟩ = true ↔ header.source = header.target :=
  (checkTraceRequest_exact _).trans (Trace.valid_nil_iff _ _ _ _ _)

theorem reflexive_raw_carrier (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (type : TypeExpr) (raw : Pattern) :
    checkTraceRequest ⟨⟨snapshot, permissions, bound, type, raw, raw⟩, []⟩ = true :=
  (empty_trace_exact _).mpr rfl

def encodeTraceRequest (request : TraceRequest) : List Binary.Alphabet :=
  Binary.encodeWith traceRequestCodec request

def decodeTraceRequest (word : List Binary.Alphabet) : Option TraceRequest :=
  Binary.canonicalDecodeWith traceRequestCodec word

theorem decodeTraceRequest_encodeTraceRequest (request : TraceRequest) :
    decodeTraceRequest (encodeTraceRequest request) = some request :=
  Binary.canonicalDecodeWith_encodeWith traceRequestCodec request

theorem decodeTraceRequest_exact (word : List Binary.Alphabet) (request : TraceRequest) :
    decodeTraceRequest word = some request ↔ encodeTraceRequest request = word :=
  Binary.canonicalDecodeWith_exact traceRequestCodec word request

theorem encodeTraceRequest_injective : Function.Injective encodeTraceRequest :=
  Binary.encodeWith_injective traceRequestCodec

theorem decodeTraceRequest_trailing_refused (request : TraceRequest) (tail : List Binary.Alphabet)
    (nonempty : tail.isEmpty = false) :
    decodeTraceRequest (encodeTraceRequest request ++ tail) = none :=
  Binary.canonicalDecodeWith_trailing_refused traceRequestCodec request tail nonempty

def encodeSemanticRequest (request : SemanticRequest) : List Binary.Alphabet :=
  Binary.encodeWith semanticRequestCodec request

def decodeSemanticRequest (word : List Binary.Alphabet) : Option SemanticRequest :=
  Binary.canonicalDecodeWith semanticRequestCodec word

theorem decodeSemanticRequest_encodeSemanticRequest (request : SemanticRequest) :
    decodeSemanticRequest (encodeSemanticRequest request) = some request :=
  Binary.canonicalDecodeWith_encodeWith semanticRequestCodec request

theorem decodeSemanticRequest_exact (word : List Binary.Alphabet) (request : SemanticRequest) :
    decodeSemanticRequest word = some request ↔ encodeSemanticRequest request = word :=
  Binary.canonicalDecodeWith_exact semanticRequestCodec word request

theorem encodeSemanticRequest_injective : Function.Injective encodeSemanticRequest :=
  Binary.encodeWith_injective semanticRequestCodec

theorem decodeSemanticRequest_trailing_refused (request : SemanticRequest) (tail : List Binary.Alphabet)
    (nonempty : tail.isEmpty = false) :
    decodeSemanticRequest (encodeSemanticRequest request ++ tail) = none :=
  Binary.canonicalDecodeWith_trailing_refused semanticRequestCodec request tail nonempty

def checkTraceWord (word : List Binary.Alphabet) : Bool :=
  match decodeTraceRequest word with
  | none => false
  | some request => checkTraceRequest request

def checkSemanticWord (word : List Binary.Alphabet) : Bool :=
  match decodeSemanticRequest word with
  | none => false
  | some request => checkSemanticRequest request

theorem checkTraceWord_exact (word : List Binary.Alphabet) :
    checkTraceWord word = true ↔ ∃ request, encodeTraceRequest request = word ∧ request.Valid := by
  have decoded : checkTraceWord word = true ↔
      ∃ request, decodeTraceRequest word = some request ∧ request.Valid := by
    cases result : decodeTraceRequest word with
    | none => simp [checkTraceWord, result]
    | some request => simp [checkTraceWord, result, checkTraceRequest_exact]
  simpa only [decodeTraceRequest_exact] using decoded

theorem checkSemanticWord_exact (word : List Binary.Alphabet) :
    checkSemanticWord word = true ↔ ∃ request, encodeSemanticRequest request = word ∧ request.Valid := by
  have decoded : checkSemanticWord word = true ↔
      ∃ request, decodeSemanticRequest word = some request ∧ request.Valid := by
    cases result : decodeSemanticRequest word with
    | none => simp [checkSemanticWord, result]
    | some request => simp [checkSemanticWord, result, checkSemanticRequest_exact]
  simpa only [decodeSemanticRequest_exact] using decoded

@[simp] theorem checkTraceWord_encodeTraceRequest (request : TraceRequest) :
    checkTraceWord (encodeTraceRequest request) = checkTraceRequest request := by
  simp only [checkTraceWord, decodeTraceRequest_encodeTraceRequest]

@[simp] theorem checkSemanticWord_encodeSemanticRequest (request : SemanticRequest) :
    checkSemanticWord (encodeSemanticRequest request) = checkSemanticRequest request := by
  simp only [checkSemanticWord, decodeSemanticRequest_encodeSemanticRequest]

theorem exists_checked_trace_iff_rewritePath (header : Header) :
    (∃ trace, checkTraceWord (encodeTraceRequest ⟨header, trace⟩) = true) ↔
      Nonempty ((GeneralOccurrenceSemantics.gslt (compile header.snapshot header.permissions)
        header.bound header.type).RewritePath header.source header.target) := by
  simpa only [checkTraceWord_encodeTraceRequest, checkTraceRequest] using
    Trace.exists_checked_iff_rewritePath (compile header.snapshot header.permissions)
      header.bound header.type header.source header.target

theorem exists_checked_semantic_iff_semanticPath (header : Header) :
    (∃ evidence, checkSemanticWord (encodeSemanticRequest ⟨header, evidence⟩) = true) ↔
      Nonempty (Mettapedia.OSLF.Framework.PathTypeSynthesis.SemanticPath
        (GeneralOccurrenceSemantics.gslt (compile header.snapshot header.permissions) header.bound header.type)
        header.source header.target) := by
  simpa only [checkSemanticWord_encodeSemanticRequest, checkSemanticRequest] using
    SemanticTrace.exists_checked_iff_semanticPath (compile header.snapshot header.permissions)
      header.bound header.type header.source header.target


private def dagConversionFields := Codec.prod GeneralPremiseReceiptWire.patternCodec
  (Codec.prod GeneralPremiseReceiptWire.patternCodec (Codec.list GeneralRewriteRecipeWire.conversionCodec))
private def dagAtomicFields := Codec.prod GeneralPremiseReceiptWire.patternCodec
  (Codec.prod GeneralPremiseReceiptWire.patternCodec GeneralRewriteRecipeWire.stepTraceCodec)
private def dagTransFields := Codec.prod GeneralPremiseReceiptWire.patternCodec
  (Codec.prod GeneralPremiseReceiptWire.patternCodec
    (Codec.prod GeneralPremiseReceiptWire.patternCodec (Codec.prod Codec.nat Codec.nat)))

private def putDAGNode : GeneralRewriteRecipeDAG.Node → Data
  | .refl state => .pair (.atom 0) (GeneralPremiseReceiptWire.patternCodec.put state)
  | .conversion source target walk => .pair (.atom 1) (dagConversionFields.put (source, target, walk))
  | .atomic source target recipe => .pair (.atom 2) (dagAtomicFields.put (source, target, recipe))
  | .trans source middle target left right => .pair (.atom 3) (dagTransFields.put (source, middle, target, left, right))

private def getDAGNode : Data → Option GeneralRewriteRecipeDAG.Node
  | .pair (.atom 0) state => (GeneralPremiseReceiptWire.patternCodec.get state).map .refl
  | .pair (.atom 1) fields => (dagConversionFields.get fields).map fun value =>
      .conversion value.1 value.2.1 value.2.2
  | .pair (.atom 2) fields => (dagAtomicFields.get fields).map fun value =>
      .atomic value.1 value.2.1 value.2.2
  | .pair (.atom 3) fields => (dagTransFields.get fields).map fun value =>
      .trans value.1 value.2.1 value.2.2.1 value.2.2.2.1 value.2.2.2.2
  | _ => none

def dagNodeCodec : Codec GeneralRewriteRecipeDAG.Node := ⟨putDAGNode, getDAGNode, fun value => by
  cases value <;> simp only [putDAGNode, getDAGNode, Codec.get_put] <;> rfl⟩

def graphCodec : Codec GeneralRewriteRecipeDAG.Graph :=
  (Codec.prod (Codec.list dagNodeCodec) Codec.nat).mapped
    (fun value => (value.nodes, value.root))
    (fun fields => some ⟨fields.1, fields.2⟩)
    (fun _ => rfl)

/-- Sharing references identify certificate nodes. The original source
checker still validates every declared row and every separate reference use. -/
structure DAGRequest where
  header : Header
  graph : GeneralRewriteRecipeDAG.Graph
  deriving Repr

def dagRequestTag : String := "gslt-authored-rewrite-dag-v1"

def dagRequestCodec : Codec DAGRequest := tagged dagRequestTag
  ((Codec.prod headerCodec graphCodec).mapped
    (fun request => (request.header, request.graph))
    (fun fields => some ⟨fields.1, fields.2⟩)
    (fun _ => rfl))

def DAGRequest.Valid (request : DAGRequest) : Prop :=
  GeneralRewriteRecipeDAG.Graph.Valid (compile request.header.snapshot request.header.permissions)
    request.header.bound request.header.type request.graph (request.header.source, request.header.target)

def checkDAGRequest (request : DAGRequest) : Bool :=
  GeneralRewriteRecipeDAG.Graph.check (compile request.header.snapshot request.header.permissions)
    request.header.bound request.header.type request.graph (request.header.source, request.header.target)

theorem checkDAGRequest_exact (request : DAGRequest) :
    checkDAGRequest request = true ↔ request.Valid := GeneralRewriteRecipeDAG.Graph.check_exact _ _ _ _ _

def encodeDAGRequest (request : DAGRequest) : List Binary.Alphabet :=
  Binary.encodeWith dagRequestCodec request

def decodeDAGRequest (word : List Binary.Alphabet) : Option DAGRequest :=
  Binary.canonicalDecodeWith dagRequestCodec word

theorem decodeDAGRequest_encodeDAGRequest (request : DAGRequest) :
    decodeDAGRequest (encodeDAGRequest request) = some request :=
  Binary.canonicalDecodeWith_encodeWith dagRequestCodec request

theorem decodeDAGRequest_exact (word : List Binary.Alphabet) (request : DAGRequest) :
    decodeDAGRequest word = some request ↔ encodeDAGRequest request = word :=
  Binary.canonicalDecodeWith_exact dagRequestCodec word request

theorem encodeDAGRequest_injective : Function.Injective encodeDAGRequest :=
  Binary.encodeWith_injective dagRequestCodec

theorem decodeDAGRequest_trailing_refused (request : DAGRequest) (tail : List Binary.Alphabet)
    (nonempty : tail.isEmpty = false) :
    decodeDAGRequest (encodeDAGRequest request ++ tail) = none :=
  Binary.canonicalDecodeWith_trailing_refused dagRequestCodec request tail nonempty

def checkDAGWord (word : List Binary.Alphabet) : Bool :=
  match decodeDAGRequest word with
  | none => false
  | some request => checkDAGRequest request

theorem checkDAGWord_exact (word : List Binary.Alphabet) :
    checkDAGWord word = true ↔ ∃ request, encodeDAGRequest request = word ∧ request.Valid := by
  have decoded : checkDAGWord word = true ↔
      ∃ request, decodeDAGRequest word = some request ∧ request.Valid := by
    cases result : decodeDAGRequest word with
    | none => simp [checkDAGWord, result]
    | some request => simp [checkDAGWord, result, checkDAGRequest_exact]
  simpa only [decodeDAGRequest_exact] using decoded

@[simp] theorem checkDAGWord_encodeDAGRequest (request : DAGRequest) :
    checkDAGWord (encodeDAGRequest request) = checkDAGRequest request := by
  simp only [checkDAGWord, decodeDAGRequest_encodeDAGRequest]

theorem exists_checked_dag_iff_semanticPath (header : Header) :
    (∃ graph, checkDAGWord (encodeDAGRequest ⟨header, graph⟩) = true) ↔
      Nonempty (Mettapedia.OSLF.Framework.PathTypeSynthesis.SemanticPath
        (GeneralOccurrenceSemantics.gslt (compile header.snapshot header.permissions) header.bound header.type)
        header.source header.target) := by
  simpa only [checkDAGWord_encodeDAGRequest, checkDAGRequest] using
    GeneralRewriteRecipeDAG.exists_checked_iff_semanticPath (compile header.snapshot header.permissions)
      header.bound header.type header.source header.target

end Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeCompositionWire
