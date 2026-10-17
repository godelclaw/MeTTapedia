import Mettapedia.Languages.OpenTheory.StorageSize
import Mettapedia.Languages.HOLLight.GraphExpansion

/-!
# Full payload size of actual HOL Light certificates

The concrete account charges every request field, copied premise theorem,
output theorem, axiom tag, origin string and binary numeric field. Physical
parent indices use the existing binary graph account. The selected root is
also included. Semantic proof fields are erased.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.StorageSize

open Mettapedia.Languages.OpenTheory
open SourceSubstitution
open ProofExecution
open GraphExpansion (graphWeight primitiveBlock)

def typeMaplet (entry : Ty × Ty) : Nat := 1 + OpenTheory.StorageSize.ty entry.1 + OpenTheory.StorageSize.ty entry.2

def termMaplet (entry : TermMaplet) : Nat :=
  1 + OpenTheory.StorageSize.checkedSource entry.1 + OpenTheory.StorageSize.sourceTerm entry.2

def inferenceRequest : InferenceRequest → Nat
  | .refl value | .assume value => 1 + OpenTheory.StorageSize.canonical value
  | .trans left right | .mkComb left right | .eqMp left right | .deductAntisym left right =>
      1 + OpenTheory.StorageSize.theoremData left + OpenTheory.StorageSize.theoremData right
  | .abs binder input => 1 + OpenTheory.StorageSize.sourceVar binder + OpenTheory.StorageSize.theoremData input
  | .beta value => 1 + OpenTheory.StorageSize.checkedSource value
  | .instType entries input => 1 + OpenTheory.StorageSize.list typeMaplet entries + OpenTheory.StorageSize.theoremData input
  | .inst entries input => 1 + OpenTheory.StorageSize.list termMaplet entries + OpenTheory.StorageSize.theoremData input

def request : RuleRequest → Nat
  | .inference value => 1 + inferenceRequest value
  | .axiom value => 1 + OpenTheory.StorageSize.sequent value

def origin (value : Origin) : Nat := 1 + OpenTheory.StorageSize.string value.1 + OpenTheory.StorageSize.nat value.2

/-- The payload retained in an actual physical graph occurrence. -/
def receiptPayload (conclusion : Theorem) (witness : RuleRequest) (source : Origin) : Nat :=
  1 + OpenTheory.StorageSize.theoremData conclusion + request witness + origin source

/-- Framing, full payloads, physical parent addresses and the selected root. -/
def certificateUnits (value : ProofSystem.Certificate) : Nat :=
  1 + GraphExpansion.binaryGraphWeight receiptPayload value.1 + OpenTheory.StorageSize.nat value.2

def certificateBits (value : ProofSystem.Certificate) : Nat := 8 * certificateUnits value

/-- Relocating a graph changes only addresses, whose binary charge is retained
separately. Every UTF-8/type/theorem/request/origin payload is unchanged. -/
theorem relocated_payload (roots : List Nat) (base : Nat) (block : ProofSystem.Certificate) :
    GraphExpansion.graphWeight receiptPayload (GraphExpansion.expandBlock roots base block).1 =
      GraphExpansion.graphWeight receiptPayload block.1 :=
  GraphExpansion.expandBlock_weight receiptPayload roots base block

/-- Repeated theorem premises are charged at every stored request occurrence,
even if their physical parent indices coincide. -/
@[simp] theorem repeated_premise (value : Theorem) :
    request (.inference (.trans value value)) = 2 + 2 * OpenTheory.StorageSize.theoremData value := by
  simp [request, inferenceRequest]; omega

/-- The payload account depends on namespace contents, not only term shape. -/
theorem namespace_bytes_charged (names : List String) (component : String) :
    OpenTheory.StorageSize.name ⟨names, component⟩ =
      3 + (names.map (fun value => 1 + value.utf8ByteSize)).sum + component.utf8ByteSize := by
  change 1 + (1 + (names.map (fun value => 1 + value.utf8ByteSize)).sum) +
    (1 + component.utf8ByteSize) = _
  omega

/-- Every primitive request retains its conclusion and its complete witness,
including copied theorem premises. -/
theorem primitive_payload (witness : RuleRequest) (conclusion : Theorem) (source : Origin) :
    GraphExpansion.graphWeight receiptPayload (GraphExpansion.primitiveBlock witness conclusion source).1 =
      receiptPayload conclusion witness source + witness.premises.length + 1 := by
  simp [GraphExpansion.primitiveBlock, GraphExpansion.graphWeight, GraphExpansion.receiptWeight]

/-- Successful block emission appends its full payload without expanding the
shared external theorem proofs. Binary address relocation is charged separately. -/
theorem emitBlock_payload {policy : AxiomPolicy} [DecidablePred policy]
    {roots : List Nat} {block : ProofSystem.Certificate}
    {state result : ProofExecution.State} {root : Nat}
    (emitted : GraphExpansion.emitBlock policy roots block state = some (result, root)) :
    GraphExpansion.graphWeight receiptPayload result.receipts.toList =
      GraphExpansion.graphWeight receiptPayload state.receipts.toList +
        GraphExpansion.graphWeight receiptPayload block.1 :=
  GraphExpansion.emitBlock_weight receiptPayload emitted

/-- The stored payload of a chronological plan is exactly the sum of its
concrete local block payloads and the existing graph prefix. -/
theorem emitPlan_payload {policy : AxiomPolicy} [DecidablePred policy]
    {state result : ProofExecution.State} {roots finalRoots : Array Nat}
    {requests : List GraphExpansion.BlockRequest}
    (emitted : GraphExpansion.emitPlan policy state roots requests = some (result, finalRoots)) :
    GraphExpansion.graphWeight receiptPayload result.receipts.toList =
      GraphExpansion.graphWeight receiptPayload state.receipts.toList +
        (requests.map (fun request => GraphExpansion.graphWeight receiptPayload request.witness.1)).sum :=
  GraphExpansion.emitPlan_weight receiptPayload emitted

theorem finishPlan_payload {policy : AxiomPolicy} [DecidablePred policy]
    {state : ProofExecution.State} {roots : Array Nat} {requests : List GraphExpansion.BlockRequest}
    {index : Nat} {block : ProofSystem.Certificate}
    (emitted : GraphExpansion.finishPlan policy state roots requests index = some block) :
    GraphExpansion.graphWeight receiptPayload block.1 =
      GraphExpansion.graphWeight receiptPayload state.receipts.toList +
        (requests.map (fun request => GraphExpansion.graphWeight receiptPayload request.witness.1)).sum :=
  GraphExpansion.finishPlan_weight receiptPayload emitted

theorem eqMp_payload (equation premise result : Theorem) (origin : Origin) :
    graphWeight StorageSize.receiptPayload
      (primitiveBlock (.inference (.eqMp equation premise)) result origin).1 =
      6 + OpenTheory.StorageSize.theoremData result + OpenTheory.StorageSize.theoremData equation +
        OpenTheory.StorageSize.theoremData premise + StorageSize.origin origin := by
  rw [StorageSize.primitive_payload]
  simp only [StorageSize.receiptPayload, StorageSize.request, StorageSize.inferenceRequest,
    RuleRequest.premises, InferenceRequest.premises, List.length_cons, List.length_nil]
  omega

theorem refl_payload (value : CanonicalTerm) (result : Theorem) (origin : Origin) :
    graphWeight StorageSize.receiptPayload
      (primitiveBlock (.inference (.refl value)) result origin).1 =
      4 + OpenTheory.StorageSize.theoremData result + OpenTheory.StorageSize.canonical value +
        StorageSize.origin origin := by
  rw [StorageSize.primitive_payload]
  simp only [StorageSize.receiptPayload, StorageSize.request, StorageSize.inferenceRequest,
    RuleRequest.premises, InferenceRequest.premises, List.length_nil]
  omega

theorem app_payload (first second result : Theorem) (origin : Origin) :
    graphWeight StorageSize.receiptPayload
      (primitiveBlock (.inference (.mkComb first second)) result origin).1 =
      6 + OpenTheory.StorageSize.theoremData result + OpenTheory.StorageSize.theoremData first +
        OpenTheory.StorageSize.theoremData second + StorageSize.origin origin := by
  rw [StorageSize.primitive_payload]
  simp only [StorageSize.receiptPayload, StorageSize.request, StorageSize.inferenceRequest,
    RuleRequest.premises, InferenceRequest.premises, List.length_cons, List.length_nil]
  omega

theorem trans_payload (first second result : Theorem) (origin : Origin) :
    graphWeight StorageSize.receiptPayload
      (primitiveBlock (.inference (.trans first second)) result origin).1 =
      6 + OpenTheory.StorageSize.theoremData result + OpenTheory.StorageSize.theoremData first +
        OpenTheory.StorageSize.theoremData second + StorageSize.origin origin := by
  rw [StorageSize.primitive_payload]
  simp only [StorageSize.receiptPayload, StorageSize.request, StorageSize.inferenceRequest,
    RuleRequest.premises, InferenceRequest.premises, List.length_cons, List.length_nil]
  omega

end Mettapedia.Languages.HOLLight.StorageSize
