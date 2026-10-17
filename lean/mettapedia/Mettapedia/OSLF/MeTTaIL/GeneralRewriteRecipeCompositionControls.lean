import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeControls
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeCompositionWire
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeContext
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeParallel
import Mettapedia.GSLT.LanguageDef.GSLTILAuthoredFibre

/-!
# Composable authored rewrite-recipe controls

Actual authored recipes exercise typed context transport, independent residual
squares, chronological sharing, equation-respecting paths and the native command
fibre. Each fixture retains its original language snapshot. Construction failure
is a failed gate, never a replacement by an unrelated accepted request.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeCompositionControls

namespace Composed
open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralExecutionAdmission GeneralTypedSites GeneralRewriteRecipeComposition GeneralRewriteRecipeCompositionWire
open Mettapedia.OSLF.Binding.WireCodec

abbrev A := GeneralRewriteRecipeControls.a
abbrev B := GeneralRewriteRecipeControls.b
abbrev C := GeneralRewriteRecipeControls.c
abbrev D := GeneralRewriteRecipeControls.d

def snapshot : Snapshot :=
  { GeneralRewriteRecipeControls.snapshot with language :=
    { GeneralRewriteRecipeControls.language with rewrites := GeneralRewriteRecipeControls.language.rewrites ++
      [{ name := "c-b", typeContext := [], premises := [], left := C, right := B }] } }
def permissions : Permissions := GeneralRewriteRecipeControls.permissions
def plan : Plan := compile snapshot permissions

def header (source target : Pattern) : Header :=
  ⟨snapshot, permissions, [], GeneralRewriteRecipeControls.type, source, target⟩

def backRecipe : Option GeneralRewriteRecipe.StepTrace := do
  let declaration ← plan.rules[2]?
  let fire : GeneralRuleJobs.Receipt :=
    { job := ⟨2, declaration, .here [] GeneralRewriteRecipeControls.type C⟩
      matcherTrace := [], captured := [], completed := [], premiseHistory := [], localTarget := B, target := B }
  pure ⟨⟨C, [], fire⟩, []⟩

def traceFixture : Option TraceRequest := do
  let direct ← GeneralRewriteRecipeControls.directFixture
  let back ← backRecipe
  pure ⟨header B B, [⟨C, direct.step⟩, ⟨B, back⟩]⟩

def semanticFixture : Option SemanticRequest := do
  let direct ← GeneralRewriteRecipeControls.directFixture
  let pre ← GeneralRewriteRecipeControls.equation 0 A B
  let post ← GeneralRewriteRecipeControls.equation 1 C D
  pure ⟨header A D, ⟨B, C, [.forward pre], [⟨C, direct.step⟩], [.forward post]⟩⟩

def equationOnly : Option SemanticRequest := do
  let pre ← GeneralRewriteRecipeControls.equation 0 A B
  pure ⟨header A B, ⟨B, B, [.forward pre], [], []⟩⟩

def appendFixture : Option SemanticRequest := do
  let direct ← GeneralRewriteRecipeControls.directFixture
  let pre ← GeneralRewriteRecipeControls.equation 0 A B
  let back ← backRecipe
  let front : SemanticTrace := ⟨B, C, [.forward pre], [⟨C, direct.step⟩], []⟩
  let later : SemanticTrace := ⟨C, B, [], [⟨B, back⟩], []⟩
  pure ⟨header A B, SemanticTrace.append front later⟩

def traceRoundtrip (request : TraceRequest) : Bool :=
  match decodeTraceRequest (encodeTraceRequest request) with
  | none => false
  | some result => decide (traceRequestCodec.put result = traceRequestCodec.put request)
def semanticRoundtrip (request : SemanticRequest) : Bool :=
  match decodeSemanticRequest (encodeSemanticRequest request) with
  | none => false
  | some result => decide (semanticRequestCodec.put result = semanticRequestCodec.put request)
def traceAccepted (request : TraceRequest) : Bool := checkTraceWord (encodeTraceRequest request)
def semanticAccepted (request : SemanticRequest) : Bool := checkSemanticWord (encodeSemanticRequest request)

def traceControls (request : TraceRequest) : List (String × Bool) :=
  let word := encodeTraceRequest request
  let empty : TraceRequest := ⟨request.header, []⟩
  let badSource := { request with header := { request.header with source := C } }
  let badTarget := { request with header := { request.header with target := D } }
  let badContext := { request with header := { request.header with bound := [GeneralRewriteRecipeControls.type] } }
  let badType := { request with header := { request.header with type := .base "Undeclared" } }
  let wrongJoin := { request with trace := request.trace.map fun link => { link with next := D } }
  [
    ("two-primitive-composed-trace", traceAccepted request),
    ("two-physical-links-retained", decide (request.trace.length = 2)),
    ("trace-literal-fields-roundtrip", traceRoundtrip request),
    ("same-endpoint-empty-trace", traceAccepted empty),
    ("nonempty-proof-distinct-from-reflexivity", decide (word ≠ encodeTraceRequest empty)),
    ("bad-join-refused", !traceAccepted wrongJoin),
    ("bad-source-refused", !traceAccepted badSource),
    ("bad-target-refused", !traceAccepted badTarget),
    ("bad-context-refused", !traceAccepted badContext),
    ("bad-type-refused", !traceAccepted badType),
    ("reverse-step-order-refused", !traceAccepted { request with trace := request.trace.reverse }),
    ("missing-last-link-refused", !traceAccepted { request with trace := request.trace.take 1 }),
    ("revoked-permission-refused", !traceAccepted { request with header :=
      { request.header with permissions := { request.header.permissions with ruleIndices := some [] } } }),
    ("stale-source-header-refused", !traceAccepted { request with header :=
      { request.header with snapshot := { snapshot with language :=
        { snapshot.language with rewrites := snapshot.language.rewrites.reverse } } } }),
    ("trace-empty-byteword-refused", (decodeTraceRequest []).isNone),
    ("trace-bare-data-refused", (decodeTraceRequest (Binary.encodeData (.atom 0))).isNone),
    ("trace-truncated-refused", (decodeTraceRequest (word.take (word.length - 1))).isNone),
    ("trace-trailing-refused", (decodeTraceRequest (word ++ [0])).isNone),
    ("trace-doubled-word-refused", (decodeTraceRequest (word ++ word)).isNone),
    ("trace-scalar-alias-refused", (decodeTraceRequest (GeneralRewriteRecipeControls.scalarAlias word)).isNone),
    ("trace-not-semantic-protocol", (decodeSemanticRequest word).isNone),
    ("trace-not-atomic-protocol", (GeneralRewriteRecipeWire.decodeRequest word).isNone) ]

def semanticControls (request : SemanticRequest) : List (String × Bool) :=
  let word := encodeSemanticRequest request
  [
    ("semantic-endpoint-equations", semanticAccepted request),
    ("semantic-fields-roundtrip", semanticRoundtrip request),
    ("semantic-bad-source", !semanticAccepted { request with header := { request.header with source := D } }),
    ("semantic-bad-target", !semanticAccepted { request with header := { request.header with target := A } }),
    ("semantic-missing-prefix", !semanticAccepted { request with evidence := { request.evidence with before := [] } }),
    ("semantic-missing-suffix", !semanticAccepted { request with evidence := { request.evidence with after := [] } }),
    ("semantic-bad-start-representative", !semanticAccepted { request with evidence := { request.evidence with startRepresentative := A } }),
    ("semantic-bad-end-representative", !semanticAccepted { request with evidence := { request.evidence with endRepresentative := D } }),
    ("semantic-bad-join", !semanticAccepted { request with evidence := { request.evidence with trace := request.evidence.trace.map fun link => { link with next := D } } }),
    ("semantic-revoked-equations", !semanticAccepted { request with header :=
      { request.header with permissions := { request.header.permissions with equationIndices := some [] } } }),
    ("semantic-empty-byteword", (decodeSemanticRequest []).isNone),
    ("semantic-bare-data", (decodeSemanticRequest (Binary.encodeData (.atom 0))).isNone),
    ("semantic-truncated", (decodeSemanticRequest (word.take (word.length - 1))).isNone),
    ("semantic-trailing", (decodeSemanticRequest (word ++ [0])).isNone),
    ("semantic-scalar-alias", (decodeSemanticRequest (GeneralRewriteRecipeControls.scalarAlias word)).isNone),
    ("semantic-not-literal-trace", (decodeTraceRequest word).isNone),
    ("semantic-not-atomic", (GeneralRewriteRecipeWire.decodeRequest word).isNone) ]



end Composed

namespace DAG
open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralExecutionAdmission GeneralRewriteRecipeDAG GeneralRewriteRecipeCompositionWire
open Mettapedia.OSLF.Binding.WireCodec
open Composed

def sharedFixture : Option DAGRequest := do
  let direct ← GeneralRewriteRecipeControls.directFixture
  let back ← backRecipe
  pure ⟨header B B, ⟨[
    .atomic B C direct.step,
    .atomic C B back,
    .trans B C B 0 1,
    .trans B B B 2 2,
    .trans B B B 3 3], 4⟩⟩

def conversionFixture : Option DAGRequest := do
  let direct ← GeneralRewriteRecipeControls.directFixture
  let post ← GeneralRewriteRecipeControls.equation 1 C D
  pure ⟨header B C, ⟨[
    .atomic B C direct.step,
    .conversion C D [.forward post],
    .trans B C D 0 1,
    .conversion D C [.reverse post],
    .trans B D C 2 3], 4⟩⟩

def accepted (request : DAGRequest) : Bool := checkDAGWord (encodeDAGRequest request)
def roundtrip (request : DAGRequest) : Bool :=
  match decodeDAGRequest (encodeDAGRequest request) with
  | none => false
  | some result => decide (dagRequestCodec.put result = dagRequestCodec.put request)
def expansionCount (request : DAGRequest) (count : Nat) : Bool :=
  match Graph.expand? (compile request.header.snapshot request.header.permissions)
      request.header.bound request.header.type request.graph (request.header.source, request.header.target) with
  | none => false
  | some result => decide (result.recipes.length = count ∧ result.receipt.trace.length = count)
def expansionAccepted (request : DAGRequest) : Bool :=
  match Graph.expand? (compile request.header.snapshot request.header.permissions)
      request.header.bound request.header.type request.graph (request.header.source, request.header.target) with
  | none => false
  | some result => checkSemanticRequest ⟨request.header, result.receipt⟩

def graphControls (request : DAGRequest) : List (String × Bool) :=
  let word := encodeDAGRequest request
  let earlier := { request with graph := { request.graph with root := 2 } }
  let invalidUnused := { request with graph := { request.graph with nodes :=
    request.graph.nodes ++ [.trans B B B 99 99] } }
  let forgedRows := (request.graph.nodes.take 1).map (fun node => match node with
    | .atomic _ _ recipe => .atomic D D recipe
    | other => other)
  let invalidAtomic := { request with graph := { request.graph with nodes :=
    request.graph.nodes ++ forgedRows } }
  let wrongJoin := { request with graph := { request.graph with nodes :=
    (request.graph.nodes.take 2 ++ [.trans B D B 0 1] ++ request.graph.nodes.drop 3) } }
  [
    ("dag-shared-eight-use-cycle", accepted request),
    ("dag-literal-fields-roundtrip", roundtrip request),
    ("dag-five-stored-nodes", decide (request.graph.nodes.length = 5)),
    ("dag-expanded-eight-recipe-uses", expansionCount request 8),
    ("dag-expansion-rechecks-original-semantic-trace", expansionAccepted request),
    ("dag-distinct-earlier-root-accepted", accepted earlier),
    ("dag-distinct-earlier-root-two-uses", expansionCount earlier 2),
    ("dag-distinct-root-distinct-article", decide (word ≠ encodeDAGRequest earlier)),
    ("dag-unused-bad-reference-row-refused", !accepted invalidUnused),
    ("dag-unused-bad-atomic-row-refused", !accepted invalidAtomic),
    ("dag-forward-reference-refused", !accepted ⟨request.header, ⟨[.trans B B B 0 0], 0⟩⟩),
    ("dag-empty-graph-refused", !accepted ⟨request.header, ⟨[], 0⟩⟩),
    ("dag-absent-root-refused", !accepted { request with graph := { request.graph with root := 99 } }),
    ("dag-wrong-root-claim-refused", !accepted { request with graph := { request.graph with root := 0 } }),
    ("dag-wrong-join-refused", !accepted wrongJoin),
    ("dag-bad-source-refused", !accepted { request with header := { request.header with source := C } }),
    ("dag-bad-target-refused", !accepted { request with header := { request.header with target := D } }),
    ("dag-bad-context-refused", !accepted { request with header :=
      { request.header with bound := [GeneralRewriteRecipeControls.type] } }),
    ("dag-bad-sort-refused", !accepted { request with header := { request.header with type := .base "Undeclared" } }),
    ("dag-revoked-rule-refused", !accepted { request with header :=
      { request.header with permissions := { request.header.permissions with ruleIndices := some [] } } }),
    ("dag-stale-rule-order-refused", !accepted { request with header :=
      { request.header with snapshot := { snapshot with language :=
        { snapshot.language with rewrites := snapshot.language.rewrites.reverse } } } }),
    ("dag-empty-word-refused", (decodeDAGRequest []).isNone),
    ("dag-bare-data-refused", (decodeDAGRequest (Binary.encodeData (.atom 0))).isNone),
    ("dag-truncated-word-refused", (decodeDAGRequest (word.take (word.length - 1))).isNone),
    ("dag-trailing-word-refused", (decodeDAGRequest (word ++ [0])).isNone),
    ("dag-doubled-word-refused", (decodeDAGRequest (word ++ word)).isNone),
    ("dag-noncanonical-scalar-refused", (decodeDAGRequest (GeneralRewriteRecipeControls.scalarAlias word)).isNone),
    ("dag-not-trace-protocol", (decodeTraceRequest word).isNone),
    ("dag-not-semantic-protocol", (decodeSemanticRequest word).isNone),
    ("dag-not-atomic-protocol", (GeneralRewriteRecipeWire.decodeRequest word).isNone),
    ("dag-unknown-node-tag-refused", (dagNodeCodec.get (.pair (.atom 4) (.atom 0))).isNone),
    ("dag-missing-node-fields-refused", (dagNodeCodec.get (.pair (.atom 3) (.atom 0))).isNone),
    ("dag-bare-node-refused", (dagNodeCodec.get (.atom 0)).isNone),
    ("dag-bare-graph-refused", (graphCodec.get (.atom 0)).isNone),
    ("dag-bare-request-refused", (dagRequestCodec.get (.atom 0)).isNone) ]

def legacyExtras (trace : TraceRequest) (semantic : SemanticRequest) (eqOnly appended : SemanticRequest)
    (atomic : GeneralRewriteRecipeWire.Request) : List (String × Bool) :=
  let unknown : Pattern := .apply "UNDECLARED" []
  let raw : TraceRequest := ⟨header unknown unknown, []⟩
  [
    ("equation-only-zero-firing-path", semanticAccepted eqOnly),
    ("equation-only-firing-count-zero", decide (eqOnly.evidence.trace.length = 0)),
    ("equation-only-endpoints-differ", decide (eqOnly.header.source ≠ eqOnly.header.target)),
    ("literal-empty-trace-cannot-change-endpoint", !traceAccepted ⟨eqOnly.header, []⟩),
    ("semantic-actual-append", semanticAccepted appended),
    ("semantic-append-retains-two-firings", decide (appended.evidence.trace.length = 2)),
    ("semantic-append-roundtrip", semanticRoundtrip appended),
    ("raw-reflexivity-accepted", traceAccepted raw),
    ("raw-reflexivity-not-typing", !(Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
      raw.header.snapshot.language raw.header.snapshot.free raw.header.bound raw.header.type unknown)),
    ("atomic-not-trace-protocol", (decodeTraceRequest (GeneralRewriteRecipeWire.encodeRequest atomic)).isNone),
    ("atomic-not-semantic-protocol", (decodeSemanticRequest (GeneralRewriteRecipeWire.encodeRequest atomic)).isNone),
    ("trace-not-dag-protocol", (decodeDAGRequest (encodeTraceRequest trace)).isNone),
    ("semantic-not-dag-protocol", (decodeDAGRequest (encodeSemanticRequest semantic)).isNone),
    ("atomic-not-dag-protocol", (decodeDAGRequest (GeneralRewriteRecipeWire.encodeRequest atomic)).isNone) ]



end DAG

namespace Context
open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralTypedSites
open GeneralRewriteRecipe
open Mettapedia.GSLT.LanguageDef

def sameRule (first second : GeneralRuleJobs.Receipt) : Bool :=
  decide (GeneralPremiseReceiptWire.receiptCodec.put first =
    GeneralPremiseReceiptWire.receiptCodec.put second)

def sameEquation (first second : GeneralEquationJobs.Receipt) : Bool :=
  decide (GeneralRewriteRecipeWire.equationReceiptCodec.put first =
    GeneralRewriteRecipeWire.equationReceiptCodec.put second)

def ruleFinishAgrees (bound : List TypeExpr) (expected : TypeExpr)
    (receipt : GeneralRuleJobs.Receipt) : Bool :=
  (GeneralRuleJobs.finish? GeneralRewriteRecipeControls.Arithmetic.plan bound expected receipt.job receipt.matcherTrace
    receipt.captured receipt.completed receipt.premiseHistory).any fun result =>
      sameRule result receipt

def equationFinishAgrees (bound : List TypeExpr) (expected : TypeExpr)
    (receipt : GeneralEquationJobs.Receipt) : Bool :=
  (GeneralEquationJobs.finish GeneralRewriteRecipeControls.plan bound expected receipt.job receipt.matcherTrace
    receipt.captured receipt.completed receipt.premiseHistory).any fun result =>
      sameEquation result receipt

def checks? : Option (List (String × Bool)) := do
  let localSource := GeneralRewriteRecipeControls.Arithmetic.add GeneralRewriteRecipeControls.Arithmetic.zero (.bvar 0)
  let localReceipt ← expand GeneralRewriteRecipeControls.Arithmetic.plan [GeneralRewriteRecipeControls.Arithmetic.nat] GeneralRewriteRecipeControls.Arithmetic.nat localSource GeneralRewriteRecipeControls.Arithmetic.root
  let binder := SiteData.wrapLambda none GeneralRewriteRecipeControls.Arithmetic.nat (SiteData.here [GeneralRewriteRecipeControls.Arithmetic.nat] GeneralRewriteRecipeControls.Arithmetic.nat localSource)
  let enclosed := localReceipt.inContext binder
  let originalEnclosed ← expand GeneralRewriteRecipeControls.Arithmetic.plan [] (.arrow GeneralRewriteRecipeControls.Arithmetic.nat GeneralRewriteRecipeControls.Arithmetic.nat)
    (.lambda none localSource) GeneralRewriteRecipeControls.Arithmetic.insideBinder
  let middle := SiteData.wrapApplication 1 "S" [localSource] 0
    (SiteData.here [GeneralRewriteRecipeControls.Arithmetic.nat] GeneralRewriteRecipeControls.Arithmetic.nat localSource)
  let outside := SiteData.wrapLambda none GeneralRewriteRecipeControls.Arithmetic.nat
    (SiteData.here [GeneralRewriteRecipeControls.Arithmetic.nat] GeneralRewriteRecipeControls.Arithmetic.nat (GeneralRewriteRecipeControls.Arithmetic.successor localSource))
  let twice := (localReceipt.inContext middle).inContext outside
  let once := localReceipt.inContext (outside.compose middle)
  let pairLocal ← expand GeneralRewriteRecipeControls.Arithmetic.plan [] GeneralRewriteRecipeControls.Arithmetic.nat (GeneralRewriteRecipeControls.Arithmetic.add GeneralRewriteRecipeControls.Arithmetic.zero GeneralRewriteRecipeControls.Arithmetic.zero) GeneralRewriteRecipeControls.Arithmetic.root
  let leftOriginal ← expand GeneralRewriteRecipeControls.Arithmetic.plan [] GeneralRewriteRecipeControls.Arithmetic.nat GeneralRewriteRecipeControls.Arithmetic.pairSource GeneralRewriteRecipeControls.Arithmetic.leftPair
  let rightOriginal ← expand GeneralRewriteRecipeControls.Arithmetic.plan [] GeneralRewriteRecipeControls.Arithmetic.nat GeneralRewriteRecipeControls.Arithmetic.pairSource GeneralRewriteRecipeControls.Arithmetic.rightPair
  let left := pairLocal.inContext leftOriginal.job.site
  let right := pairLocal.inContext rightOriginal.job.site
  let equation ← GeneralRewriteRecipeControls.equation 0 GeneralRewriteRecipeControls.a GeneralRewriteRecipeControls.b
  let localEquation := {equation with job :=
    {equation.job with site := SiteData.here [GeneralRewriteRecipeControls.type] GeneralRewriteRecipeControls.type GeneralRewriteRecipeControls.a}}
  let equationOutside := SiteData.wrapLambda none GeneralRewriteRecipeControls.type
    (SiteData.here [GeneralRewriteRecipeControls.type] GeneralRewriteRecipeControls.type GeneralRewriteRecipeControls.a)
  let enclosedEquation := localEquation.inContext equationOutside
  pure [
    ("original open local firing", checkFiring GeneralRewriteRecipeControls.Arithmetic.plan [GeneralRewriteRecipeControls.Arithmetic.nat] GeneralRewriteRecipeControls.Arithmetic.nat localSource localReceipt),
    ("actual under-binder receipt checks", checkFiring GeneralRewriteRecipeControls.Arithmetic.plan [] (.arrow GeneralRewriteRecipeControls.Arithmetic.nat GeneralRewriteRecipeControls.Arithmetic.nat)
      (.lambda none localSource) enclosed),
    ("under-binder target preserves bound variable", enclosed.target == .lambda none (.bvar 0)),
    ("under-binder receipt agrees with original site expansion", sameRule enclosed originalEnclosed),
    ("under-binder original completion emits exact lifted fields", ruleFinishAgrees [] (.arrow GeneralRewriteRecipeControls.Arithmetic.nat GeneralRewriteRecipeControls.Arithmetic.nat) enclosed),
    ("nested context lift checks", checkFiring GeneralRewriteRecipeControls.Arithmetic.plan [] (.arrow GeneralRewriteRecipeControls.Arithmetic.nat GeneralRewriteRecipeControls.Arithmetic.nat)
      (.lambda none (GeneralRewriteRecipeControls.Arithmetic.successor localSource)) twice),
    ("nested context composition literal receipt equality", sameRule twice once),
    ("nested context concatenated physical address", twice.job.site.address == [0,0]),
    ("left independent typed context checks", checkFiring GeneralRewriteRecipeControls.Arithmetic.plan [] GeneralRewriteRecipeControls.Arithmetic.nat GeneralRewriteRecipeControls.Arithmetic.pairSource left),
    ("right independent typed context checks", checkFiring GeneralRewriteRecipeControls.Arithmetic.plan [] GeneralRewriteRecipeControls.Arithmetic.nat GeneralRewriteRecipeControls.Arithmetic.pairSource right),
    ("left lift equals original site receipt", sameRule left leftOriginal),
    ("right lift equals original site receipt", sameRule right rightOriginal),
    ("unchanged local evidence survives enclosure", decide (left.captured = pairLocal.captured ∧
      left.completed = pairLocal.completed ∧ left.matcherTrace = pairLocal.matcherTrace ∧
      left.premiseHistory = pairLocal.premiseHistory)),
    ("wrong ambient context refused", !checkFiring GeneralRewriteRecipeControls.Arithmetic.plan [GeneralRewriteRecipeControls.Arithmetic.nat] (.arrow GeneralRewriteRecipeControls.Arithmetic.nat GeneralRewriteRecipeControls.Arithmetic.nat)
      (.lambda none localSource) enclosed),
    ("wrong enclosing source refused", !checkFiring GeneralRewriteRecipeControls.Arithmetic.plan [] GeneralRewriteRecipeControls.Arithmetic.nat
      (GeneralRewriteRecipeControls.Arithmetic.pair GeneralRewriteRecipeControls.Arithmetic.zero (GeneralRewriteRecipeControls.Arithmetic.add GeneralRewriteRecipeControls.Arithmetic.zero GeneralRewriteRecipeControls.Arithmetic.zero)) left),
    ("forged local bound context refused", !checkFiring GeneralRewriteRecipeControls.Arithmetic.plan [] (.arrow GeneralRewriteRecipeControls.Arithmetic.nat GeneralRewriteRecipeControls.Arithmetic.nat)
      (.lambda none localSource) {enclosed with job := {enclosed.job with site :=
        {enclosed.job.site with focusBound := []}}}),
    ("actual local equation below a binder", checkEquation GeneralRewriteRecipeControls.plan [GeneralRewriteRecipeControls.type] GeneralRewriteRecipeControls.type GeneralRewriteRecipeControls.a localEquation),
    ("actual equation context lift checks", checkEquation GeneralRewriteRecipeControls.plan [] (.arrow GeneralRewriteRecipeControls.type GeneralRewriteRecipeControls.type)
      (.lambda none GeneralRewriteRecipeControls.a) enclosedEquation),
    ("equation context target", enclosedEquation.target == .lambda none GeneralRewriteRecipeControls.b),
    ("original equation completion emits exact lifted fields", equationFinishAgrees []
      (.arrow GeneralRewriteRecipeControls.type GeneralRewriteRecipeControls.type) enclosedEquation),
    ("equation evidence retained literally", decide (enclosedEquation.captured = localEquation.captured ∧
      enclosedEquation.completed = localEquation.completed ∧
      enclosedEquation.matcherTrace = localEquation.matcherTrace ∧
      enclosedEquation.premiseHistory = localEquation.premiseHistory ∧
      enclosedEquation.rawReduct = localEquation.rawReduct)),
    ("equation wrong enclosing source refused", !checkEquation GeneralRewriteRecipeControls.plan [] (.arrow GeneralRewriteRecipeControls.type GeneralRewriteRecipeControls.type)
      (.lambda none GeneralRewriteRecipeControls.c) enclosedEquation),
    ("equation invented target refused", !checkEquation GeneralRewriteRecipeControls.plan [] (.arrow GeneralRewriteRecipeControls.type GeneralRewriteRecipeControls.type)
      (.lambda none GeneralRewriteRecipeControls.a) {enclosedEquation with target := .lambda none GeneralRewriteRecipeControls.d})]


end Context

namespace Parallel
open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission GeneralTypedSites
open GeneralRewriteRecipe GeneralRewriteRecipeParallel

open GeneralRewriteRecipe

open Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeControls.Arithmetic

def pairSource : Pattern := pair (add zero zero) (add zero zero)
def pairTarget : Pattern := pair zero zero

def independentSquare? : Option Square := do
  let first ← expand plan [] nat pairSource leftPair
  let second ← expand plan [] nat first.target rightPair
  let otherFirst ← expand plan [] nat pairSource rightPair
  let otherSecond ← expand plan [] nat otherFirst.target leftPair
  pure ⟨first,second,otherFirst,otherSecond⟩

def overlapSource : Pattern := pair (add zero (add zero zero)) zero

def overlapSquare? : Option Square := do
  let first ← expand plan [] nat overlapSource leftPair
  let second ← expand plan [] nat first.target leftPair
  pure ⟨first,second,first,second⟩

def allEdges (source : Pattern) (square : Square) : Bool :=
  checkFiring plan [] nat source square.first &&
  checkFiring plan [] nat square.first.target square.second &&
  checkFiring plan [] nat source square.otherFirst &&
  checkFiring plan [] nat square.otherFirst.target square.otherSecond

def checks? : Option (List (String × Bool)) := do
  let positive ← independentSquare?
  let overlapping ← overlapSquare?
  pure [
    ("four independent residual edges checked",allEdges pairSource positive),
    ("literal independent square admitted",positive.check plan [] nat pairSource),
    ("actual independence tile constructed",(positive.checkedTile plan [] nat pairSource).isSome),
    ("independent square literal endpoint",positive.second.target == pairTarget),
    ("equal-valued redexes keep distinct addresses",positive.first.job.site.address != positive.otherFirst.job.site.address),
    ("wrong residual source refuses",!({positive with second := positive.first}).check plan [] nat pairSource),
    ("wrong closing endpoint refuses",!({positive with otherSecond := {positive.otherSecond with target := pairSource}}).check plan [] nat pairSource),
    ("wrong residual site identity refuses",!({positive with otherSecond := positive.second}).check plan [] nat pairSource),
    ("overlap has four independently valid edges",allEdges overlapSource overlapping),
    ("overlapping site square refused",!(overlapping.check plan [] nat overlapSource)),
    ("overlapping tile unavailable",(overlapping.checkedTile plan [] nat overlapSource).isNone),
    ("ancestor addresses not independent",!(decide (AddressIndependent [0] [0,1]))),
    ("sibling addresses independent",decide (AddressIndependent [0] [1]))]


end Parallel

namespace Command
open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.GSLTIL

def stage : Pattern := .apply "authored-stage" []
def unknown : Pattern := .apply "unknown-stage" []
def kind : Pattern := .apply "route-kind" []
def route : Pattern := .apply "route-name" []
def destination : Pattern := .apply "destination-stage" []

def checks? : Option (List (String × Bool)) := do
  let packet ← Composed.traceFixture
  let plan := compile packet.header.snapshot packet.header.permissions
  let type := packet.header.type
  let first := packet.header.source
  let last := packet.header.target
  let configured := AuthoredFibre.checking stage plan [] type
  let atEntries := AuthoredFibre.atJournal stage plan [] type packet.trace
  let underneath := AuthoredFibre.underneathJournal stage plan [] type packet.trace
  pure [
    ("authored fibre actual two-rewrite journal", NativeKernel.check configured (.at stage first) (.at stage last) atEntries),
    ("authored fibre underneath pending route", NativeKernel.check configured
      (.via kind route stage destination first) (.via kind route stage destination last) underneath),
    ("authored fibre rejects unknown stage", !NativeKernel.check configured (.at unknown first) (.at unknown last) atEntries),
    ("authored fibre rejects unknown underlying stage", !NativeKernel.check configured
      (.via kind route unknown destination first) (.via kind route unknown destination last) underneath),
    ("authored fibre at entry rejects underneath mode", !NativeKernel.check configured
      (.via kind route stage destination first) (.via kind route stage destination last) atEntries),
    ("authored fibre underneath entry rejects at mode", !NativeKernel.check configured (.at stage first) (.at stage last) underneath),
    ("authored fibre does not manufacture transport", !NativeKernel.check configured
      (.via kind route stage destination first) (.at destination last) underneath),
    ("authored fibre retains pending route identity", !NativeKernel.check configured
      (.via kind route stage destination first) (.via kind unknown stage destination last) underneath),
    ("authored fibre wrong goal refused", !NativeKernel.check configured (.at stage first) (.at stage GeneralRewriteRecipeControls.d) atEntries),
    ("authored fibre stage cannot change", !NativeKernel.check configured (.at stage first) (.at unknown last) atEntries),
    ("authored fibre empty journal is reflexive", NativeKernel.check configured (.at stage first) (.at stage first) []),
    ("authored fibre empty journal adds no equation", !NativeKernel.check configured
      (.at stage GeneralRewriteRecipeControls.a) (.at stage GeneralRewriteRecipeControls.b) [])]

end Command


namespace Plans
open Mettapedia.OSLF.MeTTaIL
open GeneralRewriteRecipeComposition
open GeneralRewriteRecipeControls.Arithmetic

def producesPair : RecipePlan.Result → Bool
  | .verified target trace => target == pairTarget &&
      decide (trace.length = 2) && Trace.check plan [] nat pairSource pairTarget trace
  | _ => false

def checks : List (String × Bool) := [
  ("recipe plan computes both intermediate states", producesPair
    (RecipePlan.run plan [] nat pairSource [some leftPair, some rightPair])),
  ("recipe plan open choice stays pending", match RecipePlan.run plan [] nat pairSource
    [some leftPair, none] with | .pending => true | _ => false),
  ("recipe plan invalid complete choice refuses", match RecipePlan.run plan [] nat pairSource
    [some root] with | .refused => true | _ => false),
  ("recipe plan empty run is reflexive", match RecipePlan.run plan [] nat pairSource [] with
    | .verified target trace => target == pairSource && trace.isEmpty | _ => false),
  ("recipe plan unused matching guidance refuses", match RecipePlan.run plan [] nat pairSource
    [some {leftPair with matching := [{path := [], selected := 0}]}] with
    | .refused => true | _ => false)]
end Plans

def checks? : Option (List (String × Bool)) := do
  let trace ← Composed.traceFixture
  let semantic ← Composed.semanticFixture
  let eqOnly ← Composed.equationOnly
  let appended ← Composed.appendFixture
  let atomic ← GeneralRewriteRecipeControls.fixture
  let shared ← DAG.sharedFixture
  let conversion ← DAG.conversionFixture
  let context ← Context.checks?
  let parallel ← Parallel.checks?
  let command ← Command.checks?
  let unknown : Syntax.Pattern := .apply "UNDECLARED" []
  let raw : GeneralRewriteRecipeCompositionWire.DAGRequest :=
    ⟨Composed.header unknown unknown, ⟨[.refl unknown], 0⟩⟩
  pure (GeneralRewriteRecipeControls.checks ++
    Composed.traceControls trace ++ Composed.semanticControls semantic ++
    DAG.legacyExtras trace semantic eqOnly appended atomic ++ DAG.graphControls shared ++ [
    ("dag-explicit-equation-detour", DAG.accepted conversion),
    ("dag-equation-detour-all-node-fields-roundtrip", DAG.roundtrip conversion),
    ("dag-equation-detour-one-original-firing", DAG.expansionCount conversion 1),
    ("dag-equation-detour-expansion-accepted", DAG.expansionAccepted conversion),
    ("dag-equation-authority-revoked", !DAG.accepted {conversion with header :=
      {conversion.header with permissions := {conversion.header.permissions with equationIndices := some []}}}),
    ("dag-raw-reflexivity-accepted", DAG.accepted raw),
    ("dag-raw-reflexivity-not-typing", !(Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
      raw.header.snapshot.language raw.header.snapshot.free raw.header.bound raw.header.type unknown))] ++
    context ++ parallel ++ command ++ Plans.checks)

#guard checks?.any (List.all · Prod.snd)

end Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeCompositionControls
