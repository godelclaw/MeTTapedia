import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionOccurrence
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceDiscoveryExecution
import Mettapedia.GSLT.LanguageDef.CollectionOccurrenceMachineControls
import Mettapedia.GSLT.LanguageDef.CollectionInputGuardControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution
import Mettapedia.GSLT.LanguageDef.CollectionNestedBatchControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution
import Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionHandoffExecution
import Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentationControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionStateExecution
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContextExecution
import Mettapedia.OSLF.MeTTaIL.CollectionContextVariantsControls
import Mettapedia.GSLT.LanguageDef.CollectionConsumerControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionLoggedSearchExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RootCollection
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentCodec
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSharedOutputControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionExecutionQualification

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Machines.ResumableSearchRunner (Machine Search)

namespace CollectionRunnerControls

mutual
  def collectionNestingDepth : Pattern → Nat
    | .bvar _ | .fvar _ => 0
    | .apply _ arguments => collectionListDepth arguments
    | .lambda _ body | .multiLambda _ _ body => collectionNestingDepth body
    | .subst body value => max (collectionNestingDepth body) (collectionNestingDepth value)
    | .collection _ elements _ => 1 + collectionListDepth elements
  def collectionListDepth : List Pattern → Nat
    | [] => 0
    | first :: rest => max (collectionNestingDepth first) (collectionListDepth rest)
end

def measurement (label : String) (source : Pattern)
    (work first frames publications providerRows : Nat) : String :=
  "; GSLT-MEASUREMENT " ++ (Lean.Json.mkObj
    [("label", .str label), ("collection_nesting_depth", Lean.toJson (collectionNestingDepth source)),
     ("work_budget", Lean.toJson work), ("resume_first_budget", Lean.toJson first),
     ("resume_extra_budget", Lean.toJson (work - first)),
     ("retained_allocation_frames", Lean.toJson frames),
     ("publications", Lean.toJson publications), ("provider_rows", Lean.toJson providerRows)]).compress ++ "\n"

def searchControl {Run Receipt : Type} (label : String) (plan : GeneralExecutionAdmission.Plan)
    (expected : TypeExpr) (source : Pattern) (work : Nat)
    (search : Search Pattern Run Receipt) (backend : Term)
    (encodeRun : Run → Term) (encodeReceipt : Receipt → Term) : String :=
  let source := CanonicalBags.canon source
  let names := StandardWire.planTable plan []
  let standard := Term.application "Canonical"
    [.symbol "LNil", .symbol "LNil", encodeList Term.string names]
  let planWire := CompletePlanWire.planTerm plan plan.snapshot.freeTypes [] expected
  let begun := Machine.begin search source
  let machine := Machine.advance search 2 work begun
  let middle := Machine.advance search 1 work begun
  let explorer := Complete.Settled.roundsUntilSettled search work
    (Complete.Explore.begin search source)
  let machineTerm := CompleteExecution.SearchWire.machineTerm encodeRun encodeReceipt
  let explorerTerm := CompleteExecution.SearchWire.explorerTerm encodeRun encodeReceipt
  let edges := encodeList (CompleteExecution.SearchWire.edgeTerm encodeReceipt)
    (Complete.Graph.edges search explorer)
  "!(let* (($plan (quote " ++ planWire.render ++ "))\n" ++
  "        ($backend (quote " ++ backend.render ++ "))\n" ++
  "        ($standard (quote " ++ standard.render ++ "))\n" ++
  "        ($source (quote " ++ (Term.render (InferenceCettaWire.encodePattern source)) ++ "))\n" ++
  "        ($begin (gslt:runner:begin $backend $plan $standard $source))\n" ++
  "        ($machine (gslt:runner:advance $backend $plan $standard 2 " ++ toString work ++ " $begin))\n" ++
  "        ($middle (gslt:runner:advance $backend $plan $standard 1 " ++ toString work ++ " $begin))\n" ++
  "        ($resumed (gslt:runner:advance $backend $plan $standard 1 " ++ toString work ++ " $middle))\n" ++
  "        ($trace (gslt:runner:trace $machine))\n" ++
  "        ($initial (gslt:explore:begin $backend $plan $standard $source))\n" ++
  "        ($explorer (gslt:explore:rounds $backend $plan $standard " ++ toString work ++ " $initial))\n" ++
  "        ($states (gslt:explore:states $explorer))\n" ++
  "        ($edges (gslt:explore:edges $backend $standard $explorer)))\n" ++
  "  (println! (CollectionRunnerControl " ++ reprStr label ++
    " (== $begin (quote " ++ (machineTerm begun).render ++ "))" ++
    " (== $machine (quote " ++ (machineTerm machine).render ++ "))" ++
    " (== $middle (quote " ++ (machineTerm middle).render ++ "))" ++
    " (== $resumed $machine)" ++
    " (== $trace (quote " ++ (CompleteExecution.SearchWire.traceTerm machine).render ++ "))" ++
    " (== $explorer (quote " ++ (explorerTerm explorer).render ++ "))" ++
    " (== $states (quote " ++ (encodeList InferenceCettaWire.encodePattern
      (explorer.nodes.map (·.state))).render ++ "))" ++
    " (== $edges (quote " ++ edges.render ++ ")))))"

def rootControl (label : String) (plan : GeneralExecutionAdmission.Plan)
    (profile : CollectionRootSearch.Profile plan) (expected : TypeExpr) (source : Pattern) (work : Nat) : String :=
  searchControl label plan expected source work (CollectionRootSearch.search (profile := profile) expected)
    (CompleteExecution.RootCollection.backendTerm (StandardWire.planTable plan []))
    CompleteExecution.RootCollection.runTerm CompleteExecution.RootCollection.receiptTerm

def withheldRun : CollectionLoggedSearch.Run :=
  let source := CanonicalBags.canon (CollectionConsumers.marking
    [CollectionConsumers.token "A", CollectionConsumers.token "B"])
  let finished := CollectionLoggedSearch.run CollectionConsumers.petriPlan
    CollectionConsumers.petriCertificate source 20
  ⟨source, ⟨finished.state.lanes.map (fun lane =>
    { lane with consumed := 0, consumed_le := Nat.zero_le _ }), []⟩⟩

#guard withheldRun.state.lanes.all (fun lane => ScopedCollectionMachine.complete lane.state)
#guard !CollectionLoggedSearch.complete withheldRun.state
#guard !(CollectionLoggedSearch.resume 1 withheldRun.state).log.isEmpty
#guard CollectionLoggedSearch.complete (CollectionLoggedSearch.resume 1 withheldRun.state)

def statusControl : String :=
  let names := StandardWire.planTable CollectionConsumers.petriPlan []
  let backend := Term.application "CollectionSearch" [encodeList Term.string names]
  let next : CollectionLoggedSearch.Run :=
    ⟨withheldRun.source, CollectionLoggedSearch.resume 1 withheldRun.state⟩
  "!(let* (($backend (quote " ++ backend.render ++ "))\n" ++
  "        ($run (quote " ++ (CollectionLoggedSearchExecution.loggedRunTerm withheldRun).render ++ "))\n" ++
  "        ($status (gslt:search:status $backend UnusedPlan $run))\n" ++
  "        ($next (gslt:search:resume $backend UnusedPlan $run 1))\n" ++
  "        ($next-status (gslt:search:status $backend UnusedPlan $next))\n" ++
  "        ($published (gslt:search:publication $backend $next)))\n" ++
  "  (println! (CollectionStatusControl \"withheld-firing\"" ++
    " (== $status SearchPending)" ++
    " (== $next (quote " ++ (CollectionLoggedSearchExecution.loggedRunTerm next).render ++ "))" ++
    " (== $next-status SearchComplete)" ++
    " (== $published (quote " ++ (encodeList CollectionPlanExecution.planFiringTerm next.state.log).render ++ ")))))"

def sexpr (items : List String) : String :=
  "(" ++ String.intercalate " " items ++ ")"

def call (head : String) (items : List String) : String := sexpr (head :: items)

def letStar (bindings : List (String × String)) (body : String) : String :=
  call "let*" [sexpr (bindings.map fun (name, value) => sexpr [name, value]), body]

def select (value : String) (pattern body : String) : String :=
  call "case" [value, sexpr [sexpr [pattern, body]]]

def handoffControl (label : String) (plan : GeneralExecutionAdmission.Plan)
    (source : Pattern) (type : TypeExpr) (firing : CollectionPlanMachine.Firing)
    {goal : StructuralDescent.Scheduled.Goal}
    (started finished : StructuralDescent.Scheduled.State (GeneralPlanEnvironment.environment plan) goal)
    (offset : Nat := 0) : String :=
  let environment := GeneralPlanEnvironment.environment plan
  let quoted (term : Term) := call "quote" [term.render]
  let middle := StructuralDescent.Scheduled.run environment goal 1 started
  let assertions := call "println!" [call "CollectionHandoffControl"
    [reprStr label,
     call "==" ["$firing", quoted (CollectionPlanExecution.planFiringTerm firing)],
     call "==" ["$started", quoted (CompleteExecution.DescentCodec.stateTerm started)],
     call "==" ["$zero", "$started"],
     call "==" ["$middle", quoted (CompleteExecution.DescentCodec.stateTerm middle)],
     call "==" ["$finished", quoted (CompleteExecution.DescentCodec.stateTerm finished)],
     call "==" ["$resumed", "$finished"]]]
  let body := letStar
    [("$started", call "gslt:collection-backend:begin" ["$environment", "0", "$type", "$firing"]),
     ("$zero", call "gslt:descent:run" ["$environment", "0", "$started"]),
     ("$middle", call "gslt:descent:run" ["$environment", "1", "$started"]),
     ("$resumed", call "gslt:descent:run" ["$environment", "19", "$middle"]),
     ("$finished", call "gslt:descent:run" ["$environment", "20", "$started"])] assertions
  "!" ++ letStar
    [("$plan", quoted (CompletePlanWire.planTerm plan plan.snapshot.freeTypes [] type)),
     ("$backend", quoted (.application "CollectionSearch"
       [encodeList Term.string (StandardWire.planTable plan [])])),
     ("$source", quoted (InferenceCettaWire.encodePattern source)),
     ("$environment", quoted (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
       (environment.free.entriesOn []))),
     ("$type", quoted (InferenceCettaWire.AuthoredRule.typeTerm type)),
     ("$run", call "gslt:search:run" ["$backend", "$plan", "$source", "30"]),
     ("$published", call "gslt:search:publication" ["$backend", "$run"]),
     ("$selected-publication", call "gslt:complete:drop" [toString offset, "$published"])]
    (select "$selected-publication" "(LCons $firing $later)" body)

def depthCutControl : String :=
  let environment := CollectionConsumers.Controls.petriEnvironment
  let quoted (term : Term) := call "quote" [term.render]
  "!" ++ letStar
    [("$environment", quoted (PremiseOperationsExecution.GeneralExecution.environmentTerm
       environment (environment.free.entriesOn []))),
     ("$goal", quoted (CompleteExecution.DescentCodec.goalTerm
       CollectionConsumers.Controls.petriDepthCutGoal)),
     ("$initial", call "gslt:descent:start" ["$goal"]),
     ("$cut", call "gslt:descent:run" ["$environment", "1", "$initial"])]
    (call "println!" [call "CollectionCutControl"
      [reprStr "depth-cut-remains-unresolved", call "==" ["$cut", quoted
        (CompleteExecution.DescentCodec.stateTerm CollectionConsumers.Controls.petriDepthCut)]]])

def rawHandoffControl (permitted : Bool) : String :=
  let plan := CollectionConsumers.Controls.producedPetriPlan permitted
  let environment := GeneralPlanEnvironment.environment plan
  let entry := CollectionConsumers.Controls.producedPetriEntry permitted
  let receipt := CollectionConsumers.Controls.producedPetriReceipt permitted
  let goal := CollectionConsumers.Controls.producedPetriGoal permitted
  let started := CollectionConsumers.Controls.producedPetriScheduled permitted
  let middle := StructuralDescent.Scheduled.run environment goal 1 started
  let finished := CollectionConsumers.Controls.producedPetriRun permitted
  let quoted (term : Term) := call "quote" [term.render]
  let assertions := call "println!" [call "CollectionRawHandoffControl"
    [reprStr s!"premise-produces-rhs-{permitted}",
     call "==" ["$index", toString entry.1],
     call "==" ["$query", quoted (ScopedCollectionExecution.requestTerm entry.2)],
     call "==" ["$receipt", quoted (ScopedCollectionExecution.receiptTerm receipt)],
     call "==" ["$provisional", "LNil"],
     call "==" ["$started", quoted (CompleteExecution.DescentCodec.stateTerm started)],
     call "==" ["$zero", "$started"],
     call "==" ["$middle", quoted (CompleteExecution.DescentCodec.stateTerm middle)],
     call "==" ["$finished", quoted (CompleteExecution.DescentCodec.stateTerm finished)],
     call "==" ["$resumed", "$finished"]]]
  let body := letStar
    [("$provisional", call "gslt:collection-machine:firings" ["$query", "$publication"]),
     ("$started", call "gslt:collection-backend:begin-match"
       ["$environment", "0", "$type", "$index", "$query", "$receipt"]),
     ("$zero", call "gslt:descent:run" ["$environment", "0", "$started"]),
     ("$middle", call "gslt:descent:run" ["$environment", "1", "$started"]),
     ("$resumed", call "gslt:descent:run" ["$environment", "29", "$middle"]),
     ("$finished", call "gslt:descent:run" ["$environment", "30", "$started"])] assertions
  let matched := letStar
    [("$initial", call "gslt:collection-machine:start" ["$query"]),
     ("$matched", call "gslt:collection-machine:resume" ["$query", "30", "$initial"]),
     ("$publication", call "gslt:collection-machine:publication" ["$matched"])]
    (select "$publication" "(LCons $receipt $later)" body)
  "!" ++ letStar
    [("$plan", quoted (CompletePlanWire.planTerm plan plan.snapshot.freeTypes [] (.base "Marking"))),
     ("$source", quoted (InferenceCettaWire.encodePattern CollectionConsumers.Controls.petriSource)),
     ("$environment", quoted (PremiseOperationsExecution.GeneralExecution.environmentTerm
       environment (environment.free.entriesOn []))),
     ("$type", quoted (InferenceCettaWire.AuthoredRule.typeTerm (.base "Marking"))),
     ("$requests", call "gslt:collection-search:requests-for-source" ["$plan", "$source"])]
    (select "$requests" "(LCons (CollectionPlanRequest $index $query) $rest)" matched)

def continuationControl (label : String) (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan) (source : Pattern) (type : TypeExpr)
    (first : CollectionMatcherBackend.Retained.Frame plan certificate source type)
    (rest : List (CollectionMatcherBackend.Retained.Frame plan certificate source type)) : String :=
  let frames := first :: rest
  let environment := GeneralPlanEnvironment.environment plan
  let started := CollectionMatcherBackend.Retained.State.begin frames
  let middle := CollectionMatcherBackend.Retained.State.run 1 started
  let finished := CollectionMatcherBackend.Retained.State.run 30 started
  let firstFinished := CollectionMatcherBackend.Retained.Frame.run 30 first
  let quoted (term : Term) := call "quote" [term.render]
  let bindings := frames.zipIdx.flatMap fun (frame, index) =>
    [(s!"$query-{index}", quoted (ScopedCollectionExecution.requestTerm frame.matched.request)),
     (s!"$receipt-{index}", quoted (ScopedCollectionExecution.receiptTerm frame.matched.receipt)),
     (s!"$continuation-{index}", call "gslt:collection-backend:frame-begin"
       ["$environment", toString frame.depth, "$type", toString frame.matched.ordinal,
        s!"$query-{index}", s!"$receipt-{index}"])]
  let nativeFrames := (frames.zipIdx.map fun (_, index) => s!"$continuation-{index}").foldr
    (fun frame tail => call "LCons" [frame, tail]) "LNil"
  "!" ++ letStar
    ([("$environment", quoted (PremiseOperationsExecution.GeneralExecution.environmentTerm
         environment (environment.free.entriesOn []))),
      ("$type", quoted (InferenceCettaWire.AuthoredRule.typeTerm type))] ++ bindings ++
     [("$started", call "gslt:collection-backend:state-begin" [nativeFrames]),
      ("$zero", call "gslt:collection-backend:state-run" ["$environment", "0", "$started"]),
      ("$middle", call "gslt:collection-backend:state-run" ["$environment", "1", "$started"]),
      ("$finished", call "gslt:collection-backend:state-run" ["$environment", "30", "$started"]),
      ("$resumed", call "gslt:collection-backend:state-run" ["$environment", "29", "$middle"]),
      ("$settled", call "gslt:collection-backend:state-settled" ["$finished"]),
      ("$first-finished", call "gslt:collection-backend:frame-run"
        ["$environment", "30", "$continuation-0"]),
      ("$first-published", call "gslt:collection-backend:frame-publication" ["$first-finished"])])
    (call "println!" [call "CollectionContinuationControl"
      [reprStr label,
       call "==" ["$continuation-0", quoted (CollectionContinuationExecution.frameTerm first)],
       call "==" ["$started", quoted (CollectionContinuationExecution.stateTerm started)],
       call "==" ["$zero", "$started"],
       call "==" ["$middle", quoted (CollectionContinuationExecution.stateTerm middle)],
       call "==" ["$finished", quoted (CollectionContinuationExecution.stateTerm finished)],
       call "==" ["$resumed", "$finished"],
       call "==" ["$settled", "1"],
       call "==" ["$first-finished", quoted (CollectionContinuationExecution.frameTerm firstFinished)],
       call "==" ["$first-published", quoted (encodeList CollectionContinuationExecution.publicationTerm
         firstFinished.publication)]]])

def outOfOrderControl : String :=
  let request := CollectionConsumers.Controls.outOfOrderRequest
  let requests := [(0, request)]
  let source : Pattern := .collection request.kind request.targets none
  let wire (work : Nat) := CollectionLoggedSearchExecution.loggedRunTerm
    ⟨source, CollectionConsumers.Controls.outOfOrderState work⟩
  let quoted (term : Term) := call "quote" [term.render]
  let bindings :=
    [("$requests", quoted (encodeList CollectionPlanExecution.requestEntryTerm requests)),
     ("$source", quoted (InferenceCettaWire.encodePattern source)),
     ("$zero", call "gslt:collection-search:run" ["$requests", "$source", "0"]),
     ("$middle", call "gslt:collection-search:run" ["$requests", "$source", "20"]),
     ("$finished", call "gslt:collection-search:run" ["$requests", "$source", "100"]),
     ("$resumed", call "gslt:collection-search:resume-run" ["$middle", "80"]),
     ("$status", call "gslt:collection-search:status" ["$finished"])]
  String.intercalate "\n" ([("zero", call "==" ["$zero", quoted (wire 0)]),
    ("interrupted", call "==" ["$middle", quoted (wire 20)]),
    ("complete", call "==" ["$finished", quoted (wire 100)]),
    ("resumed", call "==" ["$resumed", "$finished"]),
    ("status", call "==" ["$status", "SearchComplete"])].map fun (label, check) =>
      "!" ++ letStar bindings (call "println!"
        [call "CollectionPublicationControl" [reprStr s!"out-of-order-{label}", check]]))

/-- Check the complete native site payload against the independently generated
typed occurrences and the proved residual operation. -/
def contextControl (label : String) (site : GeneralTypedSites.SiteData) : String :=
  let variants := CollectionSelection.siteVariants site
  let quoted (term : Term) := call "quote" [term.render]
  let expected := encodeList CollectionContextExecution.variantTerm variants
  let wrong := encodeList CollectionContextExecution.variantTerm
    (variants.map fun variant => { variant with original := { variant.original with address := [999] } })
  "!" ++ letStar [("$site", quoted (ScopedRuleJobReadoutExecution.siteTerm site)),
    ("$variants", call "gslt:collection-context:site-variants" ["$site"])]
    (call "println!" [call "CollectionContextControl" [reprStr label,
      call "==" ["$variants", quoted expected],
      call "==" [call "==" ["$variants", quoted wrong], "False"]]])


def recursiveMatcherControl (specimen : RecursiveCollectionMachine.Controls.Case) (fuel : Nat) : String :=
  let request := specimen.request
  let names := CanonicalCompare.nameTable (CanonicalCompare.names request.target)
  let quote (term : Term) := call "quote" [term.render]
  let initial := RecursiveCollectionMachine.start request
  let expected := RecursiveCollectionMachine.run request fuel initial
  let first := fuel / 2
  let middle := RecursiveCollectionMachine.run request first initial
  "!" ++ letStar
    [("$request", quote (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm request)),
     ("$names", quote (encodeList Term.string names)),
     ("$initial", call "gslt:recursive-collection:start" ["$request"]),
     ("$actual", call "gslt:recursive-collection:run" ["$names", "$request", toString fuel, "$initial"]),
     ("$middle", call "gslt:recursive-collection:run" ["$names", "$request", toString first, "$initial"]),
     ("$resumed", call "gslt:recursive-collection:run" ["$names", "$request", toString (fuel-first), "$middle"])]
    (call "println!" [call "RecursiveMatcherControl" [reprStr s!"{specimen.label}-{fuel}",
      call "==" ["$initial", quote (RecursiveCollectionExecution.stateTerm initial)],
      call "==" ["$actual", quote (RecursiveCollectionExecution.stateTerm expected)],
      call "==" ["$middle", quote (RecursiveCollectionExecution.stateTerm middle)],
      call "==" ["$resumed", "$actual"]]])

def canonicalMatcherControl (specimen : RecursiveCollectionMachine.Controls.Case) (fuel : Nat) : String :=
  let request := specimen.request
  let canonical := RecursiveCollectionHandoff.canonicalRequest request
  let names := CanonicalCompare.nameTable (CanonicalCompare.names request.target)
  let backend := RecursiveCollectionHandoff.canonicalMatchingExecution
  let initial := backend.start request
  let machine := (canonical, RecursiveCollectionMachine.run canonical fuel
    (RecursiveCollectionMachine.start canonical))
  let next := backend.tick request machine
  let quote (term : Term) := call "quote" [term.render]
  "!" ++ letStar
    [("$request", quote (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm request)),
     ("$names", quote (encodeList Term.string names)),
     ("$machine", quote (RecursiveCollectionExecution.canonicalStateTerm machine)),
     ("$actual", quote (InferenceCettaWire.encodePattern request.target)),
     ("$expected", quote (InferenceCettaWire.encodePattern (CanonicalBags.canon request.target))),
     ("$initial", call "gslt:recursive-collection:canonical-start" ["$names", "$request"]),
     ("$next", call "gslt:recursive-collection:canonical-tick" ["$names", "$machine"]),
     ("$complete", call "gslt:recursive-collection:canonical-complete" ["$machine"]),
     ("$first", call "gslt:recursive-collection:canonical-answer-at" ["$machine", "0"]),
     ("$end", call "gslt:recursive-collection:canonical-answer-at"
       ["$machine", toString machine.2.answers.length]),
     ("$same", call "gslt:recursive-collection:canonical-input" ["$names", "$actual", "$expected"])]
    (call "println!" [call "CanonicalMatcherControl" [reprStr s!"{specimen.label}-{fuel}",
      call "==" ["$initial", quote (RecursiveCollectionExecution.canonicalStateTerm initial)],
      call "==" ["$next", quote (RecursiveCollectionExecution.canonicalStateTerm next)],
      call "==" ["$complete", if backend.complete machine then "True" else "False"],
      call "==" ["$first", quote (encodeOption RecursiveCollectionExecution.canonicalAnswerTerm
        machine.2.answers[0]?)],
      call "==" ["$end", "None"],
      call "==" ["$same", "True"]]])

def canonicalInputControl (label : String) (actual expected : Pattern) (accepted : Bool) : String :=
  let names := CanonicalCompare.nameTable
    (CanonicalCompare.names actual ++ CanonicalCompare.names expected)
  let quote (term : Term) := call "quote" [term.render]
  "!" ++ letStar
    [("$names", quote (encodeList Term.string names)),
     ("$actual", quote (InferenceCettaWire.encodePattern actual)),
     ("$expected", quote (InferenceCettaWire.encodePattern expected)),
     ("$same", call "gslt:recursive-collection:canonical-input" ["$names", "$actual", "$expected"])]
    (call "println!" [call "CanonicalMatcherInputControl" [reprStr label,
      call "==" ["$same", if accepted then "True" else "False"]]])

def presentationControl (test : RecursiveCollectionPresentation.Controls.Case) : String :=
  let names := CanonicalCompare.nameTable (CanonicalCompare.names test.target)
  let quote (term : Term) := call "quote" [term.render]
  "!" ++ letStar
    [("$names", quote (encodeList Term.string names)),
     ("$path", quote (encodeList Term.natural test.path)),
     ("$schema", quote (InferenceCettaWire.encodePattern test.schema)),
     ("$target", quote (InferenceCettaWire.encodePattern test.target)),
     ("$events", quote (encodeList RecursiveCollectionExecution.eventTerm test.events)),
     ("$actual", call "gslt:collection-presentation:at" ["$names", "$path", "$schema", "$target", "$events"])]
    (call "println!" [call "CollectionPresentationControl" [reprStr test.label,
      call "==" ["$actual", quote (encodeOption
        (CollectionPresentationExecution.presentationTerm InferenceCettaWire.encodePattern) test.expected)]]])

def recursiveHandoffControl (label : String) (request : RecursiveCollectionMachine.Request)
    (answer : RecursiveCollectionMachine.Answer) : String :=
  let names := CanonicalCompare.nameTable (CanonicalCompare.names request.target)
  let quote (term : Term) := call "quote" [term.render]
  let unused : EquationalScopedReceipts.Event := ⟨[], .hashSet, []⟩
  let altered := { answer with trace := answer.trace ++ [unused] }
  "!" ++ letStar
    [("$names", quote (encodeList Term.string names)),
     ("$request", quote (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm request)),
     ("$answer", quote (RecursiveCollectionExecution.answerTerm answer)),
     ("$altered", quote (RecursiveCollectionExecution.answerTerm altered)),
     ("$path", quote (encodeList Term.natural request.path)),
     ("$schema", quote (InferenceCettaWire.encodePattern request.schema)),
     ("$trace", call "gslt:collection-handoff:trace" ["$path", "$schema"]),
     ("$actual", call "gslt:collection-handoff:prepare" ["$names", "$request", "$answer"]),
     ("$bad", call "gslt:collection-handoff:prepare" ["$names", "$request", "$altered"])]
    (call "println!" [call "RecursiveHandoffControl" [reprStr label,
      call "==" ["$trace", quote (RuleInstantiationExecution.GeneralExecution.traceTerm
        (RecursiveCollectionPresentation.frontTraceAt request.path request.schema))],
      call "==" ["$actual", quote (encodeOption RecursiveCollectionHandoffExecution.preparedTerm
        (RecursiveCollectionHandoff.prepare request answer))],
      call "==" ["$bad", "None"]]])

def representationControl (label : String) (language : LanguageDef) (source : Pattern)
    (expected : TypeExpr) (accepted : Bool) : String :=
  let quote (term : Term) := call "quote" [term.render]
  let declarations := encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm language.terms
  let sites := GeneralTypedSites.generate language (fun _ => none) .all [] expected source
  "!" ++ letStar
    [("$declarations", quote declarations),
     ("$source", quote (InferenceCettaWire.encodePattern source)),
     ("$type", quote (InferenceCettaWire.AuthoredRule.typeTerm expected)),
     ("$permissions", quote (InferenceCettaWire.ContextObservation.permissionsTerm .all)),
     ("$typed", call "gslt:premise:type-has" ["$declarations", "LNil", "LNil", "$source", "$type"]),
     ("$sites", call "gslt:sites:generate"
       ["$declarations", "LNil", "$permissions", "LNil", "$type", "$source"])]
    (call "println!" [call "CollectionRepresentationControl" [reprStr label,
      call "==" ["$typed", if accepted then "True" else "False"],
      call "==" ["$sites", quote (encodeList ScopedRuleJobReadoutExecution.siteTerm sites)]]])

open GeneralPremise.SharedOutputControls.ChildPresentation in
def childAllocationCases : List RecursiveCollectionMachine.Controls.Case :=
  let request (target : Pattern) : RecursiveCollectionMachine.Request :=
    ⟨child, GeneralRuleBindingInference.inferredSpec child, 0, .left, [], 0, [], child.left, target⟩
  [⟨"child-allocation-canonical", request (choice [a]), 1⟩,
   ⟨"child-allocation-duplicate-presentation", request (choice [a, a]), 1⟩,
   ⟨"child-allocation-wrong-kind", request (.collection .hashBag [a] none), 0⟩,
   ⟨"child-held-noncanonical-target", heldTargetRequest true, 0⟩,
   ⟨"child-held-canonical-target", heldTargetRequest false, 1⟩]

def main : IO Unit := do
  IO.println "; Generated shared-runner collection controls."
  for (label, source, accepted) in ModuleSource.CollectionRepresentationControls.queries do
    IO.println (representationControl s!"independent-monoids-{label}"
      ModuleSource.CollectionRepresentationControls.core source
      ModuleSource.CollectionRepresentationControls.resultSort accepted)
  for (label, source, accepted) in ModuleSource.CollectionRepresentationControls.NamedSets.queries do
    IO.println (representationControl s!"named-sets-{label}"
      ModuleSource.CollectionRepresentationControls.NamedSets.core source
      ModuleSource.CollectionRepresentationControls.NamedSets.resultSort accepted)
  for test in RecursiveCollectionPresentation.Controls.cases do
    IO.println (presentationControl test)
  for specimen in RecursiveCollectionMachine.Controls.cases do
    for (answer, index) in (RecursiveCollectionMachine.Controls.finished specimen).answers.zipIdx do
      let request := specimen.request
      IO.println (recursiveHandoffControl s!"{specimen.label}-{index}" request answer)
      IO.println (presentationControl ⟨s!"published-{specimen.label}-{index}", request.path,
        request.schema, request.target, answer.trace,
        RecursiveCollectionPresentation.presentAt request.path request.schema request.target answer.trace⟩)
  for specimen in RecursiveCollectionMachine.Controls.cases do
    for fuel in [0, 1, 7, 100] do
      IO.println (recursiveMatcherControl specimen fuel)

  for specimen in childAllocationCases do
    let finished := RecursiveCollectionMachine.Controls.finished specimen
    unless RecursiveCollectionMachine.complete finished &&
        finished.answers.length == specimen.expectedCount do
      throw (IO.userError s!"Child allocation control failed: {specimen.label}")
    for fuel in [0, 1, 7, 100] do
      IO.println (recursiveMatcherControl specimen fuel)

  for specimen in childAllocationCases do
    for fuel in [0, 1, 7, 100] do
      IO.println (canonicalMatcherControl specimen fuel)

  let item := GeneralPremise.SharedOutputControls.ChildPresentation.a
  let collection (kind : CollType) (items : List Pattern) := .collection kind items none
  for (label, actual, expected, accepted) in
      [("set-idempotence", collection .hashSet [item, item], collection .hashSet [item], true),
       ("bag-occurrences", collection .hashBag [item, item], collection .hashBag [item], false),
       ("collection-kind", collection .hashSet [item], collection .hashBag [item], false),
       ("undeclared-unit", collection .hashSet [], .apply "Unit" [], false)] do
    unless (CanonicalBags.canon actual == CanonicalBags.canon expected) == accepted do
      throw (IO.userError s!"Canonical input control failed: {label}")
    IO.println (canonicalInputControl label actual expected accepted)

  let atom := CollectionSelection.ContextControls.atom
  let setOf := CollectionSelection.ContextControls.setOf
  let bagOf := CollectionSelection.ContextControls.bagOf
  for (label, term) in
      [("set-retain", setOf [atom "A"]),
       ("bag-consume", bagOf [atom "A"]),
       ("nested-set-retain", setOf [setOf [atom "A"]]),
       ("set-collapse", setOf [atom "A", atom "B"]),
       ("equal-bag-origins", bagOf [atom "A", atom "A"]),
       ("authored-container", .apply "Wrap" [setOf [atom "A"]]),
       ("mixed-nesting", bagOf [setOf [atom "A"], setOf [atom "A"]])] do
    for (site, index) in (CollectionSelection.ContextControls.selectedSites term).zipIdx do
      IO.println (contextControl s!"{label}-{index}" site)

  let underBinders := { CollectionSelection.ContextControls.permissions with
    underLambda := true, underMultiLambda := true }
  for (label, expected, term) in
      [("under-lambda", TypeExpr.arrow (.base "Proc") (.base "Proc"),
          Pattern.lambda none (setOf [atom "A"])),
       ("under-multi-lambda", .arrow (.multiBinder (.base "Proc")) (.base "Proc"),
          .multiLambda 2 [] (setOf [atom "A"])),
       ("ordered-vector", .collection .vec (.base "Proc"),
          .collection .vec [atom "B", atom "A"] none)] do
    let permissions := { underBinders with collectionKinds := [.vec, .hashBag, .hashSet] }
    let sites := (GeneralTypedSites.generate CollectionSelection.ContextControls.language
      (fun _ => none) permissions [] expected term).filter (fun site => site.focus == atom "A")
    if sites.isEmpty then throw (IO.userError s!"Missing typed context control: {label}")
    for (site, index) in sites.zipIdx do
      IO.println (contextControl s!"{label}-{index}" site)
  for work in [0, 1, 30] do
    IO.println (rootControl s!"root-petri-{work}" CollectionConsumers.petriPlan
      CollectionConsumers.Controls.RootControls.petriProfile (.base "Marking")
      CollectionConsumers.Controls.petriSource work)
    IO.println (rootControl s!"root-graph-{work}" CollectionConsumers.reachabilityPlan
      CollectionConsumers.Controls.RootControls.graphProfile (.base "Graph")
      CollectionConsumers.Controls.graphSource work)
  for permitted in [true, false] do
    IO.println (rootControl s!"root-producer-{permitted}"
      (CollectionConsumers.Controls.producedPetriPlan permitted)
      (CollectionConsumers.Controls.RootControls.producedProfile permitted) (.base "Marking")
      CollectionConsumers.Controls.petriSource 40)
  for work in [0, 1, 20] do
    for (label, source) in
        [("petri", CollectionConsumers.marking [CollectionConsumers.token "A", CollectionConsumers.token "B"]),
         ("petri-duplicate", CollectionConsumers.marking
           [CollectionConsumers.token "A", CollectionConsumers.token "A", CollectionConsumers.token "B"]),
         ("petri-missing", CollectionConsumers.marking [CollectionConsumers.token "A"])] do
      IO.println (rootControl s!"{label}-{work}" CollectionConsumers.petriPlan
        CollectionConsumers.Controls.RootControls.petriProfile (.base "Marking") source work)
    for (label, source) in
        [("graph", CollectionConsumers.graph
            [CollectionConsumers.edge "A" "B", CollectionConsumers.edge "B" "C"]),
         ("graph-overlap", CollectionConsumers.graph [CollectionConsumers.edge "A" "A"]),
         ("graph-missing", CollectionConsumers.graph
            [CollectionConsumers.edge "A" "B", CollectionConsumers.edge "A" "C"])] do
      IO.println (rootControl s!"{label}-{work}" CollectionConsumers.reachabilityPlan
        CollectionConsumers.Controls.RootControls.graphProfile (.base "Graph") source work)
  IO.println statusControl
  IO.println outOfOrderControl
  IO.println depthCutControl
  IO.println (rawHandoffControl true)
  IO.println (rawHandoffControl false)
  for permitted in [true, false] do
    IO.println (continuationControl s!"retained-producer-{permitted}"
      (CollectionConsumers.Controls.producedPetriPlan permitted)
      (CollectionConsumers.Controls.producedPetriCertificate permitted)
      CollectionConsumers.Controls.petriSource (.base "Marking")
      (CollectionConsumers.Controls.RetainedControls.producedFrame permitted) [])
  IO.println (continuationControl "retained-distinct-origins" CollectionConsumers.petriPlan
    CollectionConsumers.petriCertificate CollectionConsumers.Controls.petriDuplicateSource (.base "Marking")
    (CollectionConsumers.Controls.RetainedControls.duplicateFrame 0)
    [CollectionConsumers.Controls.RetainedControls.duplicateFrame 1])
  IO.println (handoffControl "petri-logged-continuation" CollectionConsumers.petriPlan
    CollectionConsumers.Controls.petriSource (.base "Marking")
    CollectionConsumers.Controls.petriLoggedFirstFiring
    CollectionConsumers.Controls.petriLoggedScheduled
    CollectionConsumers.Controls.petriLoggedScheduledRun)
  IO.println (handoffControl "graph-logged-continuation" CollectionConsumers.reachabilityPlan
    CollectionConsumers.Controls.graphSource (.base "Graph")
    CollectionConsumers.Controls.graphLoggedFirstFiring
    CollectionConsumers.Controls.graphLoggedScheduled
    CollectionConsumers.Controls.graphLoggedScheduledRun)
  for permitted in [true, false] do
    let controls := s!"guarded-petri-{permitted}"
    IO.println (handoffControl controls (CollectionConsumers.Controls.guardedPetriPlan permitted)
      CollectionConsumers.Controls.petriSource (.base "Marking")
      (CollectionConsumers.Controls.guardedPetriLoggedFirst permitted)
      (CollectionConsumers.Controls.guardedPetriScheduled permitted)
      (CollectionConsumers.Controls.guardedPetriScheduledRun permitted))
  for index in ([0, 1] : List (Fin 2)) do
    IO.println (handoffControl s!"petri-distinct-source-occurrence-{index.val}"
      CollectionConsumers.petriPlan CollectionConsumers.Controls.petriDuplicateSource
      (.base "Marking") (CollectionConsumers.Controls.petriDuplicateFiring index)
      (CollectionConsumers.Controls.petriDuplicateScheduled index)
      (CollectionConsumers.Controls.petriDuplicateScheduledRun index) index.val)

end CollectionRunnerControls

#eval CollectionRunnerControls.main

namespace NestedContinuationControls

open CollectionRunnerControls (sexpr call letStar)

def quoted (value : Term) : String := call "quote" [value.render]
def letStar (bindings : List (String × String)) (body : String) : String :=
  call "let*" [sexpr (bindings.map fun (label,value) => sexpr [label,value]),body]

def control (label : String) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (retained : CollectionNestedConsumerControls.Retained)
    (index : Nat) : String :=
  let request := retained.request
  let names := StandardWire.planTable plan []
  let matcher := retained.job.request
  let matched := RecursiveCollectionMachine.run matcher 100 (RecursiveCollectionMachine.start matcher)
  let initial := RecursiveCollectionContinuation.start request
  let finished := RecursiveCollectionContinuation.run request 80 initial
  let pub := RecursiveCollectionContinuation.publication request finished
  let jobRequest : GeneralRuleJobExecution.Request :=
    ⟨plan, bound, .base "Workspace", retained.job.presentedSource request.prepared,
      retained.job.preparedJob request.prepared⟩
  let receipt := pub.head?.bind fun firing => CollectionOccurrenceContinuation.finish?
    plan bound (.base "Workspace") retained.job request.prepared firing
  let finishBody := call "case" ["$published", sexpr
    [sexpr ["LNil","None"],
     sexpr ["(LCons (RecursiveCollectionContinued $witness $answer) $publication-rest)",
       call "gslt:rule:job-finish-root" ["$job-request",call "PremiseResult" ["$root-goal","$answer"]]]]]
  let assertions := call "println!" [call "NestedContinuationControl"
    [reprStr label,
      call "==" ["$matched",quoted (RecursiveCollectionExecution.stateTerm matched)],
      call "==" ["$selected",quoted (RecursiveCollectionExecution.answerTerm request.answer)],
      call "==" ["$prepared",quoted (RecursiveCollectionHandoffExecution.preparedTerm request.prepared)],
      call "==" ["$begin",quoted (RecursiveCollectionContinuationExecution.frameTerm request initial)],
      call "==" ["$finished",quoted (RecursiveCollectionContinuationExecution.frameTerm request finished)],
      call "==" ["$resumed","$finished"],
      call "==" ["$published",quoted (encodeList (RecursiveCollectionContinuationExecution.publicationTerm request) pub)],
      call "==" ["$early","LNil"],
      call "==" ["$receipt",quoted (encodeOption ScopedRuleJobReadoutExecution.receiptTerm receipt)]]]
  let body := letStar
    [("$begin",call "gslt:collection-continuation:begin"
        ["$environment",toString request.depth,"$bound","$type",toString request.index,"$rule","$spec","$prepared"]),
     ("$early",call "gslt:collection-continuation:publication" ["$begin"]),
     ("$finished",call "gslt:collection-continuation:run" ["$environment","80","$begin"]),
     ("$middle",call "gslt:collection-continuation:run" ["$environment","33","$begin"]),
     ("$resumed",call "gslt:collection-continuation:run" ["$environment","47","$middle"]),
     ("$published",call "gslt:collection-continuation:publication" ["$finished"]),
     ("$receipt",finishBody)] assertions
  "!" ++ letStar
    [("$names",quoted (encodeList Term.string names)),
     ("$matcher",quoted (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm matcher)),
     ("$environment",quoted (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn []))),
     ("$bound",quoted (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.bound)),
     ("$type",quoted (InferenceCettaWire.AuthoredRule.typeTerm request.type)),
     ("$rule",quoted (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule)),
     ("$spec",quoted (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec)),
     ("$job-request",quoted (ScopedRuleJobReadoutExecution.requestProjectionTerm jobRequest [])),
     ("$root-goal",quoted (PremiseOperationsExecution.GeneralExecution.goalTerm jobRequest.goal)),
     ("$matching-initial",call "gslt:recursive-collection:start" ["$matcher"]),
     ("$matched",call "gslt:recursive-collection:run"
        ["$names","$matcher","100","$matching-initial"])]
    (call "case" ["$matched",sexpr [sexpr ["(RecursiveCollectionState $pending $answers)",
      letStar [("$chosen",call "gslt:complete:drop" [toString index,"$answers"])]
        (call "case" ["$chosen",sexpr [sexpr ["(LCons $selected $matching-rest)",
          call "case" [call "gslt:collection-handoff:prepare" ["$names","$matcher","$selected"],
            sexpr [sexpr ["(Some $prepared)",body]]]]]])]]])

def main : IO Unit := do
  for permitted in [true,false] do
    let plan := CollectionNestedConsumerControls.plan permitted
    let cases := CollectionNestedConsumerControls.prepared permitted CollectionNestedConsumerControls.source
    unless cases.length == 2 do throw (IO.userError "Missing nested continuation cases")
    for (retained,index) in cases.zipIdx do
      IO.println (control s!"nested-guard-{permitted}-{index}" plan [] retained index)
  let bound : List TypeExpr := [.base "Place"]
  let source := CollectionNestedConsumerControls.boxed
    [CollectionNestedConsumerControls.token "A",.bvar 0,CollectionNestedConsumerControls.token "A",
      CollectionNestedConsumerControls.token "B"]
  let cases := CollectionNestedConsumerControls.prepared true source bound
  unless cases.length == 2 do throw (IO.userError "Missing ambient continuation cases")
  for (retained,index) in cases.zipIdx do
    IO.println (control s!"nested-ambient-{index}" (CollectionNestedConsumerControls.plan true) bound retained index)

end NestedContinuationControls
#eval NestedContinuationControls.main

namespace CollectionBatchControls

open CollectionRunnerControls (sexpr call letStar)
open NestedContinuationControls (quoted)
open CollectionOccurrenceBatch

def wireList : List String → String
  | [] => "LNil"
  | head :: rest => call "LCons" [head, wireList rest]

def frameBegin {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (allocation : Allocation plan bound expected source)
    (ordinal : Nat) : String :=
  let request := allocation.request
  let name (field : String) := s!"$allocation-{ordinal}-{field}"
  letStar
    [(name "origin",quoted (CollectionOccurrenceBatchExecution.originTerm allocation.job allocation.answer)),
     (name "bound",quoted (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.bound)),
     (name "type",quoted (InferenceCettaWire.AuthoredRule.typeTerm request.type)),
     (name "rule",quoted (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule)),
     (name "spec",quoted (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec)),
     (name "prepared",quoted (RecursiveCollectionHandoffExecution.preparedTerm request.prepared))]
    (call "gslt:occurrence-batch:frame-begin"
      [name "origin","$environment",toString request.depth,name "bound",name "type",toString request.index,
        name "rule",name "spec",name "prepared"])

def control (label : String) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (source : Pattern)
    (allocations : List (Allocation plan bound (.base "Workspace") source))
    (skew : Bool) : String := Id.run do
  let mut bindings := [("$environment", quoted (PremiseOperationsExecution.GeneralExecution.environmentTerm
    (GeneralPlanEnvironment.environment plan) ((GeneralPlanEnvironment.environment plan).free.entriesOn [])))]
  let mut frameNames := []
  for (allocation,index) in allocations.zipIdx do
    let name := s!"$frame-{index}"
    bindings := bindings ++ [(name, frameBegin allocation index)]
    frameNames := frameNames ++ [name]
  let initial := State.begin allocations
  let mut seed := initial
  if skew then
    match initial.frames with
    | first :: second :: _ =>
      let pause := ((List.range 80).find? fun work =>
        (Frame.run work first).publication.isEmpty &&
          !(Frame.run (work + 1) first).publication.isEmpty).getD 0
      let frames := [Frame.run pause first, Frame.run 80 second]
      seed := ⟨frames, frames.flatMap Frame.publication⟩
      bindings := bindings ++
        [("$paused-first", call "gslt:occurrence-batch:frame-run" ["$environment",toString pause,"$frame-0"]),
         ("$finished-second", call "gslt:occurrence-batch:frame-run" ["$environment","80","$frame-1"]),
         ("$old-log",call "gslt:occurrence-batch:frame-publication" ["$finished-second"]),
         ("$seed",call "RecursiveOccurrenceBatch"
           [wireList ["$paused-first","$finished-second"],"$old-log"])]
    | _ => pure ()
  else
    bindings := bindings ++ [("$seed",call "gslt:occurrence-batch:begin" [wireList frameNames])]
  let afterOne := State.run 1 seed
  let finished := State.run 80 seed
  bindings := bindings ++
    [("$zero",call "gslt:occurrence-batch:run" ["$environment","0","$seed"]),
     ("$one",call "gslt:occurrence-batch:run" ["$environment","1","$seed"]),
     ("$full",call "gslt:occurrence-batch:run" ["$environment","80","$seed"]),
     ("$first-part",call "gslt:occurrence-batch:run" ["$environment","33","$seed"]),
     ("$resumed",call "gslt:occurrence-batch:run" ["$environment","47","$first-part"]),
     ("$one-publication",call "gslt:occurrence-batch:publication" ["$one"]),
     ("$publication",call "gslt:occurrence-batch:publication" ["$full"])]
  let encodeState := CollectionOccurrenceBatchExecution.stateTerm
  let encodePublication := encodeList CollectionOccurrenceBatchExecution.publicationTerm
  return "!" ++ letStar bindings (call "println!" [call "CollectionBatchControl"
    [reprStr label,
      call "==" [wireList frameNames, quoted (encodeList CollectionOccurrenceBatchExecution.frameTerm initial.frames)],
      call "==" ["$seed",quoted (encodeState seed)],
      call "==" ["$zero","$seed"],
      call "==" ["$one",quoted (encodeState afterOne)],
      call "==" ["$full",quoted (encodeState finished)],
      call "==" ["$resumed","$full"],
      call "==" ["$one-publication",quoted (encodePublication afterOne.log)],
      call "==" ["$publication",quoted (encodePublication finished.log)]]])

def main : IO Unit := do
  for permitted in [true,false] do
    IO.println (control s!"guarded-batch-{permitted}" (CollectionNestedConsumerControls.plan permitted)
      [] CollectionNestedBatchControls.source
      (CollectionNestedBatchControls.allocations permitted CollectionNestedBatchControls.source) false)
  let bound : List TypeExpr := [.base "Place"]
  let source := CollectionNestedConsumerControls.boxed
    [CollectionNestedConsumerControls.token "A",.bvar 0,CollectionNestedConsumerControls.token "A",
      CollectionNestedConsumerControls.token "B"]
  IO.println (control "guarded-batch-ambient" (CollectionNestedConsumerControls.plan true)
    bound source (CollectionNestedBatchControls.allocations true source bound) false)
  IO.println (control "delayed-earlier-allocation" (CollectionNestedConsumerControls.plan true)
    [] CollectionNestedBatchControls.source
    (CollectionNestedBatchControls.allocations true CollectionNestedBatchControls.source) true)

end CollectionBatchControls
#eval CollectionBatchControls.main

namespace OccurrenceMachineControls

open CollectionRunnerControls (call)
open NestedContinuationControls (quoted letStar)

def control (label : String) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (input : Pattern) : String :=
  let source := CanonicalBags.canon input
  let names := StandardWire.planTable plan []
  let seed := CollectionOccurrenceMachine.begin plan bound expected source
  let done := CollectionOccurrenceMachine.run 0 200 seed
  let extra := CollectionOccurrenceMachine.run 0 30 done
  let assertions := call "println!" [call "OccurrenceMachineFullControl"
    [reprStr label,
      call "==" ["$seed",quoted (CollectionOccurrenceMachineExecution.stateTerm seed)],
      call "==" ["$zero","$seed"],
      call "==" ["$done",quoted (CollectionOccurrenceMachineExecution.stateTerm done)],
      call "==" ["$resumed","$done"],
      call "==" ["$publication",quoted (encodeList CollectionOccurrenceBatchExecution.publicationTerm done.batch.log)],
      call "==" ["$count",toString done.batch.log.length],
      call "==" ["$extra",quoted (CollectionOccurrenceMachineExecution.stateTerm extra)]]]
  "!" ++ letStar
    [("$names",quoted (encodeList Term.string names)),
     ("$environment",quoted (PremiseOperationsExecution.GeneralExecution.environmentTerm
       (GeneralPlanEnvironment.environment plan) [])),
     ("$lanes",quoted (encodeList CollectionOccurrenceMatcherExecution.laneTerm seed.matchers)),
     ("$seed",call "gslt:occurrence-machine:from-lanes" ["$lanes"]),
     ("$zero",call "gslt:occurrence-machine:run" ["$names","$environment","0","0","$seed"]),
     ("$done",call "gslt:occurrence-machine:run" ["$names","$environment","0","200","$seed"]),
     ("$part",call "gslt:occurrence-machine:run" ["$names","$environment","0","73","$seed"]),
     ("$resumed",call "gslt:occurrence-machine:run" ["$names","$environment","0","127","$part"]),
     ("$extra",call "gslt:occurrence-machine:run" ["$names","$environment","0","30","$done"]),
     ("$publication",call "gslt:occurrence-machine:publication" ["$done"]),
     ("$count",call "gslt:automata:length" ["$publication"])] assertions

def main : IO Unit := do
  for permitted in [true,false] do
    IO.println (control s!"nested-guard-{permitted}" (CollectionNestedConsumerControls.plan permitted)
      [] (.base "Workspace") CollectionNestedConsumerControls.source)
  IO.println (control "nested-ambient" (CollectionNestedConsumerControls.plan true)
    [.base "Place"] (.base "Workspace") (CollectionNestedConsumerControls.boxed
      [CollectionNestedConsumerControls.token "A", .bvar 0,
        CollectionNestedConsumerControls.token "A", CollectionNestedConsumerControls.token "B"]))
  let a := CollectionSelection.ContextControls.atom "A"
  let b := CollectionSelection.ContextControls.atom "B"
  let setOf := CollectionSelection.ContextControls.setOf
  let bagOf := CollectionSelection.ContextControls.bagOf
  for (label,input) in [
      ("set-both-residuals",setOf [a]), ("bag-consumes-one",bagOf [a]),
      ("set-collapse",setOf [a,b]), ("set-nested-retained-copies",setOf [setOf [a]]),
      ("constructor-context",.apply "Wrap" [setOf [a]]),
      ("missing-redex",setOf [b])] do
    IO.println (control label CollectionSelection.ContextControls.plan [] (.base "Proc") input)

end OccurrenceMachineControls
#eval OccurrenceMachineControls.main

namespace OccurrenceDiscoveryControls
open CollectionRunnerControls (call)
open NestedContinuationControls (quoted letStar)

def control (label : String) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (input : Pattern) : String :=
  let source := CanonicalBags.canon input
  let begun := CollectionOccurrenceMachine.begin plan bound expected source
  let environment := GeneralPlanEnvironment.environment plan
  let bindings :=
    [("$declarations",quoted (PremiseOperationsExecution.DeclarationTyping.declarationsTerm environment.language.terms)),
     ("$free",quoted (PremiseOperationsExecution.DeclarationTyping.freeContextTerm [])),
     ("$permissions",quoted (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites)),
     ("$bound",quoted (PremiseOperationsExecution.DeclarationTyping.boundContextTerm bound)),
     ("$expected",quoted (InferenceCettaWire.AuthoredRule.typeTerm expected)),
     ("$source",quoted (InferenceCettaWire.encodePattern source)),
     ("$rules",quoted (encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules)),
     ("$jobs",call "gslt:sites:jobs"
       ["$declarations","$free","$permissions","$bound","$expected","$source","$rules"]),
     ("$lanes",call "gslt:occurrence-discovery:jobs" ["$jobs"]),
     ("$begun",call "gslt:occurrence-discovery:begin"
       ["$declarations","$free","$permissions","$bound","$expected","$source","$rules"])]
  "!" ++ letStar bindings (call "println!" [call "OccurrenceDiscoveryControl"
    [reprStr label,
     call "==" ["$jobs",quoted (encodeList ScopedRuleJobReadoutExecution.jobTerm
       (GeneralRuleJobs.jobs plan bound expected source))],
     call "==" ["$lanes",quoted (encodeList CollectionOccurrenceMatcherExecution.laneTerm begun.matchers)],
     call "==" ["$begun",quoted (CollectionOccurrenceMachineExecution.stateTerm begun)]]])

def main : IO Unit := do
  IO.println (control "guarded-workflow" (CollectionNestedConsumerControls.plan true) []
    (.base "Workspace") CollectionNestedConsumerControls.source)
  IO.println (control "ambient-workflow" (CollectionNestedConsumerControls.plan true)
    [.base "Place"] (.base "Workspace") (CollectionNestedConsumerControls.boxed
      [CollectionNestedConsumerControls.token "A", .bvar 0,
        CollectionNestedConsumerControls.token "A", CollectionNestedConsumerControls.token "B"]))
  let setOf := CollectionSelection.ContextControls.setOf
  let a := CollectionSelection.ContextControls.atom "A"
  IO.println (control "nested-set-variants" CollectionSelection.ContextControls.plan [] (.base "Proc")
    (setOf [setOf [a]]))
  IO.println (control "missing-redex" CollectionSelection.ContextControls.plan [] (.base "Proc")
    (setOf [CollectionSelection.ContextControls.atom "B"]))
  IO.println (control "wrong-source-type" (CollectionNestedConsumerControls.plan true) []
    (.base "Place") CollectionNestedConsumerControls.source)
#guard (GeneralRuleJobs.jobs (CollectionNestedConsumerControls.plan true) []
  (.base "Place") CollectionNestedConsumerControls.source).isEmpty

end OccurrenceDiscoveryControls
#eval OccurrenceDiscoveryControls.main

namespace NativeOccurrenceSearchControls
open CollectionRunnerControls (call)
open NestedContinuationControls (quoted letStar)
open CollectionOccurrenceSearchExecution (runTerm)

def statusTerm : Mettapedia.Machines.ResumableSearchRunner.Status → Term
  | .complete => .symbol "SearchComplete"
  | .pending => .symbol "SearchPending"
  | .blocked => .symbol "SearchBlocked"
def control (label : String) (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (input : Pattern) (work : Nat := 200) (first : Nat := 73) : String :=
  let search := CollectionOccurrenceSearch.search plan bound expected 0
  let names := StandardWire.planTable plan []
  let zero := search.run input 0
  let done := search.run input work
  let receipts := search.publication done
  "!" ++ letStar
    [("$names",quoted (encodeList Term.string names)),
     ("$plan",quoted (CompletePlanWire.planTerm plan [] bound expected)),
     ("$input",quoted (InferenceCettaWire.encodePattern input)),
     ("$zero",call "gslt:occurrence-search:run" ["$names","0","$plan","$input","0"]),
     ("$done",call "gslt:occurrence-search:run" ["$names","0","$plan","$input",toString work]),
     ("$part",call "gslt:occurrence-search:resume" ["$names","0","$zero",toString first]),
     ("$resumed",call "gslt:occurrence-search:resume" ["$names","0","$part",toString (work - first)]),
     ("$zero-status",call "gslt:occurrence-search:status" ["$zero"]),
     ("$status",call "gslt:occurrence-search:status" ["$done"]),
     ("$publication",call "gslt:occurrence-search:publication" ["$done"]),
     ("$target",call "case" ["$publication",
       "((LNil LNil) ((LCons $first $rest) (gslt:occurrence-search:target $names $first)))"])]
    (call "println!" [call "OccurrenceSearchControl"
      [reprStr label,
       call "==" ["$zero",quoted (runTerm [] zero)],
       call "==" ["$done",quoted (runTerm [] done)],
       call "==" ["$resumed","$done"],
       call "==" ["$zero-status",quoted (statusTerm (search.status zero))],
       call "==" ["$status",quoted (statusTerm (search.status done))],
       call "==" ["$publication",quoted (encodeList ScopedRuleJobReadoutExecution.receiptTerm receipts)],
       call "==" ["$target",quoted (match receipts with
         | [] => .symbol "LNil"
         | first :: _ => InferenceCettaWire.encodePattern (search.target first))]]])
def pauseControl (label : String) (plan : GeneralExecutionAdmission.Plan) : String :=
  let search := CollectionOccurrenceSearch.search plan [] (.base "Workspace") 0
  let paused := search.run CollectionQueryControls.source 60
  let names := StandardWire.planTable plan []
  "!" ++ letStar
    [("$names",quoted (encodeList Term.string names)),
     ("$plan",quoted (CompletePlanWire.planTerm plan [] [] (.base "Workspace"))),
     ("$input",quoted (InferenceCettaWire.encodePattern CollectionQueryControls.source)),
     ("$paused",call "gslt:occurrence-search:run" ["$names","0","$plan","$input","60"]),
     ("$status",call "gslt:occurrence-search:status" ["$paused"])]
    (call "println!" [call "OccurrenceSearchStatusControl" [reprStr label,
      call "==" ["$paused",quoted (runTerm [] paused)],
      call "==" ["$status",quoted (statusTerm .pending)]]])
def blockedControl : String :=
  let plan := CollectionNestedConsumerControls.plan true
  let done := (CollectionOccurrenceSearch.search plan [] (.base "Workspace") 0).run
    CollectionNestedConsumerControls.source 200
  let blocked := match done.state.batch.frames with
    | [] => done
    | first :: rest =>
      { done with state := { done.state with batch := { done.state.batch with frames :=
        { first with state := { first.state with agenda := [], unresolved := [.depthExhausted 0] } } :: rest } } }
  "!" ++ letStar [("$blocked",quoted (runTerm [] blocked)),
    ("$status",call "gslt:occurrence-search:status" ["$blocked"]),
    ("$publication",call "gslt:occurrence-search:publication" ["$blocked"])]
    (call "println!" [call "OccurrenceSearchStatusControl" [reprStr "unresolved-is-blocked",
      call "==" ["$status","SearchBlocked"],
      call "==" ["$publication",quoted (encodeList ScopedRuleJobReadoutExecution.receiptTerm
        ((CollectionOccurrenceSearch.search plan [] (.base "Workspace") 0).publication blocked))]]])
def main : IO Unit := do
  for permitted in [true,false] do
    IO.println (control s!"guarded-{permitted}" (CollectionNestedConsumerControls.plan permitted) []
      (.base "Workspace") CollectionNestedConsumerControls.source)
  IO.println (control "ambient-workflow" (CollectionNestedConsumerControls.plan true)
    [.base "Place"] (.base "Workspace") (CollectionNestedConsumerControls.boxed
      [CollectionNestedConsumerControls.token "A", .bvar 0,
        CollectionNestedConsumerControls.token "A", CollectionNestedConsumerControls.token "B"]))
  let a := CollectionSelection.ContextControls.atom "A"
  let b := CollectionSelection.ContextControls.atom "B"
  let setOf := CollectionSelection.ContextControls.setOf
  for (label,input) in [("set-both-residuals",setOf [a]),
      ("nested-retained-copies",setOf [setOf [a]]), ("missing-redex",setOf [b])] do
    IO.println (control label CollectionSelection.ContextControls.plan [] (.base "Proc") input)
  IO.println blockedControl
  for (label, values, copies) in [
      ("collection-input-enabled", [CollectionInputGuardControls.a, CollectionInputGuardControls.b], 1),
      ("collection-input-provider-occurrences", [CollectionInputGuardControls.a, CollectionInputGuardControls.b], 2),
      ("collection-input-missing", [CollectionInputGuardControls.a], 1),
      ("collection-input-noncanonical-row", [CollectionInputGuardControls.b, CollectionInputGuardControls.a], 1)] do
    IO.println (control label (CollectionInputGuardControls.plan values copies) [] (.base "Workspace")
      CollectionNestedConsumerControls.source)
  for (label, copies, witness) in [
      ("mixed-query", 1, CollectionQueryControls.b),
      ("mixed-query-duplicate-provider", 2, CollectionQueryControls.b),
      ("mixed-query-missing-provider", 0, CollectionQueryControls.b),
      ("mixed-query-wrong-witness", 1, CollectionQueryControls.a)] do
    IO.println (control label (CollectionQueryControls.plan copies
      [CollectionQueryControls.a, CollectionQueryControls.b]
      [CollectionQueryControls.a, CollectionQueryControls.a, CollectionQueryControls.b] witness)
      [] (.base "Workspace") CollectionQueryControls.source 800 60)
  for copies in [1,2] do
    IO.println (pauseControl s!"mixed-query-pending-{copies}"
      (CollectionQueryControls.plan copies
        [CollectionQueryControls.a, CollectionQueryControls.b]
        [CollectionQueryControls.a, CollectionQueryControls.a, CollectionQueryControls.b]))
end NativeOccurrenceSearchControls
#eval NativeOccurrenceSearchControls.main

namespace OccurrenceSharedRunnerControls
open CollectionRunnerControls (searchControl)

def control (label : String) (plan : GeneralExecutionAdmission.Plan)
    (expected : TypeExpr) (input : Pattern) : String :=
  let names := StandardWire.planTable plan []
  searchControl label plan expected input 200 (CollectionOccurrenceSearch.search plan [] expected 0)
    (CompleteExecution.CollectionOccurrence.backendTerm names 0)
    (CollectionOccurrenceSearchExecution.runTerm []) ScopedRuleJobReadoutExecution.receiptTerm

def main : IO Unit := do
  for permitted in [true,false] do
    IO.println (control s!"shared-nested-guard-{permitted}" (CollectionNestedConsumerControls.plan permitted)
      (.base "Workspace") CollectionNestedConsumerControls.source)
  let a := CollectionSelection.ContextControls.atom "A"
  let b := CollectionSelection.ContextControls.atom "B"
  let setOf := CollectionSelection.ContextControls.setOf
  IO.println (control "shared-set-both-residuals" CollectionSelection.ContextControls.plan
    (.base "Proc") (setOf [a]))
  IO.println (control "shared-set-collapse" CollectionSelection.ContextControls.plan
    (.base "Proc") (setOf [a,b]))
end OccurrenceSharedRunnerControls
#eval OccurrenceSharedRunnerControls.main

namespace LocalQuantifierControls

open CollectionRunnerControls (call letStar)
open NestedContinuationControls (quoted)
open GeneralPremise.SharedOutputControls

/-- Stop after the first body, before evaluating the next element. The
assignment at this retained task must have no body-local output. -/
def betweenBodies {environment : GeneralPremise.Environment}
    {outer : StructuralDescent.Scheduled.Goal}
    (state : StructuralDescent.Scheduled.State environment outer) : Bool :=
  state.agenda.any fun task => match task with
    | .evaluate (.quantified _ _ _ _ 1 _ initial) _ =>
        readBody initial "Y" == none && readBody initial "element" == some one
    | _ => false

def control (label : String) (zeroRows : Nat) (oneRow : Bool) (expected : Nat)
    (nested : Bool := false) : IO String := do
  let environment := LocalOutputs.environment zeroRows oneRow nested
  let goal := StructuralDescent.Scheduled.Goal.root 1 [] term (source [zero, one]) 0
  let begun := StructuralDescent.Scheduled.start environment goal
  let cut := (List.range 200).find? fun work =>
    betweenBodies (StructuralDescent.Scheduled.run environment goal work begun)
  let some cut := cut | throw (IO.userError "No retained between-body quantifier checkpoint")
  let middle := StructuralDescent.Scheduled.run environment goal cut begun
  let finished := StructuralDescent.Scheduled.run environment goal 400 begun
  unless cut > 0 && !StructuralDescent.Scheduled.complete environment goal middle &&
      StructuralDescent.Scheduled.complete environment goal finished &&
      finished.answers.length == expected do
    throw (IO.userError "Quantified checkpoint is not pending or has the wrong final receipt account")
  let assertions := call "println!" [call "LocalQuantifierControl"
    [reprStr label,
     call "==" ["$begin", quoted (CompleteExecution.DescentCodec.stateTerm begun)],
     call "==" ["$zero", "$begin"],
     call "==" ["$middle", quoted (CompleteExecution.DescentCodec.stateTerm middle)],
     call "==" ["$middle-zero", "$middle"],
     call "==" ["$finished", quoted (CompleteExecution.DescentCodec.stateTerm finished)],
     call "==" ["$resumed", "$finished"],
     call "==" [call "gslt:premise:machine-complete" ["$finished"], "True"],
     call "==" [call "gslt:premise:machine-complete" ["$middle"], "False"]]]
  pure ("!" ++ letStar
    [("$environment", quoted (PremiseOperationsExecution.GeneralExecution.environmentTerm
       environment (environment.free.entriesOn []))),
     ("$goal", quoted (CompleteExecution.DescentCodec.goalTerm goal)),
     ("$begin", call "gslt:descent:start" ["$goal"]),
     ("$zero", call "gslt:descent:run" ["$environment", "0", "$begin"]),
     ("$middle", call "gslt:descent:run" ["$environment", toString cut, "$begin"]),
     ("$middle-zero", call "gslt:descent:run" ["$environment", "0", "$middle"]),
     ("$finished", call "gslt:descent:run" ["$environment", "400", "$begin"]),
     ("$resumed", call "gslt:descent:run" ["$environment", toString (400 - cut), "$middle"])]
    assertions)

def main : IO Unit := do
  for (label, zeroRows, oneRow, expected) in [
      ("independent-quantified-outputs", 1, true, 1),
      ("duplicate-quantified-validation", 2, true, 2),
      ("missing-second-quantified-row", 1, false, 0)] do
    IO.println (← control label zeroRows oneRow expected)
  IO.println (← control "nested-independent-outputs" 2 true 4 true)

end LocalQuantifierControls
#eval LocalQuantifierControls.main

namespace RetainedCollectionControls
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching
open CollectionOccurrenceHandoff RecursiveCollectionHandoff CollectionOccurrenceBatch
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
private def authored : LanguageDef := CollectionNestedInputPetri.language.toOption.getD (LanguageDef.empty "")
private def language : LanguageDef := (authored.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")
private def inputType : TypeExpr :=
  (language.rewrites.head?.bind fun rule => rule.typeContext.lookup "rest").getD (.base "Marking")
private def token (label : String) : Pattern := .apply label []
private def bag (values : List Pattern) : Pattern := .collection .hashBag values none
private def boxed (values : List Pattern) : Pattern := .apply "Box" [.apply "Flow" [bag values]]
private def source : Pattern := boxed [token "A", token "A", token "B"]
private def expected : Pattern := CanonicalBags.canon (boxed [token "A", token "B", token "B"])
private def provider (values : List Pattern) (copies : Nat) : ProviderSnapshot :=
  { signatures := [⟨"inspect", [inputType], [.input]⟩],
    rows := List.replicate copies ⟨"inspect", [bag values]⟩ }
private def plan (values : List Pattern) (copies : Nat) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile ⟨language, [], provider values copies⟩
    { sites := .all, includeDerivedEquations := false }

private def allocated (values : List Pattern) (copies : Nat) :
    List (Allocation (plan values copies) [] (.base "Workspace") (CanonicalBags.canon source)) :=
  (jobs (plan values copies) [] (.base "Workspace") (CanonicalBags.canon source)).attach.flatMap fun selected =>
    let job := selected.val
    let valid := (jobs_exact _ _ _ _ _).mp selected.property
    let matched := RecursiveCollectionMachine.run job.request 100 (RecursiveCollectionMachine.start job.request)
    matched.answers.attach.filterMap fun published =>
      allocate? job valid 100 published.val published.property 0


private def call (head : String) (arguments : List String) : String :=
  "(" ++ head ++ (if arguments.isEmpty then "" else " " ++ String.intercalate " " arguments) ++ ")"
private def quote (value : Term) : String := call "quote" [value.render]
private def letStar (bindings : List (String × String)) (body : String) : String :=
  call "let*" ["(" ++ String.intercalate " " (bindings.map fun pair : String × String => call pair.1 [pair.2]) ++ ")", body]

private def frameTermIn (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (frame : Frame plan bound expected source matcher) : Term :=
  .application "RecursiveOccurrenceFrame"
    [CollectionOccurrenceBatchExecution.originTerm frame.allocation.job frame.allocation.answer,
      .application "RecursiveCollectionContinuation"
        [RecursiveCollectionHandoffExecution.preparedTerm frame.allocation.request.prepared,
          RetainedMatchingWire.Scheduled.stateTerm codec frame.state]]

private def batchTermIn (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (batch : State plan bound expected source matcher) : Term :=
  .application "RecursiveOccurrenceBatch"
    [encodeList (frameTermIn matcher codec) batch.frames,
      encodeList (CollectionOccurrenceBatchExecution.publicationTermWith codec.choiceTerm) batch.log]

private def frameCall {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (allocation : Allocation plan bound expected source)
    (index : Nat) : List (String × String) :=
  let request := allocation.request
  let data : List (String × Term) :=
    [("origin", CollectionOccurrenceBatchExecution.originTerm allocation.job allocation.answer),
     ("bound", CompleteExecution.DescentCodec.typesTerm request.bound),
     ("type", CompleteExecution.DescentCodec.typeTerm request.type),
     ("rule", InferenceCettaWire.AuthoredRule.rewriteTerm request.rule),
     ("spec", InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec),
     ("prepared", RecursiveCollectionHandoffExecution.preparedTerm request.prepared)]
  (data.map fun pair => (s!"${pair.1}{index}", quote pair.2)) ++
    [(s!"$frame{index}", call "gslt:occurrence-batch:frame-begin"
      [s!"$origin{index}", "$environment", toString request.depth,
        s!"$bound{index}", s!"$type{index}", toString request.index,
        s!"$rule{index}", s!"$spec{index}", s!"$prepared{index}"])]

private def batchControl (label : String) (values : List Pattern) (copies : Nat)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (canonical : Bool) (begun : State (plan values copies) [] (.base "Workspace")
      (CanonicalBags.canon source) matcher) : String :=
  let allocations := allocated values copies
  let environment := GeneralPlanEnvironment.environment (plan values copies)
  let footprint := source.freeFvarNames ++ providerFreeNames environment.provider
  let names := StructuralDescent.Scheduled.NameSupport.environmentNameTable environment footprint
  let core := PremiseOperationsExecution.GeneralExecution.environmentTerm environment
    (environment.free.entriesOn footprint)
  let profile := if canonical then RetainedMatchingWire.interpretedEnvironmentTerm names core else core
  let first := 3
  let middle := State.run first begun
  let whole := State.run 200 begun
  let frames := (allocations.zipIdx.flatMap fun pair => frameCall pair.1 pair.2)
  let frameList := (List.range allocations.length).foldr
    (fun index rest => call "LCons" [s!"$frame{index}", rest]) "LNil"
  "!" ++ letStar
    ([("$environment", quote profile)] ++ frames ++
      [("$initial", call "gslt:occurrence-batch:begin" [frameList]),
       ("$middle", call "gslt:occurrence-batch:run" ["$environment", toString first, "$initial"]),
       ("$actual", call "gslt:occurrence-batch:run" ["$environment", "200", "$initial"]),
       ("$resumed", call "gslt:occurrence-batch:run" ["$environment", toString (200 - first), "$middle"]),
       ("$published", call "gslt:occurrence-batch:publication" ["$actual"]),
       ("$count", call "gslt:automata:length" ["$published"])])
    (call "println!" [call "CanonicalPostmatchControl"
      [reprStr s!"{if canonical then "canonical" else "ordinary"}-{label}",
       call "==" ["$initial", quote (batchTermIn matcher codec begun)],
       call "==" ["$middle", quote (batchTermIn matcher codec middle)],
       call "==" ["$actual", quote (batchTermIn matcher codec whole)],
       call "==" ["$resumed", "$actual"],
       call "==" ["$published", quote (encodeList
         (CollectionOccurrenceBatchExecution.publicationTermWith codec.choiceTerm) whole.log)],
       call "==" ["$count", toString whole.log.length]]])
private def readoutControl (label : String) (values : List Pattern) (copies : Nat)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (canonical : Bool) (finish : Publication matcher.Choice → Option (GeneralRuleJobs.Receipt matcher.Choice))
    (begun : State (plan values copies) [] (.base "Workspace")
      (CanonicalBags.canon source) matcher) : String :=
  let allocations := allocated values copies
  let environment := GeneralPlanEnvironment.environment (plan values copies)
  let footprint := source.freeFvarNames ++ providerFreeNames environment.provider
  let names := StructuralDescent.Scheduled.NameSupport.environmentNameTable environment footprint
  let core := PremiseOperationsExecution.GeneralExecution.environmentTerm environment
    (environment.free.entriesOn footprint)
  let profile := if canonical then RetainedMatchingWire.interpretedEnvironmentTerm names core else core
  let first := 3
  let whole := State.run 200 begun
  let receipts := whole.log.filterMap finish
  let committed := CollectionCommittedObservation.retainedWith finish whole.log
  let planWire : Term := .application "CompletePlan"
    [profile, InferenceCettaWire.ContextObservation.permissionsTerm (plan values copies).permissions.sites,
      encodeList InferenceCettaWire.AuthoredRule.typeTerm [], InferenceCettaWire.AuthoredRule.typeTerm (.base "Workspace"),
      encodeList ScopedRuleJobReadoutExecution.rulePlanTerm (plan values copies).rules, .symbol "LNil",
      .symbol (if StructuralDescent.checkEnvironment environment then "Admitted" else "Unadmitted")]
  let frames := (allocations.zipIdx.flatMap fun pair => frameCall pair.1 pair.2)
  let frameList := (List.range allocations.length).foldr
    (fun index rest => call "LCons" [s!"$frame{index}", rest]) "LNil"
  "!" ++ letStar
    ([("$environment", quote profile)] ++ frames ++
      [("$initial", call "gslt:occurrence-batch:begin" [frameList]),
       ("$middle", call "gslt:occurrence-batch:run" ["$environment", toString first, "$initial"]),
       ("$actual", call "gslt:occurrence-batch:run" ["$environment", "200", "$initial"]),
       ("$resumed", call "gslt:occurrence-batch:run" ["$environment", toString (200 - first), "$middle"]),
       ("$published", call "gslt:occurrence-batch:publication" ["$actual"]),
       ("$count", call "gslt:automata:length" ["$published"]),
       ("$plan", quote planWire),
       ("$receipts", call "gslt:occurrence-search:read-log" ["$plan", "$published"]),
       ("$committed", call "gslt:occurrence-search:read-committed" ["$plan", "$published"]),
       ("$resumed-published", call "gslt:occurrence-batch:publication" ["$resumed"]),
       ("$resumed-receipts", call "gslt:occurrence-search:read-log" ["$plan", "$resumed-published"]),
       ("$resumed-committed", call "gslt:occurrence-search:read-committed" ["$plan", "$resumed-published"]),
       ("$receipt-count", call "gslt:automata:length" ["$receipts"]),
       ("$pair-count", call "gslt:automata:length" ["$committed"])])
    (call "println!" [call "CanonicalReadoutControl"
      [reprStr s!"{if canonical then "canonical" else "ordinary"}-{label}",
       call "==" ["$receipts", quote (encodeList (ScopedRuleJobReadoutExecution.receiptTermWith codec.choiceTerm) receipts)],
       call "==" ["$committed", quote (encodeList (CollectionOccurrenceBatchExecution.committedTermWith codec.choiceTerm) committed)],
       call "==" ["$receipt-count", toString receipts.length],
       call "==" ["$pair-count", toString committed.length],
       call "==" ["$resumed-receipts", "$receipts"],
       call "==" ["$resumed-committed", "$committed"]]])

private def publicControl (label : String) (values : List Pattern) (copies : Nat)
    (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)
    (canonical : Bool)
    (profile : (input : Pattern) → SeedProfile matcher (plan values copies) []
      (.base "Workspace") (CanonicalBags.canon input))
    (finish : Publication matcher.Choice → Option (GeneralRuleJobs.Receipt matcher.Choice)) : String :=
  let p := plan values copies
  let environment := GeneralPlanEnvironment.environment p
  let footprint := source.freeFvarNames ++ providerFreeNames environment.provider
  let names := StructuralDescent.Scheduled.NameSupport.environmentNameTable environment footprint
  let core := PremiseOperationsExecution.GeneralExecution.environmentTerm environment
    (environment.free.entriesOn footprint)
  let environmentWire := if canonical then RetainedMatchingWire.interpretedEnvironmentTerm names core else core
  let planWire := CompletePlanWire.planTermWithEnvironment p environmentWire [] (.base "Workspace")
  let begun := CollectionOccurrenceSearch.beginWith matcher p [] (.base "Workspace") source
  let middle := CollectionOccurrenceSearch.runWith p [] (.base "Workspace") profile 0 source 3
  let whole := CollectionOccurrenceSearch.runWith p [] (.base "Workspace") profile 0 source 300
  let wire := CollectionOccurrenceSearchExecution.runTermWith codec planWire finish
  let receipts := CollectionOccurrenceSearch.publicationWith finish whole
  CollectionRunnerControls.measurement s!"public-{if canonical then "canonical" else "ordinary"}-{label}"
    source 300 3 whole.state.batch.frames.length whole.state.batch.log.length copies ++
  "!" ++ letStar
    [("$names", quote (encodeList Term.string names)), ("$plan", quote planWire),
     ("$source", quote (InferenceCettaWire.encodePattern source)),
     ("$zero", call "gslt:occurrence-search:run" ["$names", "0", "$plan", "$source", "0"]),
     ("$middle", call "gslt:occurrence-search:run" ["$names", "0", "$plan", "$source", "3"]),
     ("$actual", call "gslt:occurrence-search:run" ["$names", "0", "$plan", "$source", "300"]),
     ("$resumed", call "gslt:occurrence-search:resume" ["$names", "0", "$middle", "297"]),
     ("$receipts", call "gslt:occurrence-search:publication" ["$actual"])]
    (call "println!" [call "PublicOccurrenceControl"
      [reprStr s!"{if canonical then "canonical" else "ordinary"}-{label}",
       call "==" ["$zero", quote (wire begun)],
       call "==" ["$middle", quote (wire middle)],
       call "==" ["$actual", quote (wire whole)],
       call "==" ["$resumed", "$actual"],
       call "==" [call "gslt:occurrence-search:status" ["$zero"], "SearchPending"],
       call "==" [call "gslt:occurrence-search:status" ["$actual"],
         quote (NativeOccurrenceSearchControls.statusTerm (CollectionOccurrenceSearch.statusWith whole))],
       call "==" ["$receipts", quote (encodeList
         (ScopedRuleJobReadoutExecution.receiptTermWith codec.choiceTerm) receipts)]]])

def main : IO Unit := do
  unless CollectionNestedInputPetri.language.isOk && authored.toCore.isOk do
    throw (IO.userError "Guarded workflow authoring/core failed")
  for (label, values, copies) in [("guarded", [token "A", token "B"], 1),
      ("duplicate-validation", [token "A", token "B"], 2),
      ("wrong-premise", [token "A"], 1), ("missing-premise", [token "A", token "B"], 0),
      ("noncanonical-premise", [token "B", token "A"], 1)] do
    let allocations := allocated values copies
    unless allocations.length == 2 && (plan values copies).equations.isEmpty do
      throw (IO.userError "Guarded workflow must retain both token allocations without extra equations")
    let ordinary := State.begin allocations
    let canonical := State.beginCanonical allocations
    unless (State.run 3 canonical).frames.any (fun frame => !frame.state.agenda.isEmpty) do
      throw (IO.userError "Resume checkpoint must interrupt unfinished work")
    let ordinaryFinish : Publication → Option GeneralRuleJobs.Receipt :=
      fun packet => packet.finish? (plan values copies) [] (.base "Workspace")
    let canonicalFinish : Publication EquationalScopedReceipts.Event →
        Option (GeneralRuleJobs.Receipt EquationalScopedReceipts.Event) :=
      fun packet => packet.finishCanonical? (plan values copies) [] (.base "Workspace")
    IO.println (batchControl label values copies MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec false ordinary)
    IO.println (batchControl label values copies canonicalMatchingExecution
      RetainedMatchingWire.canonicalCodec true canonical)
    IO.println (readoutControl label values copies MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec false ordinaryFinish ordinary)
    IO.println (readoutControl label values copies canonicalMatchingExecution
      RetainedMatchingWire.canonicalCodec true canonicalFinish canonical)
    IO.println (publicControl label values copies MatchingExecution.ordinary
      RetainedMatchingWire.ordinaryCodec false
      (fun input => ordinarySeedProfile (plan values copies) [] (.base "Workspace") (CanonicalBags.canon input))
      ordinaryFinish)
    IO.println (publicControl label values copies canonicalMatchingExecution
      RetainedMatchingWire.canonicalCodec true
      (fun input => canonicalSeedProfile (plan values copies) [] (.base "Workspace") input) canonicalFinish)

end RetainedCollectionControls
#eval RetainedCollectionControls.main

namespace InterpretedNativeProbe

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open RetainedMatchingWire
open StructuralDescent.Scheduled

def call (head : String) (arguments : List String) : String :=
  "(" ++ head ++ (if arguments.isEmpty then "" else " " ++ String.intercalate " " arguments) ++ ")"

def quote (value : Term) : String := call "quote" [value.render]

def letStar (bindings : List (String × String)) (body : String) : String :=
  call "let*" ["(" ++ String.intercalate " " (bindings.map fun (name, value) => call name [value]) ++ ")", body]

def namesFor (environment : Environment) (source : Pattern) : List String :=
  StructuralDescent.Scheduled.NameSupport.environmentNameTable environment
    (source.freeFvarNames ++ providerFreeNames environment.provider)

def control (profile : MatchingExecution) (codec : MatchingCodec profile) (canonical : Bool)
    (label : String) (environment : Environment) (goal : Goal) (source : Pattern) (fuel : Nat) : String :=
  let names := namesFor environment source
  let environmentTerm := PremiseOperationsExecution.GeneralExecution.environmentTerm environment []
  let nativeEnvironment := if canonical then
      Term.application "InterpretedPremiseEnvironment" [encodeList Term.string names, environmentTerm]
    else environmentTerm
  let initial := start environment goal profile
  let first := fuel / 2
  let middle := run environment goal first initial
  let expected := run environment goal fuel initial
  "!" ++ letStar
    [("$environment", quote nativeEnvironment),
     ("$goal", quote (CompleteExecution.DescentCodec.goalTerm goal)),
     ("$initial", call "gslt:descent:start" ["$goal"]),
     ("$middle", call "gslt:descent:run" ["$environment", toString first, "$initial"]),
     ("$actual", call "gslt:descent:run" ["$environment", toString fuel, "$initial"]),
     ("$resumed", call "gslt:descent:run" ["$environment", toString (fuel-first), "$middle"]),
     ("$complete", call "gslt:premise:machine-complete" ["$actual"])]
    (call "println!" [call "InterpretedNativeControl"
      [reprStr s!"{if canonical then "canonical" else "ordinary"}-{label}-{fuel}",
       call "==" ["$initial", quote (RetainedMatchingWire.Scheduled.stateTerm codec initial)],
       call "==" ["$middle", quote (RetainedMatchingWire.Scheduled.stateTerm codec middle)],
       call "==" ["$actual", quote (RetainedMatchingWire.Scheduled.stateTerm codec expected)],
       call "==" ["$resumed", "$actual"],
       call "==" ["$complete", if complete environment goal expected then "True" else "False"]]])

def cases : List (String × Environment × Goal × Pattern) :=
  let child := SharedOutputControls.ChildPresentation.environment
  let parent := SharedOutputControls.ChildPresentation.goal
  let item := SharedOutputControls.ChildPresentation.a
  let box := SharedOutputControls.ChildPresentation.box
  let collection := SharedOutputControls.ChildPresentation.choice
  let queries : Bool → Environment := fun present =>
    SharedOutputControls.RetainedCollections.queryEnvironment present
  let query := SharedOutputControls.RetainedCollections.queryGoal
  let quantified := SharedOutputControls.RetainedCollections.quantifiedEnvironment
  let quantifiedGoal := SharedOutputControls.RetainedCollections.quantifiedGoal
  [("child-singleton", child, parent [item], box (collection [item])),
   ("child-duplicate", child, parent [item,item], box (collection [item,item])),
   ("child-missing", child, parent [], box (collection [])),
   ("query-joined", queries true, query, box item),
   ("query-missing", queries false, query, box item),
   ("quantified-singleton", quantified, quantifiedGoal [SharedOutputControls.zero],
     .apply "SetWrap" [.collection .hashSet [SharedOutputControls.zero] none]),
   ("quantified-duplicate", quantified, quantifiedGoal [SharedOutputControls.zero,SharedOutputControls.zero],
     .apply "SetWrap" [.collection .hashSet [SharedOutputControls.zero,SharedOutputControls.zero] none]),
   ("quantified-missing", quantified, quantifiedGoal [SharedOutputControls.zero,SharedOutputControls.one],
     .apply "SetWrap" [.collection .hashSet [SharedOutputControls.zero,SharedOutputControls.one] none]),
   ("quantified-empty", quantified, quantifiedGoal [], .apply "SetWrap" [.collection .hashSet [] none])]


def actualSum : IO Unit := do
  let environment := Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum.environment
  let chaos := Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum.chaos
  let zero := Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum.zero
  for (label, depth, element) in [("actual-rsum-child-success", 2, chaos),
      ("actual-rsum-child-missing", 2, zero), ("actual-rsum-depth-cut", 1, chaos)] do
    let goal := Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum.goal depth element
    let source := Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls.ActualSum.sum [element]
    for fuel in [0, 7, 500] do
      IO.println (InterpretedNativeProbe.control
        Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff.canonicalMatchingExecution
        Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RetainedMatchingWire.canonicalCodec
        true label environment goal source fuel)

def allPremises : IO Unit := do
  for (label, environment, goal, source) in cases do
    for fuel in [0, 7, 100] do
      IO.println (control MatchingExecution.ordinary RetainedMatchingWire.ordinaryCodec
        false label environment goal source fuel)
      IO.println (control RecursiveCollectionHandoff.canonicalMatchingExecution
        RetainedMatchingWire.canonicalCodec true label environment goal source fuel)
end InterpretedNativeProbe
#eval InterpretedNativeProbe.actualSum
#eval InterpretedNativeProbe.allPremises

namespace KnowledgeGraphProducerControls

open CollectionRunnerControls (call letStar select)
open NestedContinuationControls (quoted)
open CollectionConsumers
open CollectionConsumers.Controls.Observation.GraphControls
open CollectionOccurrenceBatch CollectionCommittedObservation GeneralPremise
open CollectionExecutionQualification.GraphObservation (logicalKeyTerm)

local instance : DecidableEq RecursiveCollectionHandoff.canonicalMatchingExecution.Choice := by
  change DecidableEq EquationalScopedReceipts.Event
  infer_instance

private def graphType : TypeExpr := .base "Graph"

private def packets (run : String) : String :=
  select run
    "(RecursiveOccurrenceRun $plan $source (RecursiveOccurrenceState $lanes (RecursiveOccurrenceBatch $frames $packets)) $published)"
    "$packets"

def control (label : String) (plan : GeneralExecutionAdmission.Plan) (source : Pattern)
    (work first expectedPackets expectedKeys expectedFacts : Nat) : IO String := do
  let environment := GeneralPlanEnvironment.environment plan
  let footprint := source.freeFvarNames ++ providerFreeNames environment.provider
  let names := CanonicalCompare.nameTable
    (StructuralDescent.Scheduled.NameSupport.environmentNameTable environment footprint ++
      CanonicalCompare.names source)
  let planWire := CollectionOccurrenceSearchExecution.Interpreted.interpretedPlanTerm
    names plan footprint [] graphType
  let finish : Publication EquationalScopedReceipts.Event →
      Option (GeneralRuleJobs.Receipt EquationalScopedReceipts.Event) :=
    fun packet => packet.finishCanonical? plan [] graphType
  let run := CollectionOccurrenceSearch.runWith plan [] graphType
    (fun input => canonicalSeedProfile plan [] graphType input) 0 source work
  let committed := CollectionOccurrenceSearch.committedWith finish run
  let keys := orderedCommittedKeys logicalKey committed
  let bag := keys.filterMap logicalEdge?
  let facts := bag.eraseDups
  unless run.state.batch.log.length == expectedPackets && committed.length == expectedPackets &&
      keys.length == expectedKeys && facts.length == expectedFacts &&
      CollectionOccurrenceSearch.statusWith run == .complete do
    throw (IO.userError s!"Graph producer {label} has the wrong independent packet/key/fact account")
  let choice := RecursiveCollectionExecution.eventTerm
  let packetWire := encodeList (CollectionOccurrenceBatchExecution.publicationTermWith choice) run.state.batch.log
  let pairWire := encodeList (CollectionOccurrenceBatchExecution.committedTermWith choice) committed
  let receiptWire := encodeList (ScopedRuleJobReadoutExecution.receiptTermWith choice)
    (CollectionOccurrenceSearch.publicationWith finish run)
  let wire := CollectionOccurrenceSearchExecution.runTermWith
    RetainedMatchingWire.canonicalCodec planWire finish run
  pure (CollectionRunnerControls.measurement ("graph-" ++ label) source work first
      run.state.batch.frames.length run.state.batch.log.length environment.provider.rows.length ++
    "!" ++ letStar
    [("$names", quoted (encodeList Term.string names)), ("$plan", quoted planWire),
     ("$source", quoted (InferenceCettaWire.encodePattern source)),
     ("$selected", quoted (encodeList Term.string ["x", "y", "z"])),
     ("$wrong", quoted (InferenceCettaWire.encodePattern (edge "Z" "A"))),
     ("$actual", call "gslt:occurrence-search:run" ["$names", "0", "$plan", "$source", toString work]),
     ("$middle", call "gslt:occurrence-search:run" ["$names", "0", "$plan", "$source", toString first]),
     ("$resumed", call "gslt:occurrence-search:resume" ["$names", "0", "$middle", toString (work - first)]),
     ("$packets", packets "$actual"),
     ("$pairs", call "gslt:occurrence-search:read-committed" ["$plan", "$packets"]),
     ("$receipts", call "gslt:occurrence-search:publication" ["$actual"]),
     ("$keys", call "gslt:occurrence-search:key-unique" ["$names", "$selected", "$pairs"]),
     ("$bag", call "gslt:occurrence-search:key-bag" ["$names", "$selected", "\"Edge\"", "$pairs"]),
     ("$facts", call "gslt:occurrence-search:key-facts" ["$names", "$selected", "\"Edge\"", "$pairs"]),
     ("$twice", call "gslt:automata:append" ["$pairs", "$pairs"]),
     ("$replayed-keys", call "gslt:occurrence-search:key-unique" ["$names", "$selected", "$twice"]),
     ("$replayed-bag", call "gslt:occurrence-search:key-bag" ["$names", "$selected", "\"Edge\"", "$twice"]),
     ("$replayed-facts", call "gslt:occurrence-search:key-facts" ["$names", "$selected", "\"Edge\"", "$twice"]),
     ("$packets-twice", call "gslt:automata:append" ["$packets", "$packets"]),
     ("$reread", call "gslt:occurrence-search:read-committed" ["$plan", "$packets-twice"]),
     ("$reread-keys", call "gslt:occurrence-search:key-unique" ["$names", "$selected", "$reread"])]
    (call "println!" [call "KnowledgeGraphProducerControl"
      [reprStr label,
       call "==" ["$actual", quoted wire],
       call "==" ["$resumed", "$actual"],
       call "==" ["$packets", quoted packetWire],
       call "==" ["$pairs", quoted pairWire],
       call "==" ["$keys", quoted (encodeList (logicalKeyTerm choice) keys)],
       call "==" ["$bag", quoted (encodeList InferenceCettaWire.encodePattern bag)],
       call "==" ["$facts", quoted (encodeList InferenceCettaWire.encodePattern facts)],
       call "==" ["$receipts", quoted receiptWire],
       call "==" [call "gslt:occurrence-search:status" ["$actual"], "SearchComplete"],
       call "==" [call "gslt:occurrence-search:status" ["$middle"], "SearchPending"],
       call "==" [call "gslt:automata:length" ["$packets"], toString expectedPackets],
       call "==" [call "gslt:automata:length" ["$pairs"], toString expectedPackets],
       call "==" [call "gslt:automata:length" ["$keys"], toString expectedKeys],
       call "==" [call "gslt:automata:length" ["$bag"], toString bag.length],
       call "==" [call "gslt:automata:length" ["$facts"], toString expectedFacts],
       call "==" [call "gslt:automata:member" ["$wrong", "$facts"], "False"],
       call "==" ["$replayed-keys", "$keys"],
       call "==" ["$replayed-bag", "$bag"],
       call "==" ["$replayed-facts", "$facts"],
       call "==" ["$reread", call "gslt:automata:append" ["$pairs", "$pairs"]],
       call "==" ["$reread-keys", "$keys"]]]))


private def invarianceHelpers : String := "(: kg-producer-control:packets (-> Atom %Undefined%))\n(= (kg-producer-control:packets (RecursiveOccurrenceRun $kg-plan $kg-source (RecursiveOccurrenceState $kg-lanes (RecursiveOccurrenceBatch $kg-frames $kg-packets)) $kg-published)) $kg-packets)\n" ++
  "(: kg-producer-control:ad-keys (-> Atom Atom %Undefined%))\n(= (kg-producer-control:ad-keys $wanted $keys)\n (case $keys ((LNil LNil) ((LCons $key $rest)\n  (let* (($conclusion (gslt:occurrence-search:key-binary \"Edge\" $key))\n         ($later (kg-producer-control:ad-keys $wanted $rest)))\n   (if (== $conclusion (Some $wanted)) (LCons $key $later) $later))))))\n(: kg-producer-control:subset (-> Atom Atom %Undefined%))\n(= (kg-producer-control:subset $left $right)\n (case $left ((LNil True) ((LCons $key $rest)\n  (if (gslt:automata:member $key $right) (kg-producer-control:subset $rest $right) False)))))\n(: kg-producer-control:source-sensitive-ad (-> Atom Atom Atom Atom %Undefined%))\n(= (kg-producer-control:source-sensitive-ad $table $selected $wanted $pairs)\n (case $pairs ((LNil LNil) ((LCons $pair $rest)\n  (let* (($key (gslt:occurrence-search:key-extract $table $selected $pair))\n         ($conclusion (gslt:occurrence-search:key-binary \"Edge\" $key))\n         ($later (kg-producer-control:source-sensitive-ad $table $selected $wanted $rest)))\n   (if (== $conclusion (Some $wanted))\n    (case $pair (((CommittedOccurrence\n      (RecursiveOccurrencePublication\n       (RecursiveCollectionOrigin (RuleJob $ordinal $declaration $site) $variant $answer) $continued) $receipt)\n       (LCons (SourceSensitiveKey $site $key) $later)))) $later))))))"

def invariance : IO String := do
  let sources := [("base", twoRouteSource),
    ("extended", irrelevantExtensionSource),
    ("conclusion-present", graph [edge "A" "B", edge "B" "D", edge "A" "C", edge "C" "D", edge "A" "D"]),
    ("reordered", reorderedDuplicateSource)]
  let environment := GeneralPlanEnvironment.environment twoRoutePlan
  let footprint := sources.flatMap (fun item => item.2.freeFvarNames) ++
    providerFreeNames environment.provider
  let names := CanonicalCompare.nameTable
    (StructuralDescent.Scheduled.NameSupport.environmentNameTable environment footprint ++
      sources.flatMap (fun item => CanonicalCompare.names item.2))
  let planWire := CollectionOccurrenceSearchExecution.Interpreted.interpretedPlanTerm
    names twoRoutePlan footprint [] graphType
  let mut bindings := [("$names", quoted (encodeList Term.string names)),
    ("$selected", quoted (encodeList Term.string ["x", "y", "z"])),
    ("$plan", quoted planWire), ("$wanted", quoted (InferenceCettaWire.encodePattern (edge "A" "D")))]
  for (tag, source) in sources ++ [("canonical", CanonicalBags.canon twoRouteSource)] do
    let finish : Publication EquationalScopedReceipts.Event →
        Option (GeneralRuleJobs.Receipt EquationalScopedReceipts.Event) :=
      fun packet => packet.finishCanonical? twoRoutePlan [] graphType
    let model := CollectionOccurrenceSearch.runWith twoRoutePlan [] graphType
      (fun input => canonicalSeedProfile twoRoutePlan [] graphType input) 0 source 1600
    let keys := orderedCommittedKeys logicalKey (CollectionOccurrenceSearch.committedWith finish model)
    unless (keys.filter (fun key => logicalEdge? key == some (edge "A" "D"))).length == 2 do
      throw (IO.userError s!"Graph invariance source {tag} lost an independent route")
    bindings := bindings ++
      [("$source-" ++ tag, if tag == "canonical" then
          call "gslt:canon:canon" ["$names", "$source-base"]
        else quoted (InferenceCettaWire.encodePattern source)),
       ("$run-" ++ tag, call "gslt:occurrence-search:run"
         ["$names", "0", "$plan", "$source-" ++ tag, "1600"]),
       ("$packets-" ++ tag, call "kg-producer-control:packets" ["$run-" ++ tag]),
       ("$pairs-" ++ tag, call "gslt:occurrence-search:read-committed" ["$plan", "$packets-" ++ tag]),
       ("$keys-" ++ tag, call "gslt:occurrence-search:key-unique" ["$names", "$selected", "$pairs-" ++ tag]),
       ("$ad-" ++ tag, call "kg-producer-control:ad-keys" ["$wanted", "$keys-" ++ tag])]
  bindings := bindings ++
    [("$all-ad-1", call "gslt:automata:append" ["$ad-base", "$ad-extended"]),
     ("$all-ad-2", call "gslt:automata:append" ["$all-ad-1", "$ad-conclusion-present"]),
     ("$all-ad-3", call "gslt:automata:append" ["$all-ad-2", "$ad-reordered"]),
     ("$all-ad-4", call "gslt:automata:append" ["$all-ad-3", "$ad-canonical"]),
     ("$unique-ad", call "gslt:automata:unique" ["$all-ad-4"]),
     ("$sensitive-base", call "kg-producer-control:source-sensitive-ad"
       ["$names", "$selected", "$wanted", "$pairs-base"]),
     ("$sensitive-extended", call "kg-producer-control:source-sensitive-ad"
       ["$names", "$selected", "$wanted", "$pairs-extended"]),
     ("$sensitive-combined", call "gslt:automata:append" ["$sensitive-base", "$sensitive-extended"]),
     ("$sensitive-unique", call "gslt:automata:unique" ["$sensitive-combined"])]
  let mut checks := []
  for tag in ["base", "extended", "conclusion-present", "reordered", "canonical"] do
    checks := checks ++ [call "==" [call "gslt:automata:length" ["$ad-" ++ tag], "2"]]
    if tag != "base" then
      checks := checks ++
        [call "==" [call "kg-producer-control:subset" ["$ad-" ++ tag, "$ad-base"], "True"],
         call "==" [call "kg-producer-control:subset" ["$ad-base", "$ad-" ++ tag], "True"]]
  checks := checks ++
    [call "==" [call "gslt:automata:length" ["$unique-ad"], "2"],
     call "==" [call "gslt:automata:length" ["$sensitive-unique"], "4"]]
  pure ("!" ++ letStar bindings
    (call "println!" [call "KGProducerInvarianceControl"
      (reprStr "source-presentation-and-extension-invariance" :: checks)]))

def main : IO Unit := do
  IO.println invarianceHelpers
  for (label, plan, source, work, first, raw, keys, facts) in [
      ("two-independent-routes", twoRoutePlan, twoRouteSource, 800, 3, 8, 2, 1),
      ("guard-absent", guardedTwoRoutePlan 0, twoRouteSource, 800, 3, 0, 0, 0),
      ("guard-one-validation", guardedTwoRoutePlan 1, twoRouteSource, 800, 3, 8, 2, 1),
      ("guard-duplicate-validation", guardedTwoRoutePlan 2, twoRouteSource, 800, 3, 16, 2, 1),
      ("missing-second-edge", twoRoutePlan, graph [edge "A" "B"], 200, 0, 0, 0, 0),
      ("wrong-conclusion", twoRoutePlan, graph [edge "A" "B", edge "B" "C"], 400, 3, 4, 1, 1),
      ("cyclic-source", twoRoutePlan, graph [edge "A" "B", edge "B" "A", edge "B" "C"], 1200, 3, 12, 3, 3),
      ("irrelevant-source-extension", twoRoutePlan, irrelevantExtensionSource, 1600, 3, 18, 5, 4),
      ("reordered-duplicate-source", twoRoutePlan, reorderedDuplicateSource, 800, 3, 8, 2, 1),
      ("canonical-source-presentation", twoRoutePlan, CanonicalBags.canon twoRouteSource, 800, 3, 8, 2, 1)] do
    IO.println (← control label plan source work first raw keys facts)
  IO.println (← invariance)

end KnowledgeGraphProducerControls
#eval KnowledgeGraphProducerControls.main

namespace NativeKGObservationControls
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionCommittedObservation CollectionOccurrenceBatch CanonicalBags
open Mettapedia.GSLT.LanguageDef.CollectionConsumers
open Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open CollectionExecutionQualification.GraphObservation

def pairs (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) :=
  retained plan [] (.base "Graph") packets

def aToD (xs : List Committed) : List Committed :=
  xs.filter fun pair => logicalEdge? (logicalKey pair) == some (edge "A" "D")

def choiceTerm := RuleInstantiationExecution.GeneralExecution.bagChoiceTerm

def render (label : String) (committed : List Committed) : String := Id.run do
  let raw := encodeList (CollectionOccurrenceBatchExecution.committedTermWith choiceTerm) committed
  let keys := orderedCommittedKeys logicalKey committed
  let expectedKeys := encodeList (logicalKeyTerm choiceTerm) keys
  let bag := keys.filterMap logicalEdge?
  let expectedBag := encodeList InferenceCettaWire.encodePattern bag
  let expectedFacts := encodeList InferenceCettaWire.encodePattern bag.eraseDups
  let table := encodeList Term.string ["A","B","C","D","Edge","Graph"]
  let selected := encodeList Term.string ["x","y","z"]
  let wrong := InferenceCettaWire.encodePattern (edge "Z" "A")
  return "!(println! (let* (($pairs (quote " ++ raw.render ++ ")) ($table (quote " ++ table.render ++
    ")) ($selected (quote " ++ selected.render ++ ")) ($expectedKeys (quote " ++ expectedKeys.render ++
    ")) ($expectedBag (quote " ++ expectedBag.render ++ ")) ($expectedFacts (quote " ++ expectedFacts.render ++
    ")) ($wrong (quote " ++ CettaWire.Term.render wrong ++ "))" ++
    " ($keys (gslt:occurrence-search:key-unique $table $selected $pairs))" ++
    " ($bag (gslt:occurrence-search:key-bag $table $selected \"Edge\" $pairs))" ++
    " ($facts (gslt:occurrence-search:key-facts $table $selected \"Edge\" $pairs))" ++
    " ($twice (gslt:automata:append $pairs $pairs))" ++
    " ($replayed (gslt:occurrence-search:key-unique $table $selected $twice)))" ++
    " (KGDeclaredKeyControl " ++ reprStr label ++
    " (== $keys $expectedKeys) (== $bag $expectedBag) (== $facts $expectedFacts)" ++
    " (== (gslt:automata:length $keys) " ++ toString keys.length ++ ")" ++
    " (== (gslt:automata:length $bag) " ++ toString bag.length ++ ")" ++
    " (== (gslt:automata:length $facts) " ++ toString bag.eraseDups.length ++ ")" ++
    " (== $replayed $keys) (== (gslt:automata:member $wrong $facts) False)" ++
    " (== (gslt:automata:length $pairs) " ++ toString committed.length ++ "))))"

def main : IO Unit := do
  let route := pairs twoRoutePlan twoRouteFinished.batch.log
  IO.println (render "two-independent-routes" route)
  IO.println (render "duplicate-validation-one" (pairs (guardedTwoRoutePlan 1) (guardedTwoRouteFinished 1).batch.log))
  IO.println (render "duplicate-validation-two" (pairs (guardedTwoRoutePlan 2) (guardedTwoRouteFinished 2).batch.log))
  IO.println (render "cyclic-prefix" (pairs reachabilityPlan finishedDiamond.batch.log))
  IO.println (render "source-extension-relevant-fact" (aToD (pairs twoRoutePlan irrelevantExtensionFinished.batch.log)))
  IO.println (render "reordered-duplicate-source" (aToD (pairs twoRoutePlan reorderedDuplicateFinished.batch.log)))
  IO.println (render "canonical-source-presentation" (aToD (pairs twoRoutePlan canonicalSourceFinished.batch.log)))
  IO.println (render "source-extension-full-prefix" (pairs twoRoutePlan irrelevantExtensionFinished.batch.log))
  IO.println (render "reordered-source-full-prefix" (pairs twoRoutePlan reorderedDuplicateFinished.batch.log))
  IO.println (render "canonical-source-full-prefix" (pairs twoRoutePlan canonicalSourceFinished.batch.log))
  let missing := CollectionOccurrenceMachine.run 0 160
    (CollectionOccurrenceMachine.begin reachabilityPlan [] (.base "Graph") (graph [edge "A" "B"]))
  IO.println (render "missing-second-edge" (pairs reachabilityPlan missing.batch.log))
  IO.println (render "replayed-retained-pairs" (route ++ route))
  match (orderedCommittedKeys logicalKey route).head? with
  | none => throw (IO.userError "actual graph source produced no logical route")
  | some key =>
    let missingKey := logicalKeyTerm choiceTerm {key with first := none}
    IO.println ("!(println! (let $key (quote " ++ missingKey.render ++
      ") (KGDeclaredKeyNegative \"missing-first-conclusion\" (== (gslt:occurrence-search:key-binary \"Edge\" $key) None))))")
    IO.println "!(println! (let $key (quote (WrongDeclaredFiringKey)) (KGDeclaredKeyNegative \"wrong-key-constructor\" (== (gslt:occurrence-search:key-binary \"Edge\" $key) None))))"

#eval main
end NativeKGObservationControls

namespace FiniteExplorerControls

open CollectionRunnerControls (call letStar select)
open NestedContinuationControls (quoted)
open CollectionConsumers
open CollectionConsumers.Controls.Observation.GraphControls

def control (label : String) (plan : GeneralExecutionAdmission.Plan) (source : Pattern)
    (work nodeCount edgeCount : Nat) (rawSeed : Bool := false) : IO String := do
  let search := CollectionOccurrenceSearch.search plan [] (.base "Graph") 0
  let names := StandardWire.planTable plan []
  let standard := Term.application "Canonical"
    [.symbol "LNil", .symbol "LNil", encodeList Term.string names]
  let backend := CompleteExecution.CollectionOccurrence.backendTerm names 0
  let planWire := CompletePlanWire.planTerm plan [] [] (.base "Graph")
  let prepared := if rawSeed then source else CanonicalBags.canon source
  let initial := Complete.Explore.begin search prepared
  let middle := Complete.Settled.roundsUntilSettled search 3 initial
  let whole := Complete.Settled.roundsUntilSettled search work initial
  let graphEdges := Complete.Graph.edges search whole
  unless Complete.Settled.settled search whole && whole.nodes.length == nodeCount &&
      graphEdges.length == edgeCount do
    throw (IO.userError s!"Finite explorer {label} has the wrong settled node/edge account")
  let explorerWire := CompleteExecution.SearchWire.explorerTerm
    (CollectionOccurrenceSearchExecution.runTerm []) ScopedRuleJobReadoutExecution.receiptTerm
  let frames := (whole.nodes.map fun node => node.run.state.batch.frames.length).sum
  let publications := (whole.nodes.map fun node => (search.publication node.run).length).sum
  let nativeInitial := if rawSeed then
      letStar [("$raw-run", call "gslt:search:run" ["$backend", "$plan", "$source", "0"])]
        "(Explorer 0 (LCons (ExploreNode $source LNil (LCons $source LNil) 0 $raw-run 0) LNil))"
    else call "gslt:explore:begin" ["$backend", "$plan", "$standard", "$source"]
  pure (CollectionRunnerControls.measurement ("explorer-" ++ label) prepared work 3
    frames publications plan.snapshot.provider.rows.length ++ "!" ++ letStar
    [("$backend", quoted backend), ("$standard", quoted standard), ("$plan", quoted planWire),
     ("$source", quoted (InferenceCettaWire.encodePattern source)),
     ("$initial", nativeInitial),
     ("$middle", call "gslt:explore:rounds" ["$backend", "$plan", "$standard", "3", "$initial"]),
     ("$whole", call "gslt:explore:rounds" ["$backend", "$plan", "$standard", toString work, "$initial"]),
     ("$resumed", call "gslt:explore:rounds" ["$backend", "$plan", "$standard", toString (work - 3), "$middle"]),
     ("$later", call "gslt:explore:rounds" ["$backend", "$plan", "$standard", "50", "$whole"]),
     ("$nodes", select "$whole" "(Explorer $round $nodes)" "$nodes"),
     ("$settled", call "gslt:explore:settled" ["$backend", "$plan", "$nodes"]),
     ("$states", call "gslt:explore:states" ["$whole"]),
     ("$edges", call "gslt:explore:edges" ["$backend", "$standard", "$whole"])]
    (call "println!" [call "FiniteExplorerControl"
      [reprStr label,
       call "==" ["$middle", quoted (explorerWire middle)],
       call "==" ["$whole", quoted (explorerWire whole)],
       call "==" ["$resumed", "$whole"],
       call "==" ["$settled", "True"],
       call "==" ["$later", "$whole"],
       call "==" ["$states", quoted (encodeList InferenceCettaWire.encodePattern (whole.nodes.map (·.state)))],
       call "==" ["$edges", quoted (encodeList
         (CompleteExecution.SearchWire.edgeTerm ScopedRuleJobReadoutExecution.receiptTerm) graphEdges)],
       call "==" [call "gslt:automata:length" ["$states"], toString nodeCount],
       call "==" [call "gslt:automata:length" ["$edges"], toString edgeCount]]]))

def main : IO Unit := do
  IO.println (← control "self-cycle" reachabilityPlan (graph [edge "A" "A"]) 37 1 2)
  -- The native entry prepares canonical seeds. The generic explorer can also
  -- retain a raw seed alongside canonical successors from the same search.
  IO.println (← control "closed-diamond" reachabilityPlan (CanonicalBags.canon diamond) 703 1 14)
  IO.println (← control "raw-diamond-presentation" reachabilityPlan diamond 1406 2 28 true)
  IO.println (← control "two-route-closure" twoRoutePlan twoRouteSource 1081 2 16)

end FiniteExplorerControls
#eval FiniteExplorerControls.main

namespace NativeConstructorControls

open CollectionRunnerControls (call letStar)
open NestedContinuationControls (quoted)
open CollectionPresentationExecution.ConstructorTyping
open CollectionPresentationExecution.ConstructorTyping.Controls
open BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView
open InferenceCettaWire.AuthoredRule (typeTerm typingDeclarationTerm)

def control (label : String) (sourceLanguage : LanguageDef)
    (schemaBound : List TypeExpr) (focus : Focus) (head : String)
    (schemas sources : List Pattern) (row : GrammarRule) (expected : Bool) : IO String := do
  let parameters := { Controls.parameters with language := sourceLanguage }
  unless Retained.constructorReady parameters schemaBound focus head schemas sources row == expected do
    throw (IO.userError s!"Constructor readiness control {label} has the wrong source verdict")
  let bindings :=
    [("$sorts", quoted (PremiseOperationsExecution.RestSchema.sortsTerm parameters.language)),
      ("$declarations", quoted (PremiseOperationsExecution.RestSchema.declarationsTerm parameters.language)),
      ("$free", quoted (PremiseOperationsExecution.RestSchema.freeTerm [])),
      ("$schema-free", quoted (PremiseOperationsExecution.RestSchema.freeTerm schemaContext)),
      ("$schema-bound", quoted (encodeList typeTerm schemaBound)),
      ("$bound", quoted (encodeList typeTerm focus.bound)),
      ("$expected", quoted (typeTerm (focus.expected parameters.category))),
      ("$label", quoted (.string head)),
      ("$schemas", quoted (encodeList InferenceCettaWire.encodePattern schemas)),
      ("$sources", quoted (encodeList InferenceCettaWire.encodePattern sources)),
      ("$row", quoted (typingDeclarationTerm row))]
  pure ("!" ++ letStar bindings
    (call "println!" [call "ConstructorTypingControl" [reprStr label,
      call "==" [call "gslt:collection-presentation:view-constructor-ready" (bindings.map (·.1)),
        if expected then "True" else "False"]]]))

def main : IO Unit := do
  IO.println (← control "ordinary-row" language [] (focus []) "Box"
    [.fvar "x"] [.apply "Atom" []] constructorRow true)
  IO.println (← control "separate-bound-contexts" language [valueType] (focus [valueType]) "Box"
    [.bvar 0] [.bvar 0] constructorRow true)
  IO.println (← control "wrong-schema-binder-type" language [.arrow valueType valueType] (focus [valueType]) "Box"
    [.bvar 0] [.bvar 0] constructorRow false)
  IO.println (← control "wrong-target-binder-type" language [valueType] (focus [.arrow valueType valueType]) "Box"
    [.bvar 0] [.bvar 0] constructorRow false)
  IO.println (← control "schema-context-is-not-target-context" language [] (focus []) "Box"
    [.fvar "x"] [.fvar "x"] constructorRow false)
  IO.println (← control "wrapped-collection-with-rest" language [] (focus []) "BagBox"
    [.collection .hashBag [] (some "rest")]
    [.collection .hashBag [.apply "Atom" [],.apply "Atom" []] none] (bagRow .wrapped) true)
  IO.println (← control "bare-carrier-is-not-a-wrapper" language [] (focus []) "BagBox"
    [.collection .hashBag [] (some "rest")]
    [.collection .hashBag [.apply "Atom" [],.apply "Atom" []] none] (bagRow .bare) false)
  IO.println (← control "row-fit-does-not-grant-membership" undeclaredParameters.language [] (focus []) "Box"
    [.fvar "x"] [.apply "Atom" []] constructorRow true)

end NativeConstructorControls
#eval NativeConstructorControls.main
