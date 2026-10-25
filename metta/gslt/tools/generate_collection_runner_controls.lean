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

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Machines.ResumableSearchRunner (Machine Search)

namespace CollectionRunnerControls

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
