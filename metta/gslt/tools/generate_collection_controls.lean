import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionCodec
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachineControls
import Mettapedia.GSLT.LanguageDef.CettaWireEquality
import Mettapedia.GSLT.LanguageDef.CollectionConsumers
import Mettapedia.GSLT.LanguageDef.CollectionConsumerControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPlanExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionMatcherBackendExecution

/-! Generate exact allocation, suspension and receipt expectations from Lean. -/

open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionSelection ScopedCollectionMachine
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open CollectionSelectionExecution (allocationTerm decisionTerm pairTerm booleanTerm)
open ScopedCollectionExecution (requestTerm stateTerm receiptTerm)
open ScopedCollectionExecution (firingTerm)
open CollectionPlanExecution (requestEntryTerm planStateTerm planFiringTerm)
open CollectionMatcherBackendExecution (rawOrdinaryTarget rawOrdinaryRequest backendAnswers)
open CompleteExecution.DescentCodec
open ScopedCollectionMatching.Controls (a b twoVariables repeatedVariable rule spec)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

mutual
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

def assertion (label : String) (bindings : List (String × String)) (actual : String)
    (expected : Term) : String :=
  "!(let* (" ++ String.intercalate "\n    " (bindings.map fun (name, code) => "(" ++ name ++ " " ++ code ++ ")") ++
    "\n    ($actual " ++ actual ++ "))\n  (println! (CollectionControl " ++ reprStr label ++
      " (== $actual (quote " ++ expected.render ++ ")))))"

def quoted (term : Term) : String := "(quote " ++ term.render ++ ")"

def allocationControl (label : String) (mode : Bool) (count : Nat) (items : List Pattern) : String :=
  assertion label [("$items", quoted (CettaWire.encodeList encodePattern items))]
    ("(gslt:collection:allocate " ++ (booleanTerm mode).render ++ " " ++ toString count ++ " $items)")
    (CettaWire.encodeList (allocationTerm encodePattern) (tracedAllocations mode count items))

def replayControl (label : String) (mode : Bool) (items : List Pattern) (decisions : List Decision) : String :=
  assertion label [("$items", quoted (CettaWire.encodeList encodePattern items)),
      ("$decisions", quoted (CettaWire.encodeList decisionTerm decisions))]
    ("(gslt:collection:replay " ++ (booleanTerm mode).render ++ " $items $decisions)")
    (encodeOption (pairTerm encodePattern) (replay mode items decisions))

def request (kind : CollType) (schemas : List Pattern) (rest : Option String)
    (targets : List Pattern) : Request :=
  { rule := rule kind schemas rest, spec, ambient := 0, site := .left,
    path := [], depth := 0, index := 0, initial := [], schemas, rest, kind, targets }

def batchControls (label : String) (query : Request) : List String :=
  let initial := rawStart query
  let interrupted := resume query 1 initial
  let finished := resume query 30 initial
  let base := [("$request", quoted (requestTerm query)),
    ("$initial", "(gslt:collection-machine:start $request)")]
  [ assertion (label ++ "-start") base "$initial" (stateTerm initial)
  , assertion (label ++ "-interrupted") base "(gslt:collection-machine:resume $request 1 $initial)"
      (stateTerm interrupted)
  , assertion (label ++ "-finished") base "(gslt:collection-machine:resume $request 30 $initial)"
      (stateTerm finished)
  , assertion (label ++ "-resumed")
      (base ++ [("$partial", "(gslt:collection-machine:resume $request 1 $initial)")])
      "(gslt:collection-machine:resume $request 29 $partial)" (stateTerm finished)
  , assertion (label ++ "-initial-complete") base "(gslt:collection-machine:complete $initial)"
      (booleanTerm (complete initial))
  , assertion (label ++ "-finished-complete")
      (base ++ [("$finished", "(gslt:collection-machine:resume $request 30 $initial)")])
      "(gslt:collection-machine:complete $finished)" (booleanTerm (complete finished))
  , assertion (label ++ "-full-receipts")
      (base ++ [("$finished", "(gslt:collection-machine:resume $request 30 $initial)")])
      "(gslt:collection-machine:publication $finished)"
      (CettaWire.encodeList receiptTerm (publication finished))
  , assertion (label ++ "-full-firings")
      (base ++ [("$finished", "(gslt:collection-machine:resume $request 30 $initial)"),
        ("$receipts", "(gslt:collection-machine:publication $finished)")])
      "(gslt:collection-machine:firings $request $receipts)"
      (CettaWire.encodeList firingTerm (firings query finished)) ]

def backendControls (label : String) (query : Request) : List String :=
  let finished := resume query 30 (rawStart query)
  (publication finished).zipIdx.flatMap fun (receipt, index) =>
    let suffix := label ++ "-backend-" ++ toString index
    let target := rawOrdinaryTarget query receipt
    let ordinary := rawOrdinaryRequest query receipt
    let assignment := receipt.matching.assignment
    let targetBindings :=
      [("$kind", quoted (encodeCollectionType query.kind)),
       ("$values", quoted (CettaWire.encodeList encodePattern receipt.allocation.values)),
       ("$residual", quoted (CettaWire.encodeList encodePattern receipt.allocation.residual))]
    let requestBindings :=
      [("$rule", quoted (InferenceCettaWire.AuthoredRule.rewriteTerm query.rule)),
       ("$spec", quoted (InferenceCettaWire.AuthoredRule.bindingSpecTerm query.spec)),
       ("$ambient", toString query.ambient),
       ("$site", quoted (InferenceCettaWire.AuthoredRule.siteTerm query.site)),
       ("$path", quoted (CettaWire.encodeList Term.natural query.path)),
       ("$depth", toString query.depth),
       ("$initial", quoted
          (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm query.initial)),
       ("$schema", quoted (encodePattern query.rule.left)),
       ("$target", quoted (encodePattern target))]
    let answerBindings :=
      [("$request", quoted
          (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm ordinary)),
       ("$assignment", quoted
          (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment))]
    [ assertion (suffix ++ "-target") targetBindings
        "(gslt:collection-backend:ordinary-target $kind $values $residual)"
        (encodePattern target)
    , assertion (suffix ++ "-request") requestBindings
        "(gslt:collection-backend:ordinary-request $rule $spec $ambient $site $path $depth $initial $schema $target)"
        (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm ordinary)
    , assertion (suffix ++ "-answers") answerBindings
        "(gslt:collection-backend:answers $request $assignment)"
        (CettaWire.encodeList RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
          (backendAnswers query receipt)) ]

def continuationControl (label : String) (environment : GeneralPremise.Environment)
    (type : TypeExpr) (firing : CollectionPlanMachine.Firing)
    (goal : StructuralDescent.Scheduled.Goal)
    (handoff : GeneralPremise.Scheduler.Expansion
      (StructuralDescent.Scheduled.Task environment goal)
      (StructuralDescent.Scheduled.Result environment goal)
      StructuralDescent.Scheduled.Obligation) : String :=
  let source := CollectionMatcherCompatibility.ordinaryTarget firing.request firing.receipt.source
  let ordinary := rawOrdinaryRequest firing.request firing.receipt.source
  let tail : StructuralDescent.Scheduled.Continuation environment goal goal := .done goal
  let next : List (StructuralDescent.Scheduled.Task environment goal) := []
  let bindings :=
    [("$environment", quoted
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
          (environment.free.entriesOn []))),
     ("$bound", quoted (CettaWire.encodeList InferenceCettaWire.AuthoredRule.typeTerm [])),
     ("$type", quoted (InferenceCettaWire.AuthoredRule.typeTerm type)),
     ("$source", quoted (encodePattern source)),
     ("$rule", quoted (InferenceCettaWire.AuthoredRule.rewriteTerm firing.request.rule)),
     ("$spec", quoted (InferenceCettaWire.AuthoredRule.bindingSpecTerm firing.request.spec)),
     ("$request", quoted
        (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm ordinary)),
     ("$assignment", quoted
        (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
          firing.receipt.source.matching.assignment)),
     ("$tail", quoted (continuationTerm tail)),
     ("$next", quoted (CettaWire.encodeList taskTerm next))]
  assertion label bindings
    ("(let $answers (gslt:collection-backend:answers $request $assignment) " ++
      "(gslt:collection-backend:continue-answers $environment 0 $bound $type $source " ++
      toString firing.ordinal ++ " $rule $spec $answers $tail $next))")
    (encodeOption expansionTerm (some handoff))

def petriContinuationControl : String :=
  continuationControl "petri-generic-continuation"
    CollectionConsumers.Controls.petriEnvironment (.base "Marking")
    CollectionConsumers.Controls.petriFirstFiring
    CollectionConsumers.Controls.petriHandoffGoal
    CollectionConsumers.Controls.petriHandoff

def graphContinuationControl : String :=
  continuationControl "graph-generic-continuation"
    CollectionConsumers.Controls.graphEnvironment (.base "Graph")
    CollectionConsumers.Controls.graphFirstFiring
    CollectionConsumers.Controls.graphHandoffGoal
    CollectionConsumers.Controls.graphHandoff

def scheduledControl (label : String) (environment : GeneralPremise.Environment)
    (type : TypeExpr) (firing : CollectionPlanMachine.Firing)
    (goal : StructuralDescent.Scheduled.Goal)
    (run : StructuralDescent.Scheduled.State environment goal) : String :=
  let source := CollectionMatcherCompatibility.ordinaryTarget firing.request firing.receipt.source
  let ordinary := rawOrdinaryRequest firing.request firing.receipt.source
  let tail : StructuralDescent.Scheduled.Continuation environment goal goal := .done goal
  let next : List (StructuralDescent.Scheduled.Task environment goal) := []
  let bindings :=
    [("$environment", quoted
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
          (environment.free.entriesOn []))),
     ("$bound", quoted (CettaWire.encodeList InferenceCettaWire.AuthoredRule.typeTerm [])),
     ("$type", quoted (InferenceCettaWire.AuthoredRule.typeTerm type)),
     ("$source", quoted (encodePattern source)),
     ("$rule", quoted (InferenceCettaWire.AuthoredRule.rewriteTerm firing.request.rule)),
     ("$spec", quoted (InferenceCettaWire.AuthoredRule.bindingSpecTerm firing.request.spec)),
     ("$request", quoted
        (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm ordinary)),
     ("$assignment", quoted
        (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
          firing.receipt.source.matching.assignment)),
     ("$tail", quoted (continuationTerm tail)),
     ("$next", quoted (CettaWire.encodeList taskTerm next))]
  assertion label bindings
    ("(let* (($answers (gslt:collection-backend:answers $request $assignment)) " ++
      "($expanded (gslt:collection-backend:continue-answers $environment 0 $bound $type $source " ++
      toString firing.ordinal ++ " $rule $spec $answers $tail $next)) " ++
      "($state (gslt:collection-backend:expansion-state $expanded))) " ++
      "(gslt:descent:run $environment 20 $state))")
    (stateTerm run)

def petriScheduledControl : String :=
  scheduledControl "petri-generic-scheduled-run"
    CollectionConsumers.Controls.petriEnvironment (.base "Marking")
    CollectionConsumers.Controls.petriFirstFiring
    CollectionConsumers.Controls.petriHandoffGoal
    CollectionConsumers.Controls.petriScheduledRun

def graphScheduledControl : String :=
  scheduledControl "graph-generic-scheduled-run"
    CollectionConsumers.Controls.graphEnvironment (.base "Graph")
    CollectionConsumers.Controls.graphFirstFiring
    CollectionConsumers.Controls.graphHandoffGoal
    CollectionConsumers.Controls.graphScheduledRun

def fixtures : List (String × Request) :=
  [ ("set-reuse", request .hashSet twoVariables (some "R") [a])
  , ("bag-origins", request .hashBag twoVariables (some "R") [a, a])
  , ("bag-reuse-refused", request .hashBag twoVariables (some "R") [a])
  , ("set-repeat", request .hashSet repeatedVariable none [a])
  , ("set-repeat-unequal-refused", request .hashSet repeatedVariable none [a, b])
  , ("set-empty", request .hashSet [] none [])
  , ("set-unmatched-refused", request .hashSet [] none [a])
  , ("wrong-context-refused",
      { request .hashSet [.fvar "X"] none [a] with initial := [("X", ⟨[], 1, a⟩)] })
  , ("wrong-path-refused",
      { request .hashSet twoVariables (some "R") [a] with path := [9] }) ] ++
  (CollectionConsumers.queries ++ CollectionConsumers.planQueries).filterMap fun (label, query) =>
    query.map fun selected => (label, selected)

def planFixtures : List (String × List (Nat × Request)) :=
  let petriSource : Pattern := .collection .hashBag
    [CollectionConsumers.token "A", CollectionConsumers.token "B"] none
  let graphSource : Pattern := .collection .hashSet
    [CollectionConsumers.edge "A" "B", CollectionConsumers.edge "B" "C"] none
  let petriRequests := CollectionExecutionAdmission.requestsForSource
    CollectionConsumers.petriPlan CollectionConsumers.petriCertificate petriSource
  let graphRequests := CollectionExecutionAdmission.requestsForSource
    CollectionConsumers.reachabilityPlan CollectionConsumers.reachabilityCertificate graphSource
  let duplicateOrigins := match petriRequests.head? with
    | some (_, request) => [(3, request), (7, request)]
    | none => []
  [ ("petri-plan", petriRequests)
  , ("reachability-plan", graphRequests)
  , ("duplicate-origin-plan", duplicateOrigins) ]

def planControls (label : String) (requests : List (Nat × Request)) : List String :=
  let initial := CollectionPlanMachine.start requests
  let interrupted := CollectionPlanMachine.resume 1 initial
  let finished := CollectionPlanMachine.resume 30 initial
  let base := [("$requests", quoted (CettaWire.encodeList requestEntryTerm requests)),
    ("$initial", "(gslt:collection-plan:start $requests)")]
  [ assertion (label ++ "-start") base "$initial" (planStateTerm initial)
  , assertion (label ++ "-interrupted") base
      "(gslt:collection-plan:resume 1 $initial)" (planStateTerm interrupted)
  , assertion (label ++ "-finished") base
      "(gslt:collection-plan:resume 30 $initial)" (planStateTerm finished)
  , assertion (label ++ "-resumed")
      (base ++ [("$partial", "(gslt:collection-plan:resume 1 $initial)")])
      "(gslt:collection-plan:resume 29 $partial)" (planStateTerm finished)
  , assertion (label ++ "-initial-complete") base
      "(gslt:collection-plan:complete $initial)"
      (booleanTerm (CollectionPlanMachine.complete initial))
  , assertion (label ++ "-finished-complete")
      (base ++ [("$finished", "(gslt:collection-plan:resume 30 $initial)")])
      "(gslt:collection-plan:complete $finished)"
      (booleanTerm (CollectionPlanMachine.complete finished))
  , assertion (label ++ "-firings")
      (base ++ [("$finished", "(gslt:collection-plan:resume 30 $initial)")])
      "(gslt:collection-plan:firings $finished)"
      (CettaWire.encodeList planFiringTerm (CollectionPlanMachine.publication finished)) ]

def controls : List String :=
  let allocate := [false, true].flatMap fun mode =>
    ([[], [a], [a, b], [a, a, b]] : List (List Pattern)).zipIdx |>.flatMap fun (items, index) =>
      (List.range 4).map fun count =>
        allocationControl s!"allocate-{mode}-{index}-{count}" mode count items
  let replayed := [false, true].flatMap fun mode =>
    ([[], [a], [a, b]] : List (List Pattern)).zipIdx |>.flatMap fun (items, index) =>
      ([[], [⟨0, false⟩], [⟨0, true⟩], [⟨9, false⟩],
        [⟨0, true⟩, ⟨0, false⟩], [⟨0, false⟩, ⟨0, false⟩]] : List (List Decision)).zipIdx |>.map
        fun (decisions, number) => replayControl s!"replay-{mode}-{index}-{number}" mode items decisions
  allocate ++ replayed ++ fixtures.flatMap (fun (label, query) => batchControls label query) ++
    fixtures.flatMap (fun (label, query) => backendControls label query) ++
    [petriContinuationControl, graphContinuationControl,
      petriScheduledControl, graphScheduledControl] ++
    planFixtures.flatMap fun (label, requests) => planControls label requests

def packets (label : String) (query : Request) : String :=
  "!(let* (($request " ++ quoted (requestTerm query) ++ ")\n" ++
    "    ($initial (gslt:collection-machine:start $request))\n" ++
    "    ($partial (gslt:collection-machine:resume $request 1 $initial)))\n" ++
    "  (println! (CollectionSnapshot " ++ reprStr label ++ " $partial)))\n" ++
  "!(let* (($request " ++ quoted (requestTerm query) ++ ")\n" ++
    "    ($initial (gslt:collection-machine:start $request))\n" ++
    "    ($finished (gslt:collection-machine:resume $request 30 $initial))\n" ++
    "    ($receipts (gslt:collection-machine:publication $finished)))\n" ++
    "  (println! (CollectionPacket " ++ reprStr label ++ " $receipts)))\n" ++
  "!(let* (($request " ++ quoted (requestTerm query) ++ ")\n" ++
    "    ($initial (gslt:collection-machine:start $request))\n" ++
    "    ($finished (gslt:collection-machine:resume $request 30 $initial))\n" ++
    "    ($receipts (gslt:collection-machine:publication $finished))\n" ++
    "    ($firings (gslt:collection-machine:firings $request $receipts)))\n" ++
    "  (println! (CollectionFiringPacket " ++ reprStr label ++ " $firings)))"

def planPackets (label : String) (requests : List (Nat × Request)) : String :=
  "!(let* (($requests " ++ quoted (CettaWire.encodeList requestEntryTerm requests) ++ ")\n" ++
    "    ($initial (gslt:collection-plan:start $requests))\n" ++
    "    ($partial (gslt:collection-plan:resume 1 $initial)))\n" ++
    "  (println! (CollectionPlanSnapshot " ++ reprStr label ++ " $partial)))\n" ++
  "!(let* (($requests " ++ quoted (CettaWire.encodeList requestEntryTerm requests) ++ ")\n" ++
    "    ($initial (gslt:collection-plan:start $requests))\n" ++
    "    ($finished (gslt:collection-plan:resume 30 $initial))\n" ++
    "    ($firings (gslt:collection-plan:firings $finished)))\n" ++
    "  (println! (CollectionPlanPacket " ++ reprStr label ++ " $firings)))"

def readPackets (tag text : String) : IO (List (String × Term)) := do
  let mut packets := []
  for line in text.splitOn "\n" do
    if line.startsWith ("(" ++ tag ++ " ") then
      let atoms ← match SpaceSemantics.readSource line with
        | .ok atoms => pure atoms
        | .error error => throw (IO.userError error)
      match atoms with
      | [.expression [.symbol head, .grounded (.string label), atom]] =>
          if head != tag || packets.any (fun row => row.1 == label) then
            throw (IO.userError "Repeated or malformed collection packet")
          let some wire := decodeAtom? atom
            | throw (IO.userError "Collection packet is outside the wire carrier")
          packets := packets ++ [(label, wire)]
      | _ => throw (IO.userError "Malformed collection packet")
  pure packets

def generateResume (text : String) : IO String := do
  let snapshots ← readPackets "CollectionSnapshot" text
  if snapshots.map (·.1) != fixtures.map (·.1) then
    throw (IO.userError "Missing, extra or reordered runtime snapshots")
  let mut output := []
  for ((label, query), (_, snapshot)) in fixtures.zip snapshots do
    let expected := resume query 1 (rawStart query)
    if snapshot ≠ stateTerm expected then
      throw (IO.userError s!"Wrong complete runtime snapshot: {label}")
    let bindings := [("$request", quoted (requestTerm query)), ("$snapshot", quoted snapshot)]
    output := output ++ [assertion (label ++ "-returned-snapshot-resumed") bindings
      "(gslt:collection-machine:resume $request 29 $snapshot)"
      (stateTerm (resume query 30 (rawStart query)))]
    output := output ++ [
      "!(let* (($request " ++ quoted (requestTerm query) ++ ")\n" ++
        "    ($snapshot " ++ quoted snapshot ++ ")\n" ++
        "    ($finished (gslt:collection-machine:resume $request 29 $snapshot))\n" ++
        "    ($receipts (gslt:collection-machine:publication $finished)))\n" ++
        "  (println! (CollectionPacket " ++ reprStr (label ++ "-resumed") ++ " $receipts)))",
      "!(let* (($request " ++ quoted (requestTerm query) ++ ")\n" ++
        "    ($snapshot " ++ quoted snapshot ++ ")\n" ++
        "    ($finished (gslt:collection-machine:resume $request 29 $snapshot))\n" ++
        "    ($receipts (gslt:collection-machine:publication $finished))\n" ++
        "    ($firings (gslt:collection-machine:firings $request $receipts)))\n" ++
        "  (println! (CollectionFiringPacket " ++ reprStr (label ++ "-resumed") ++ " $firings)))"]
  let planSnapshots ← readPackets "CollectionPlanSnapshot" text
  if planSnapshots.map (·.1) != planFixtures.map (·.1) then
    throw (IO.userError "Missing, extra or reordered runtime plan snapshots")
  for ((label, requests), (_, snapshot)) in planFixtures.zip planSnapshots do
    let expected := CollectionPlanMachine.resume 1 (CollectionPlanMachine.start requests)
    if snapshot ≠ planStateTerm expected then
      throw (IO.userError s!"Wrong complete runtime plan snapshot: {label}")
    let bindings := [("$snapshot", quoted snapshot)]
    output := output ++ [assertion (label ++ "-returned-plan-snapshot-resumed") bindings
      "(gslt:collection-plan:resume 29 $snapshot)"
      (planStateTerm (CollectionPlanMachine.resume 30 (CollectionPlanMachine.start requests)))]
    output := output ++ [
      "!(let* (($snapshot " ++ quoted snapshot ++ ")\n" ++
        "    ($finished (gslt:collection-plan:resume 29 $snapshot))\n" ++
        "    ($firings (gslt:collection-plan:firings $finished)))\n" ++
        "  (println! (CollectionPlanPacket " ++ reprStr (label ++ "-resumed") ++ " $firings)))"]
  pure (String.intercalate "\n\n" output ++ "\n")

def checkPackets (text : String) : IO Unit := do
  let packets ← readPackets "CollectionPacket" text
  let firingPackets ← readPackets "CollectionFiringPacket" text
  let planPacketsReturned ← readPackets "CollectionPlanPacket" text
  let expectedFixtures := fixtures ++ fixtures.map fun (label, query) => (label ++ "-resumed", query)
  if packets.map (·.1) != expectedFixtures.map (·.1) then
    throw (IO.userError "Missing, extra or reordered collection receipt packets")
  if firingPackets.map (·.1) != expectedFixtures.map (·.1) then
    throw (IO.userError "Missing, extra or reordered collection firing packets")
  let expectedPlans := planFixtures ++ planFixtures.map fun (label, requests) =>
    (label ++ "-resumed", requests)
  if planPacketsReturned.map (·.1) != expectedPlans.map (·.1) then
    throw (IO.userError "Missing, extra or reordered collection plan packets")
  let mut checked : Nat := 0
  for ((label, query), (_, wire)) in expectedFixtures.zip packets do
    let some receipts := CettaWire.decodeList ScopedCollectionCodec.receipt? wire
      | throw (IO.userError s!"Malformed returned receipts: {label}")
    let expected := publication (resume query 30 (rawStart query))
    if wire ≠ CettaWire.encodeList receiptTerm expected then
      throw (IO.userError s!"Lost, added or altered source receipt: {label}")
    for receipt in receipts do
      if !checkReceipt query receipt then
        throw (IO.userError s!"Independent receipt replay refused: {label}")
      checked := checked + 1
  let mut checkedFirings : Nat := 0
  for ((label, query), (_, wire)) in expectedFixtures.zip firingPackets do
    let some returned := CettaWire.decodeList ScopedCollectionCodec.firing? wire
      | throw (IO.userError s!"Malformed returned firings: {label}")
    let expected := firings query (resume query 30 (rawStart query))
    if wire ≠ CettaWire.encodeList firingTerm expected then
      throw (IO.userError s!"Lost, added or altered source firing: {label}")
    for firing in returned do
      if !ScopedCollectionCodec.checkFiring query (firingTerm firing) then
        throw (IO.userError s!"Independent firing replay refused: {label}")
      checkedFirings := checkedFirings + 1
  for ((label, requests), (_, wire)) in expectedPlans.zip planPacketsReturned do
    let expected := CollectionPlanMachine.publication
      (CollectionPlanMachine.resume 30 (CollectionPlanMachine.start requests))
    if wire ≠ CettaWire.encodeList planFiringTerm expected then
      throw (IO.userError s!"Lost, added or altered plan firing: {label}")
  IO.println s!"Independently replayed {checked} receipts and {checkedFirings} firings in {packets.length} complete packets; checked {planPacketsReturned.length} plan packets"

def main (args : List String) : IO Unit := do
  match args with
  | [destination] =>
      IO.FS.writeFile destination
        ("; Generated expectations: collection allocations, scoped machine states and complete receipts.\n" ++
          String.intercalate "\n\n" (controls ++
            fixtures.map (fun (label, query) => packets label query) ++
            planFixtures.map fun (label, requests) => planPackets label requests) ++ "\n")
      IO.println s!"Collection controls: {controls.length}"
  | ["resume", input, destination] =>
      IO.FS.writeFile destination (← generateResume (← IO.FS.readFile input))
  | ["check", input] => checkPackets (← IO.FS.readFile input)
  | _ => throw (IO.userError "Expected OUTPUT, resume INPUT OUTPUT, or check INPUT")
