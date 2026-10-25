import Mettapedia.GSLT.LanguageDef.CollectionConsumers
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionLoggedSearchExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

namespace CollectionLoggedSearchControls

def render (term : Term) : String := term.render

def control (label : String) (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (expected : TypeExpr) (source : Pattern) (work : Nat) : String :=
  let requests := CollectionExecutionAdmission.requestsForSource plan certificate source
  let run := CollectionLoggedSearch.run plan certificate source work
  let planWire := CompletePlanWire.planTerm plan plan.snapshot.freeTypes [] expected
  let names := StandardWire.planTable plan []
  let backend := Term.application "CollectionSearch" [encodeList Term.string names]
  let requestsTerm := encodeList CollectionPlanExecution.requestEntryTerm requests
  let sourceTerm := InferenceCettaWire.encodePattern source
  let runTerm := CollectionLoggedSearchExecution.loggedRunTerm run
  let lanesTerm := encodeList CollectionLoggedSearchExecution.loggedLaneTerm run.state.lanes
  let logTerm := encodeList CollectionPlanExecution.planFiringTerm run.state.log
  let status := if CollectionLoggedSearch.complete run.state then "SearchComplete" else "SearchPending"
  "!(let* (($plan (quote " ++ render planWire ++ "))\n" ++
  "        ($backend (quote " ++ render backend ++ "))\n" ++
  "        ($requests (quote " ++ render requestsTerm ++ "))\n" ++
  "        ($source (quote " ++ render sourceTerm ++ "))\n" ++
  "        ($derived (gslt:collection-search:requests-for-source $plan $source))\n" ++
  "        ($run (gslt:search:run $backend $plan $source " ++ toString work ++ "))\n" ++
  "        ($lanes (quote " ++ render lanesTerm ++ "))\n" ++
  "        ($log (quote " ++ render logTerm ++ "))\n" ++
  "        ($published (gslt:search:publication $backend $run))\n" ++
  "        ($status (gslt:search:status $backend $plan $run))\n" ++
  "        ($started (gslt:search:run $backend $plan $source 0))\n" ++
  "        ($resumed (gslt:search:resume $backend $plan $started " ++ toString work ++ ")))\n" ++
  "  (println! (CollectionProfileControl " ++ reprStr label ++
    " (== $derived $requests) (== $run (quote " ++ render runTerm ++
    ")) (== $published $log) (== $status " ++ status ++
    ") (== $resumed $run))))"

def petriSource : Pattern :=
  CollectionConsumers.marking [CollectionConsumers.token "A", CollectionConsumers.token "B"]

def graphSource : Pattern :=
  CollectionConsumers.graph
    [CollectionConsumers.edge "A" "B", CollectionConsumers.edge "B" "C"]

def main : IO Unit := do
  IO.println "; Generated logged collection search controls."
  for work in [0, 1, 5, 20] do
    IO.println (control s!"petri-{work}" CollectionConsumers.petriPlan
      CollectionConsumers.petriCertificate (.base "Marking") petriSource work)
    IO.println (control s!"graph-{work}" CollectionConsumers.reachabilityPlan
      CollectionConsumers.reachabilityCertificate (.base "Graph") graphSource work)

end CollectionLoggedSearchControls

#eval CollectionLoggedSearchControls.main
