import Mettapedia.GSLT.LanguageDef.CollectionConsumers
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend

/-! End-to-end source controls for the two authored collection consumers. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls

open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine
open Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend
open CollectionConsumers

def completed? (request : Option Request) : Option (List Receipt) :=
  request.map fun query => publication (resume query 30 (start query))

def targets? (request : Option Request) : Option (List Pattern) := do
  let query ← request
  let receipts := publication (resume query 30 (start query))
  receipts.mapM fun receipt =>
    canon <$> reduct? query.rule query.spec query.ambient receipt.matching.assignment

def petriAB := petriRequest? 0 [token "A", token "B"]
def petriAAB := petriRequest? 0 [token "A", token "A", token "B"]
def petriMissing := petriRequest? 0 [token "A"]
def graphChain := reachabilityRequest? 0 [edge "A" "B", edge "B" "C"]
def graphLoop := reachabilityRequest? 0 [edge "A" "A"]
def graphMissing := reachabilityRequest? 0 [edge "A" "B", edge "A" "C"]

#guard (completed? petriAB).map List.length == some 1
#guard (completed? petriAAB).map List.length == some 2
#guard (completed? petriMissing).map List.length == some 0

#guard targets? petriAB == some [canon (.collection .hashBag [token "C", token "D"] none)]
#guard targets? petriAAB == some (List.replicate 2
  (canon (.collection .hashBag [token "C", token "D", token "A"] none)))

-- Four retention histories denote one set result; the histories remain
-- distinct receipts even though canonical targets coincide.
#guard (completed? graphChain).map List.length == some 4
#guard targets? graphChain == some (List.replicate 4
  (canon (.collection .hashSet [edge "A" "B", edge "B" "C", edge "A" "C"] none)))

-- Repeated selection is essential: one self-loop satisfies both premises.
#guard (completed? graphLoop).map List.length == some 2
#guard targets? graphLoop == some (List.replicate 2
  (canon (.collection .hashSet [edge "A" "A"] none)))

#guard (completed? graphMissing).map List.length == some 0

def petriSource : Pattern := .collection .hashBag [token "A", token "B"] none
def graphSource : Pattern := .collection .hashSet [edge "A" "B", edge "B" "C"] none

#guard (CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate petriSource).map Prod.fst == [0, 1]
#guard (CollectionExecutionAdmission.requestsForSource
  reachabilityPlan reachabilityCertificate graphSource).map Prod.fst == [0]
#guard (CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate (.apply "A" [])).isEmpty
#guard (CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate graphSource).isEmpty

def petriRequests := CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate petriSource

def graphRequests := CollectionExecutionAdmission.requestsForSource
  reachabilityPlan reachabilityCertificate graphSource

def completedPlanFirings (requests : List (Nat × Request)) :
    List CollectionPlanMachine.Firing :=
  CollectionPlanMachine.publication
    (CollectionPlanMachine.resume 30 (CollectionPlanMachine.start requests))

#guard (completedPlanFirings petriRequests).all
  (fun firing => !(adaptations firing).isEmpty)
#guard (completedPlanFirings graphRequests).all
  (fun firing => !(adaptations firing).isEmpty)

def duplicateOriginRequests : List (Nat × Request) :=
  match petriRequests.head? with
  | some (_, request) => [(3, request), (7, request)]
  | none => []

#guard (completedPlanFirings duplicateOriginRequests).map (·.ordinal) == [3, 7]

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls
