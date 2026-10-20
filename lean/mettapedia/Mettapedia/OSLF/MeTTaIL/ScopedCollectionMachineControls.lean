import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMatchingControls

/-! Shared-engine suspension and occurrence controls for collection matching. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine.Controls

open Syntax CollectionSelection ScopedRuleMatching
open ScopedCollectionMatching.Controls

def request (kind : CollType) (targets : List Pattern) : Request :=
  { rule := rule kind twoVariables (some "R"), spec, ambient := 0, site := .left
    path := [], depth := 0, index := 0, initial := [], schemas := twoVariables
    rest := some "R", kind, targets }

def setRequest : Request := request .hashSet [a]
def bagRequest : Request := request .hashBag [a, a]

def controls : List (String × Bool) :=
  let initial := start setRequest
  let interrupted := resume setRequest 1 initial
  let finished := resume setRequest 100 initial
  let resumed := resume setRequest 99 interrupted
  let bagFinished := resume bagRequest 100 (start bagRequest)
  [ ("zero-budget-is-pending", !complete initial && (publication initial).isEmpty)
  , ("interrupted-search-is-pending", !complete interrupted && (publication interrupted).isEmpty)
  , ("resumption-preserves-entire-state", reprStr resumed == reprStr finished)
  , ("set-batch-finishes", complete finished)
  , ("set-batch-agrees-with-scoped-specification",
      (publication finished).map (·.matching.assignment) ==
        ScopedCollectionMatching.Controls.evaluate .hashSet twoVariables (some "R") [a])
  , ("retention-histories-survive-publication",
      (publication finished).map (·.allocation.decisions) ==
        [[⟨0, true⟩, ⟨0, false⟩], [⟨0, true⟩, ⟨0, true⟩]])
  , ("published-set-decisions-replay",
      (publication finished).all fun receipt =>
        replay true [a] receipt.allocation.decisions == some receipt.allocation.erase)
  , ("bag-batch-finishes", complete bagFinished)
  , ("equal-bag-answers-retain-distinct-origins",
      (publication bagFinished).map (·.allocation.decisions) ==
        [[⟨0, false⟩, ⟨0, false⟩], [⟨1, false⟩, ⟨0, false⟩]])
  , ("resume-complete-batch-is-stable",
      reprStr (resume setRequest 20 finished) == reprStr finished)
  , ("impossible-bag-allocation-is-complete",
      complete (start (request .hashBag [a])) &&
        (publication (start (request .hashBag [a]))).isEmpty) ]

def checkControls : IO Unit := do
  for (name, passed) in controls do
    if !passed then throw (IO.userError s!"Collection machine control failed: {name}")
  IO.println s!"ScopedCollectionMachineControls: {controls.length}/{controls.length}"

#eval checkControls

end Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine.Controls
