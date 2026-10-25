import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceRootComparison
import Mettapedia.GSLT.LanguageDef.CollectionConsumerControls

/-! # Authored root consumers through both certified source search strategies -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionOccurrenceRootComparisonControls

open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags
open CollectionConsumers CollectionConsumers.Controls.RootControls

def compare (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionRootSearch.CoverageProfile plan) (expected : TypeExpr)
    (source : Pattern) (hasSuccessor : Bool) : IO Unit := do
  let oldSearch := CollectionRootSearch.search (profile := certificate.profile) expected
  let newSearch := CollectionOccurrenceSearch.search plan [] expected 0
  let oldRun := oldSearch.run (canon source) 1000
  let newRun := newSearch.run source 1000
  unless decide (oldSearch.status oldRun = .complete) &&
      decide (newSearch.status newRun = .complete) do
    throw (IO.userError "Root comparison used an unfinished one-step search")
  let oldTargets := ((oldSearch.publication oldRun).map fun receipt => canon receipt.target).eraseDups
  let newTargets := ((newSearch.publication newRun).map fun receipt => canon receipt.target).eraseDups
  unless decide (oldTargets.Perm newTargets) do
    throw (IO.userError "Root and occurrence search disagree on canonical successors")
  unless !newTargets.isEmpty == hasSuccessor do
    throw (IO.userError s!"Root comparison expected successor={hasSuccessor} at {reprStr source}")

def checkControls : IO Unit := do
  compare petriPlan petriCoverage (.base "Marking")
    (marking [token "A", token "A", token "B"]) true
  compare petriPlan petriCoverage (.base "Marking") (marking [token "A"]) false
  compare reachabilityPlan graphCoverage (.base "Graph")
    (graph [edge "A" "B", edge "B" "C"]) true
  compare reachabilityPlan graphCoverage (.base "Graph") (graph [edge "A" "B"]) false

#eval checkControls

end Mettapedia.GSLT.LanguageDef.CollectionOccurrenceRootComparisonControls
