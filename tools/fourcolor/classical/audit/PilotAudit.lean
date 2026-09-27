import FourColor.Main
import FourColor.RealPlaneMathlib
import FourColor.Bulk.Reducible
import FourColor.Bulk.HybridT

#check FourColor.fourColorTheorem_of_checks
#print axioms FourColor.fourColorTheorem_of_checks
#check FourColor.Bulk.cfReducible_of_bulkChecks
#print axioms FourColor.Bulk.cfReducible_of_bulkChecks
#check FourColor.Bulk.cfReducible_of_hybridT
#print axioms FourColor.Bulk.cfReducible_of_hybridT
#print FourColor.FourColorTheorem
#check FourColor.simpleMap_iff
#print axioms FourColor.simpleMap_iff

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`FourColor).isPrefixOf name && !name.isInternal then
      count := count + 1
      for axiomName in (← liftCoreM <| collectAxioms name) do
        unless allowed.contains axiomName do
          throwError m!"Unexpected axiom in {name}: {axiomName}"
  logInfo m!"Audited {count} imported FourColor declarations; only the three permitted axioms."
