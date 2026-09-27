import FourColor.Pilot.Cfg000
import FourColor.Pilot.Cfg003
import FourColor.Pilot.Cfg008
import FourColor.Pilot.Cfg019
import FourColor.Pilot.Cfg109
import FourColor.Bulk.Cfg.Hyb033
import FourColor.PilotAudit

#print axioms FourColor.Bulk.Cfg000.reducible
#print axioms FourColor.Bulk.Cfg003.reducible
#print axioms FourColor.Bulk.Cfg008.reducible
#print axioms FourColor.Bulk.Cfg019.reducible
#print axioms FourColor.Bulk.Cfg109.reducible
#print axioms FourColor.Bulk.Hyb033.reducible

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
