import FourColor.Complete
import Lean.Util.FoldConsts

/-! Independent axiom audit of the pinned, uncompressed reference theorem. -/

#check @FourColor.fourColorTheorem
#print FourColor.FourColorTheorem
#print axioms FourColor.fourColorTheorem
#print axioms FourColor.reducibility

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
  logInfo m!"Reference baseline: audited {count} imported public FourColor declarations."
