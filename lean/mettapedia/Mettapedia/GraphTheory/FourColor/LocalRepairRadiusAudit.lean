import Mettapedia.GraphTheory.FourColor.LocalRepairRadius
import Lean.Util.CollectAxioms

/-! # Audit of the endpoint obstruction to radius-two repair -/

open Lean Elab Command SimpleGraph

run_cmd do
  let env ← getEnv
  let roots := [``LocalRepairRadius.exteriorColouring, ``LocalRepairRadius.repaired,
    ``LocalRepairRadius.repaired_fixed, ``LocalRepairRadius.no_local_extension,
    ``LocalRepairRadius.outside_far, ``LocalRepairRadius.reconstruction_changes_far,
    ``LocalRepairRadius.transport, ``LocalRepairRadius.repaired_changes_near]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut all : NameSet := {}
  for root in roots do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if forbidden.any (·.isPrefixOf name) then
          throwError m!"Forbidden dependency in {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    let required :=
      if root == ``LocalRepairRadius.reconstruction_changes_far then
        [``LocalRepairRadius.no_local_extension, ``LocalRepairRadius.outside_far]
      else if root == ``LocalRepairRadius.transport then
        [``LocalRepairRadius.no_local_extension]
      else if root == ``LocalRepairRadius.repaired_changes_near then
        [``LocalRepairRadius.repaired_fixed]
      else if root == ``LocalRepairRadius.repaired_fixed then
        [``LocalRepairRadius.repaired]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Local repair radius: {roots.length} roots; {all.toList.length} declarations."
