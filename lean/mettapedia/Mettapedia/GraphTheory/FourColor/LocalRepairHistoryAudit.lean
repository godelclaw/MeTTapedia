import Mettapedia.GraphTheory.FourColor.LocalRepairHistory
import Lean.Util.CollectAxioms

/-! # Audit of the separated-component reconstruction histories -/

open Lean Elab Command SimpleGraph

run_cmd do
  let env ← getEnv
  let roots := [``KempeSeparatedChains.Certificate.component_mem,
    ``KempeSeparatedChains.Certificate.after, ``KempeSeparatedChains.Certificate.history,
    ``KempeSeparatedChains.Certificate.commute, ``KempeSeparatedChains.Certificate.fixed_outside,
    ``LocalRepairHistory.history, ``LocalRepairHistory.history_length,
    ``LocalRepairHistory.reverseHistory, ``LocalRepairHistory.reverseHistory_length,
    ``LocalRepairHistory.orders_agree,
    ``LocalRepairHistory.reconstruction, ``LocalRepairHistory.both_orders_fixed,
    ``LocalRepairHistory.changes_near,
    ``LocalRepairHistory.radius_two_insufficient]
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
      if root == ``LocalRepairHistory.reconstruction then
        [``KempeSeparatedChains.Certificate.history, ``LocalRepairHistory.reconstructed_agrees]
      else if root == ``LocalRepairHistory.orders_agree then
        [``KempeSeparatedChains.Certificate.commute]
      else if root == ``LocalRepairHistory.both_orders_fixed then
        [``KempeSeparatedChains.Certificate.fixed_outside]
      else if root == ``LocalRepairHistory.radius_two_insufficient then
        [``LocalRepairRadius.no_local_extension]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Local repair histories: {roots.length} roots; {all.toList.length} declarations."
