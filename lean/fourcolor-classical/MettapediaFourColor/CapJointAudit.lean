import MettapediaFourColor.CapJointTransport
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``CapJointTransport.triangle_switch, [``CapJointTransport.flip]),
    (``CapJointTransport.switched_good, [``CapJointTransport.triangle_switch,
      ``CapJointTransport.Respects]),
    (``CapJointTransport.observe_good, [``CapJointTransport.graph, ``CapJointTransport.observe]),
    (``CapJointTransport.reconstruct, [``BoundaryFanRepair.extend, ``BoundaryFourFanRepair.extend]),
    (``CapJointTransport.lift_selection, [``CapJointTransport.switched_good,
      ``CapJointTransport.reconstruct]),
    (``CapJointTransport.lift_chromogram, [``CapJointTransport.lift_selection,
      ``KempeBoundarySplit.GraphTrace]),
    (``CapJointTransport.source_consumer, [``CapJointTransport.lift_selection,
      ``StripFanProgram.graph2])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.ResidualSeedRepairData, `FourColor.DiamondProfileData]
  let mut all : NameSet := {}
  for (root, required) in contracts do
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
    for name in required do
      unless seen.contains name do
        throwError m!"Missing semantic dependency in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Retained cap reconstruction: {contracts.length} roots; \
    {all.toList.length} declarations."
