import MettapediaFourColor.StripSixRim
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripSixConnection.core_valid,
      [``StripSixConnection.core_edges, ``StripSixConnection.core_lists]),
    (``StripSixConnection.direct,
      [``StripSixConnection.core_valid, ``StripSixConnection.mask_exact,
       ``StripSourceExtension.complete_valid]),
    (``StripSixConnection.classified, [``StripSixConnection.local_form]),
    (``StripSixConnection.repair_or_joint, [``StripSixConnection.direct]),
    (``StripSixConnection.of_port_six,
      [``StripSixConnection.classified, ``StripSixConnection.repair_or_joint]),
    (``StripSixConnection.joint_walks, [``SimpleGraph.ConnectedComponent.exact]),
    (``StripSixRim.repair,
      [``StripSixConnection.direct, ``StripSixRim.barriers, ``StripSixRim.proper])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.StripStrongAnchorTrap.proper, `FourColor.StripStrongAnchorTrap.repair_checked,
    `FourColor.StripStrongAnchorTrap.repairCertificate, `FourColor.StripStrongAnchorTrap.repair_eq,
    `FourColor.StripStrongAnchorTrap.repairStep, `FourColor.StripStrongAnchorTrap.repairHistory,
    `FourColor.StripStrongAnchorTrap.whole_valid, `FourColor.StripStrongAnchorTrap.final_valid,
    `FourColor.StripStrongAnchorTrap.finalColouring, `FourColor.StripStrongAnchorTrap.reconstructed]
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
  logInfo m!"Port-six repair or joint connection: {contracts.length} roots; \
    {all.toList.length} declarations."
