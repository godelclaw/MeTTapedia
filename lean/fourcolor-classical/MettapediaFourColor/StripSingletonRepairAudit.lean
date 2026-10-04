import MettapediaFourColor.StripSingletonRim
import MettapediaFourColor.StripSingletonExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempeSingletonRelease.singleton_closed, [``KempeComponentDetach.closed_after_swap]),
    (``KempeSingletonRelease.history, [``KempeSingletonRelease.singleton_closed,
      ``KempeSeparatedChains.Certificate.step]),
    (``KempeSingletonRelease.fixed_outside, [``KempeSingletonRelease.endpoint]),
    (``StripSingletonRepair.after_lists, [``KempeSingletonRelease.endpoint,
      ``StripSingletonRepair.forced, ``StripSingletonRepair.list_step]),
    (``StripSingletonRepair.source, [``StripSingletonRepair.core_valid,
      ``StripSourceExtension.complete_valid]),
    (``StripSingletonRepair.repair, [``KempeSingletonRelease.history,
      ``StripSingletonRepair.source]),
    (``StripSingletonRepair.repair_or_connection, [``StripSingletonRepair.repair]),
    (``StripSingletonRepair.connection_walk, [``SimpleGraph.ConnectedComponent.exact]),
    (``StripSingletonRim.confined, [``StripSingletonRim.barriers,
      ``SimpleGraph.Coloring.kempeComponentSet_subset_of_closed]),
    (``StripSingletonRim.repair, [``StripSingletonRepair.repair, ``StripSingletonRim.confined]),
    (``StripSingletonExample.source, [``StripSingletonRepair.source]),
    (``StripSingletonExample.assemble, [``PatchBoundaryGluing.reconstruct,
      ``StripStrongAnchorTrap.core_stars]),
    (``StripSingletonExample.reconstructed, [``StripSingletonRepair.source,
      ``StripSingletonExample.assemble, ``KempeSingletonRelease.singleton_closed]),
    (``StripSingletonExample.repaired_values, [``KempeSingletonRelease.endpoint])]
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
  logInfo m!"Uniform singleton release and source reconstruction: {contracts.length} roots; \
    {all.toList.length} declarations."
