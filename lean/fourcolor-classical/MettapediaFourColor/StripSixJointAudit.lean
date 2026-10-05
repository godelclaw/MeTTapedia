import MettapediaFourColor.StripSixJointReconstruction
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempeRetainedMatching.two_anchor_coclosure, [``KempeChromogramMatching.recover_stable,
      ``KempeRetainedMatching.possible_of_mate]),
    (``StripSixJointRepair.select, [``KempeIntervalMatching.possible]),
    (``StripSixJointRepair.one_ready, [``StripSymbolicRepair.Direct]),
    (``StripSixJointRepair.two_ready, [``StripSymbolicRepair.Direct]),
    (``StripSixJointRepair.stages, [``KempeRetainedMatching.two_anchor_coclosure,
      ``StripSymbolicRepair.direct_coclosure]),
    (``StripSixJointRepair.repair,
      [``StripSixJointRepair.stages, ``StripSixJointRepair.source_trace]),
    (``StripSixJointRepair.nonextension, [``StripSixJointRepair.no_direct,
      ``StripResponseSummary.no_trace]),
    (``StripSixJointRepair.compatible_changed, [``StripSixJointRepair.repair,
      ``StripSixJointRepair.nonextension, ``GraphTraceAlignment.align,
      ``StripSourceExtension.complete_valid]),
    (``StripSixJointRepair.classified_repair, [``StripSixConnection.classified,
      ``StripSixJointRepair.compatible_changed]),
    (``StripSixJointRepair.disk_compatible, [``PlanarGraphBoundaryClosure.rotation_closed,
      ``StripSixJointRepair.compatible_changed]),
    (``StripSixJointRepair.whole_repair, [``PatchBoundaryGluing.reconstruct,
      ``StripSixJointRepair.compatible_changed, ``Fintype.card_lt_of_injective_of_notMem]),
    (``StripSixJointRepair.disk_whole_repair, [``StripSixJointRepair.whole_repair,
      ``PlanarGraphBoundaryClosure.rotation_closed])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairData,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.StripSpherePhase.whole_repair, `FourColor.StripPhaseObstruction.repairHistory]
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
  logInfo m!"Joint port-six repair: {contracts.length} roots; {all.toList.length} declarations."
