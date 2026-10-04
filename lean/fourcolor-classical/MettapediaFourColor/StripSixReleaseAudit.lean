import MettapediaFourColor.StripSixReleaseExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempeNeighborRelease.singleton_closed, [``KempeComponentDetach.closed_after_swap]),
    (``KempeNeighborRelease.endpoint, [``KempeNeighborRelease.outside]),
    (``StripSixRelease.first_members, [``StripSingletonRepair.forced]),
    (``StripSixRelease.repair,
      [``KempeNeighborRelease.history, ``KempeNeighborRelease.endpoint,
       ``StripSixRelease.core_valid, ``StripSixRelease.first_values,
       ``StripSourceExtension.complete_valid]),
    (``StripSixReleaseExample.planar, [``GraphTriangulationEuler.planar_iff_balance]),
    (``StripSixReleaseExample.minimum_degree, [``StripSixReleaseExample.degree_eq]),
    (``StripSixReleaseExample.core_stars, []),
    (``StripSixReleaseExample.joint_case, [``StripSixReleaseExample.joint_checked]),
    (``StripSixReleaseExample.failedHistory,
      [``StripSixReleaseExample.first_eq, ``StripSixReleaseExample.failed_eq]),
    (``StripSixReleaseExample.failed_nonextension,
      [``StripSixReleaseExample.empty_terminal, ``StripResponseSummary.terminal_iff]),
    (``StripSixReleaseExample.source, [``StripSixRelease.repair,
       ``StripSixReleaseExample.exits, ``StripSixReleaseExample.no_entry]),
    (``StripSixReleaseExample.reconstructed, [``StripSixReleaseExample.source,
       ``PatchBoundaryGluing.reconstruct, ``StripSixReleaseExample.core_stars])]
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
  logInfo m!"Neighbour release and spherical continuation: {contracts.length} roots; \
    {all.toList.length} declarations."
