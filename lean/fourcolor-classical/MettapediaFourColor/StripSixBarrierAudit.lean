import MettapediaFourColor.StripSixBarrierExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripSixBarrierGeometry.Patch.separated_faces,
      [``StripSixBarrierGeometry.Patch.face_labels]),
    (``StripSixBarrierGeometry.Patch.no_crossing_paths,
      [``StripSixBarrierGeometry.Patch.separated_faces,
       ``Mettapedia.GraphTheory.FourColor.PrimalPathSeparation.labels_eq_of_disjoint_walk]),
    (``StripSixBarrierRepair.eight_members, [``StripSixRelease.first_members]),
    (``StripSixBarrierRepair.footprint, [``SimpleGraph.Coloring.mem_kempeComponentSet_of_adj]),
    (``StripSixBarrierRepair.repair_after,
      [``StripSixBarrierRepair.footprint, ``StripSixBarrierRepair.core_valid,
       ``StripSourceExtension.complete_valid]),
    (``StripSixBarrierGeometry.ExteriorReading.protects_outer,
      [``StripSixBarrierGeometry.Patch.no_crossing_paths]),
    (``StripSixBarrierGeometry.ExteriorReading.repair_of_preserved_path,
      [``StripSixBarrierGeometry.ExteriorReading.protects_outer,
       ``SimpleGraph.Coloring.swapOnKempeComponent_apply_of_not_mem,
       ``StripSixBarrierRepair.repair_after]),
    (``StripSixBarrierExample.eight_members,
      [``StripSixBarrierRepair.eight_members, ``StripSixBarrierExample.eight_checked]),
    (``StripSixBarrierExample.source,
      [``StripSixBarrierExample.face_data, ``StripSixBarrierExample.connection_active,
       ``StripSixBarrierExample.connection_apart, ``StripSixBarrierExample.eight_members,
       ``StripSixBarrierGeometry.ExteriorReading.repair_of_preserved_path,
       ``GraphSphericalEuler.balance]),
    (``StripSixBarrierExample.reconstructed,
      [``StripSixBarrierExample.source, ``PatchBoundaryGluing.reconstruct,
       ``StripSixReleaseExample.core_stars])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`SimpleGraph.KempeNeighborRelease.second,
    `FourColor.StripSixRelease.repair, `FourColor.StripSixReleaseExample.source,
    `FourColor.StripSixReleaseExample.reconstructed, `sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
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
  logInfo m!"Preserved-path repair and spherical reconstruction: {contracts.length} roots; \
    {all.toList.length} declarations."
