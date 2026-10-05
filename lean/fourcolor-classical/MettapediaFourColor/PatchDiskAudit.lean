import MettapediaFourColor.PatchDiskFoldedExample
import MettapediaFourColor.ThreeBlockExteriorPlanar
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``PatchDiskSources.d0092, [``FiveTriangleCollapseObstruction.upper]),
    (``PatchDiskSources.d0099, [``TriangleStripAnchors.input0099]),
    (``PatchDisk.neighbours_injective, [``CyclicCoreStars.covers]),
    (``PatchDisk.Reading.boundary_arc, [``PatchDisk.Source.fan_chain,
      ``PatchDisk.Reading.corner]),
    (``PatchDisk.Reading.boundaryDart_injective, [``PatchDisk.Reading.core_injective,
      ``PatchDisk.Reading.local_injective, ``ExceptionalCoreOrientation.Corner.rotate]),
    (``PatchDisk.Reading.outside_triangular, [``PatchDisk.Source.core_boundary_turn,
      ``PatchDisk.Reading.core_stars, ``InducedGraphRotation.phi_of_retained]),
    (``PatchDisk.Reading.deletion_dart_count, [``PatchDisk.Reading.coreDartMap_injective,
      ``PatchDisk.Reading.coreDartMap_surjective, ``PatchDisk.Source.core_dart_count]),
    (``PatchDisk.Reading.deletion_vertex_count, [``PatchDisk.Reading.core_eq]),
    (``PatchDisk.Reading.outside_planar, [``GraphTriangulationEuler.balance,
      ``GraphDiskEuler.planar, ``PatchDisk.Reading.outside_connected,
      ``PatchDisk.Reading.outside_triangular, ``PatchDisk.Reading.deletion_dart_count,
      ``PatchDisk.Reading.deletion_vertex_count, ``PatchDisk.Reading.boundaryDart_injective]),
    (``PatchDisk.Reading.exterior_closed, [``PlanarGraphBoundaryClosure.rotation_closed,
      ``PatchDisk.Reading.outside_planar]),
    (``ThreeBlockDiskBoundary.outside_planar, [``PatchDisk.Reading.outside_planar,
      ``PatchDiskSources.of_d0092]),
    (``PatchDiskRepair.d0099_repair, [``PatchDisk.Reading.exterior_closed,
      ``StripSixJointRepair.whole_repair_of_core_injective, ``PatchBoundaryGluing.reconstruct]),
    (``PatchDiskFoldedExample.reading, [``PatchDiskSources.of_d0099,
      ``PatchDiskFoldedExample.core_turn, ``PatchDiskFoldedExample.degrees]),
    (``PatchDiskFoldedExample.not_injective, [``PatchDiskFoldedExample.identified]),
    (``PatchDiskFoldedExample.deleted_planar, [``PatchDisk.Reading.outside_planar,
      ``PatchDiskFoldedExample.planar]),
    (``PatchDiskFoldedExample.closed, [``PatchDisk.Reading.exterior_closed])]
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
  logInfo m!"Common patch deletion: {contracts.length} roots; \
    {all.toList.length} declarations."
