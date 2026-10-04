import MettapediaFourColor.StripConnectionExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripConnectionGeometry.Patch.separated_faces,
      [``StripConnectionGeometry.Patch.face_labels]),
    (``StripConnectionGeometry.Patch.no_crossing_paths,
      [``StripConnectionGeometry.Patch.separated_faces,
       ``Mettapedia.GraphTheory.FourColor.PrimalPathSeparation.labels_eq_of_disjoint_walk]),
    (``StripConnectionRepair.core_valid,
      [``StripConnectionRepair.core_edges, ``StripConnectionRepair.core_lists]),
    (``StripConnectionRepair.repair_of_isolated_port,
      [``StripConnectionRepair.core_valid, ``StripSourceExtension.complete_valid]),
    (``StripConnectionGeometry.ExteriorReading.excludes_middle,
      [``StripConnectionGeometry.Patch.no_crossing_paths]),
    (``StripConnectionGeometry.ExteriorReading.repair_of_path,
      [``StripConnectionGeometry.ExteriorReading.excludes_middle,
       ``StripConnectionRepair.repair_of_isolated_port]),
    (``StripConnectionGeometry.ExteriorReading.repair_of_component,
      [``StripConnectionGeometry.ExteriorReading.repair_of_path]),
    (``GraphSphericalEuler.balance, [``GraphDiskEuler.node_count]),
    (``StripConnectionExample.planar, [``GraphTriangulationEuler.planar_iff_balance]),
    (``StripConnectionExample.minimum_degree, [``StripConnectionExample.degree_eq]),
    (``StripConnectionExample.source,
      [``StripConnectionGeometry.ExteriorReading.repair_of_path,
       ``GraphSphericalEuler.balance, ``StripConnectionExample.face_data]),
    (``StripConnectionExample.reconstructed,
      [``StripConnectionExample.source, ``PatchBoundaryGluing.reconstruct,
       ``StripConnectionExample.core_stars])]
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
  logInfo m!"Geometric connection repair and spherical reconstruction: {contracts.length} roots; \
    {all.toList.length} declarations."
