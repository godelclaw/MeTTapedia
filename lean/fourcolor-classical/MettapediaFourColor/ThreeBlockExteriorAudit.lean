import MettapediaFourColor.ThreeBlockExteriorPlanarExample
import Lean.Util.CollectAxioms

/-! # Audit of the exterior geometry supplied by core deletion -/

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.Hypermap.Reference

run_cmd do
  let env ← getEnv
  let roots := [``InducedGraphRotation.phi_of_retained,
    ``GraphTriangulationEuler.planar_iff_balance,
    ``ThreeBlockDiskBoundary.core_face_boundary,
    ``ThreeBlockDiskBoundary.outside_triangular,
    ``ThreeBlockDiskBoundary.outside_connected,
    ``ThreeBlockDiskBoundary.coreDartMap_surjective,
    ``ThreeBlockDiskBoundary.deletion_dart_count,
    ``ThreeBlockDiskBoundary.outside_planar,
    ``ThreeBlockDiskBoundary.exterior_closed,
    ``ThreeBlockDiskBoundary.repair_of_ambient,
    ``ThreeBlockDiskBoundary.Example.planar,
    ``ThreeBlockDiskBoundary.Example.deleted_planar,
    ``ThreeBlockDiskBoundary.Example.deleted_vertices,
    ``ThreeBlockDiskBoundary.Example.deleted_darts,
    ``ThreeBlockDiskBoundary.Example.closed]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData]
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
        if root != ``ThreeBlockDiskBoundary.repair_of_ambient &&
            (`FourColor.ResidualSeedRepairCertificate).isPrefixOf name then
          throwError m!"Repair certificate in geometry root {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    let required :=
      if root == ``ThreeBlockDiskBoundary.outside_planar then
        [``PatchDisk.Reading.outside_connected,
         ``PatchDisk.Reading.outside_triangular,
         ``PatchDisk.Reading.deletion_dart_count,
         ``GraphTriangulationEuler.balance, ``GraphDiskEuler.planar,
         ``Hypermap.cubic_Euler, ``Hypermap.quasicubic_Euler]
      else if root == ``ThreeBlockDiskBoundary.repair_of_ambient then
        [``ThreeBlockDiskBoundary.outside_planar,
         ``ThreeBlockDiskBoundary.outside_triangular,
         ``ResidualSeedRepairCertificate.seed_repair,
         ``PlanarGraphBoundaryClosure.rotation_closed,
         ``ThreeBlockGeometry.ExteriorReading.reconstruct]
      else if root == ``ThreeBlockDiskBoundary.outside_triangular then
        [``ThreeBlockDiskBoundary.core_stars,
         ``ThreeBlockDiskBoundary.core_face_boundary,
         ``InducedGraphRotation.phi_of_retained]
      else if root == ``ThreeBlockDiskBoundary.deletion_dart_count then
        [``ThreeBlockDiskBoundary.coreDartMap_surjective,
         ``ThreeBlockDiskBoundary.core_dart_count]
      else if root == ``ThreeBlockDiskBoundary.Example.deleted_planar then
        [``ThreeBlockDiskBoundary.Example.planar,
         ``ThreeBlockDiskBoundary.Example.reading,
         ``ThreeBlockDiskBoundary.outside_planar]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Uniform exterior geometry: {roots.length} roots; {all.toList.length} declarations."
