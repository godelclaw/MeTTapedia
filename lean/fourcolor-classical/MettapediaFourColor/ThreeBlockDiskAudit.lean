import MettapediaFourColor.ThreeBlockDiskBoundaryExample
import MettapediaFourColor.ThreeBlockDiskReconstruction
import Lean.Util.CollectAxioms

/-! # Audit of uniform core deletion and its reconstruction consumer -/

open Lean Elab Command
open FourColor

run_cmd do
  let env ← getEnv
  let roots := [``InducedGraphRotation.cyclic, ``InducedGraphRotation.next_of_arc,
    ``ThreeBlockDiskBoundary.patch, ``ThreeBlockDiskBoundary.core_stars,
    ``ThreeBlockDiskBoundary.boundary_arc, ``ThreeBlockDiskBoundary.boundary_step,
    ``ThreeBlockDiskBoundary.outside_boundary, ``ThreeBlockDiskBoundary.outside_distinct,
    ``ThreeBlockDiskBoundary.outside_order, ``ThreeBlockDiskBoundary.exterior_covers,
    ``ThreeBlockDiskBoundary.deleted_count, ``ThreeBlockDiskBoundary.repair,
    ``ThreeBlockDiskBoundary.Example.reading,
    ``ThreeBlockDiskBoundary.Example.deletion_boundary,
    ``ThreeBlockDiskBoundary.Example.deletion_cyclic]
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
        if root != ``ThreeBlockDiskBoundary.repair &&
            (`FourColor.ResidualSeedRepairCertificate).isPrefixOf name then
          throwError m!"Repair certificate in geometry root {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    let required :=
      if root == ``ThreeBlockDiskBoundary.repair then
        [``ThreeBlockDiskBoundary.core_stars, ``ThreeBlockDiskBoundary.outside_boundary,
         ``ThreeBlockDiskBoundary.outside_cyclic, ``ThreeBlockDiskBoundary.outside_order,
         ``ResidualSeedRepairCertificate.seed_repair, ``PlanarGraphBoundaryClosure.rotation_closed,
         ``ThreeBlockGeometry.ExteriorReading.reconstruct]
      else if root == ``ThreeBlockDiskBoundary.core_stars then
        [``ThreeBlockDiskBoundary.core_predecessor, ``ThreeBlockDiskBoundary.Reading.turn]
      else if root == ``ThreeBlockDiskBoundary.outside_boundary then
        [``ThreeBlockDiskBoundary.boundary_arc, ``ThreeBlockDiskBoundary.fan_chain,
         ``ThreeBlockDiskBoundary.face_turn, ``InducedGraphRotation.next_of_arc]
      else if root == ``ThreeBlockDiskBoundary.Example.deletion_boundary then
        [``ThreeBlockDiskBoundary.Example.core_turn, ``ThreeBlockDiskBoundary.Example.triangular,
         ``ThreeBlockDiskBoundary.outside_boundary]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Uniform core deletion: {roots.length} roots; {all.toList.length} declarations."
