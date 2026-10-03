import MettapediaFourColor.ThreeBlockFamilyExample
import Lean.Util.CollectAxioms

/-! # Audit of shared three-run repairs and actual reconstruction -/

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let roots := [``KempeRepairComposition.flatten, ``KempeRepairComposition.sound,
    ``ThreeBlockRepairTransfer.leafCheck_sound, ``ThreeBlockRepairTransfer.checked,
    ``ThreeBlockRepairTransfer.repair, ``ThreeBlockRepairTransfer.direct,
    ``ThreeBlockRepairTransfer.root_word, ``ThreeBlockRepairTransfer.three_run_repair,
    ``ThreeBlockDiskBoundary.repair_of_boundary_trace,
    ``ThreeBlockDiskBoundary.repair_three_run,
    ``ThreeBlockDiskBoundary.FamilyExample.reading,
    ``ThreeBlockDiskBoundary.FamilyExample.planar,
    ``ThreeBlockDiskBoundary.FamilyExample.initial_cannot_extend,
    ``ThreeBlockDiskBoundary.FamilyExample.changed_reconstruction,
    ``ThreeBlockDiskBoundary.FamilyExample.exterior_vertices]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData]
  let geometry := [``ThreeBlockDiskBoundary.FamilyExample.reading,
    ``ThreeBlockDiskBoundary.FamilyExample.planar,
    ``ThreeBlockDiskBoundary.FamilyExample.initial_cannot_extend,
    ``ThreeBlockDiskBoundary.FamilyExample.exterior_vertices]
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
        if geometry.contains root &&
            ([`FourColor.ResidualSeedRepairCertificate, `FourColor.ThreeBlockRepairTransfer,
              `FourColor.ThreeBlockRepairTransferData].any (·.isPrefixOf name)) then
          throwError m!"Repair data in independent geometry or obstruction root {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    let required :=
      if root == ``ThreeBlockRepairTransfer.repair then
        [``KempeRepairComposition.sound, ``ResidualSeedRepairCertificate.checked,
         ``ResidualSeedRepairCertificate.coclosure, ``KempeMaskCertificate.check_sound,
         ``ResidualSeedRepairCertificate.source_edges]
      else if root == ``ThreeBlockRepairTransfer.three_run_repair then
        [``ThreeBlockRepairTransfer.repair, ``ResidualSeedRepairCertificate.seed_repair,
         ``ThreeBlockCore.colouring]
      else if root == ``ThreeBlockDiskBoundary.repair_three_run then
        [``ThreeBlockDiskBoundary.exterior_closed, ``ThreeBlockDiskBoundary.outside_planar,
         ``ThreeBlockRepairTransfer.three_run_repair, ``GraphTraceAlignment.align,
         ``ThreeBlockGeometry.ExteriorReading.reconstruct]
      else if root == ``ThreeBlockDiskBoundary.FamilyExample.changed_reconstruction then
        [``ThreeBlockDiskBoundary.FamilyExample.initial,
         ``ThreeBlockDiskBoundary.FamilyExample.boundary_proper,
         ``ThreeBlockDiskBoundary.FamilyExample.initial_cannot_extend,
         ``ThreeBlockDiskBoundary.FamilyExample.reading,
         ``ThreeBlockDiskBoundary.FamilyExample.planar,
         ``ThreeBlockDiskBoundary.repair_three_run]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Three-run family reconstruction: {roots.length} roots; {all.toList.length} declarations."
