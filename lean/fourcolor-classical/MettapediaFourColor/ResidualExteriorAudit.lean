import MettapediaFourColor.ResidualExteriorRepair
import Lean.Util.CollectAxioms

/-! # Audit of the exact exterior disk and its ambient colouring consumer -/

open Lean Elab Command
open FourColor

run_cmd do
  let env ← getEnv
  let roots := [``GraphRotationRows.Rows.cyclic, ``GraphRotationRows.Rows.dart_count,
    ``GraphDiskEuler.planar, ``ResidualExteriorDisk.planar, ``ResidualExteriorDisk.closed,
    ``ResidualExteriorPatch.reconstruct, ``ResidualSeedRepairCertificate.seed_not_direct,
    ``ResidualExteriorRepair.initial_cannot_extend,
    ``ResidualExteriorRepair.compatible, ``ResidualExteriorRepair.reconstructed]
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
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    let required :=
      if root == ``ResidualExteriorRepair.reconstructed then
        [``ResidualSeedRepairCertificate.seed_repair, ``ResidualExteriorDisk.closed,
         ``GraphTraceAlignment.align, ``PatchBoundaryGluing.reconstruct,
         ``ResidualExteriorPatch.full_check, ``ResidualExteriorPatch.complement_check]
      else if root == ``ResidualExteriorDisk.closed then
        [``Hypermap.Kempe_map, ``ResidualExteriorDisk.planar,
         ``ResidualExteriorDisk.boundary, ``ResidualExteriorDisk.triangles]
      else if root == ``ResidualExteriorDisk.planar then
        [``GraphDiskEuler.planar, ``Hypermap.quasicubic_Euler,
         ``ResidualExteriorDisk.row_nodup, ``ResidualExteriorDisk.forward_check,
         ``ResidualExteriorDisk.reverse_check, ``ResidualExteriorDisk.tour_chain,
         ``ResidualExteriorDisk.tour_covers]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Actual exterior repair: {roots.length} roots; {all.toList.length} declarations."
