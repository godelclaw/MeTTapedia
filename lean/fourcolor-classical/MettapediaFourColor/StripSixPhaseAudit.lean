import MettapediaFourColor.StripSixPhaseExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripSixPhaseChoice.normal_form,
      [``SimpleGraph.Coloring.changed_neighbour_of_pointwise_swap]),
    (``StripSixPhaseChoice.free_of_phase,
      [``StripSixPhaseChoice.normal_form, ``StripSixPhaseChoice.terminal_necessary,
       ``SimpleGraph.Coloring.component_changed_of_pointwise_swap]),
    (``StripSixPhaseChoice.single_repair,
      [``StripSixPhaseChoice.core_valid, ``StripSourceExtension.complete_valid]),
    (``StripSixPhaseChoice.compress_phase,
      [``SimpleGraph.KempePairHistory.pointwise, ``StripSixPhaseChoice.free_of_phase,
       ``StripSixPhaseChoice.single_repair]),
    (``StripSixPhaseChoice.phase_iff_free,
      [``StripSixPhaseChoice.free_of_phase, ``StripSixPhaseChoice.single_repair]),
    (``StripSixPhaseExample.planar, [``GraphTriangulationEuler.planar_iff_balance]),
    (``StripSixPhaseExample.minimum_degree, [``StripSixPhaseExample.degree_eq]),
    (``StripSixPhaseExample.original_joint,
      [``StripSixPhaseExample.first_checked, ``StripSixPhaseExample.joint_checked]),
    (``StripSixPhaseExample.no_protective_path,
      [``StripSixPhaseExample.post_checked, ``StripSixPhaseExample.face_data]),
    (``StripSixPhaseExample.failed_nonextension,
      [``StripSixPhaseChoice.terminal_necessary, ``StripResponseSummary.valid_of_colouring]),
    (``StripSixPhaseExample.free, [``StripSixPhaseExample.paired_checked]),
    (``StripSixPhaseExample.bad_preparation,
      [``StripSixPhaseExample.eight_eq, ``StripSixPhaseExample.hidden_eq]),
    (``StripSixPhaseExample.no_late_phase_repair,
      [``StripSixPhaseChoice.free_of_phase, ``StripSixPhaseExample.no_free_component,
       ``StripSixPhaseExample.locked_checked, ``SimpleGraph.KempePairHistory.pointwise]),
    (``StripSixPhaseExample.source,
      [``StripSixPhaseChoice.single_repair, ``StripSixPhaseExample.free,
       ``StripSixPhaseExample.eight_eq]),
    (``StripSixPhaseExample.reconstructed,
      [``StripSixPhaseExample.source, ``PatchBoundaryGluing.reconstruct,
       ``StripSixPhaseExample.core_stars])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`FourColor.StripSixBarrierRepair.repair_after,
    `FourColor.StripSixBarrierGeometry.ExteriorReading.repair_of_preserved_path,
    `FourColor.StripSixBarrierExample.source, `SimpleGraph.KempeNeighborRelease.second,
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
  logInfo m!"Exact fixed-pair criterion, obstruction and spherical reconstruction: {contracts.length} roots; \
    {all.toList.length} declarations."
